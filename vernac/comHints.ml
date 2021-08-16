(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open Names

(** (Partial) implementation of the [Hint] command; some more
   functionality still lives in tactics/hints.ml *)

let project_hint ~poly pri l2r r =
  let open EConstr in
  let open Coqlib in
  let gr = Smartlocate.global_with_alias r in
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let sigma, c = Evd.fresh_global env sigma gr in
  let t = Retyping.get_type_of env sigma c in
  let t =
    Tacred.reduce_to_quantified_ref env sigma (lib_ref "core.iff.type") t
  in
  let sign, ccl = decompose_prod_assum sigma t in
  let a, b =
    match snd (decompose_app sigma ccl) with
    | [a; b] -> (a, b)
    | _ -> assert false
  in
  let p = if l2r then lib_ref "core.iff.proj1" else lib_ref "core.iff.proj2" in
  let sigma, p = Evd.fresh_global env sigma p in
  let c =
    Reductionops.whd_beta env sigma
      (mkApp (c, Context.Rel.instance mkRel 0 sign))
  in
  let c =
    it_mkLambda_or_LetIn
      (mkApp
         ( p
         , [| mkArrow a Sorts.Relevant (Vars.lift 1 b)
            ; mkArrow b Sorts.Relevant (Vars.lift 1 a)
            ; c |] ))
      sign
  in
  let name =
    Nameops.add_suffix
      (Nametab.basename_of_global gr)
      ("_proj_" ^ if l2r then "l2r" else "r2l")
  in
  let ctx = Evd.univ_entry ~poly sigma in
  let c = EConstr.to_constr sigma c in
  let cb =
    Declare.(DefinitionEntry (definition_entry ~univs:ctx ~opaque:false c))
  in
  let c =
    Declare.declare_constant ~local:Locality.ImportDefaultBehavior ~name
      ~kind:Decls.(IsDefinition Definition)
      cb
  in
  let info = {Typeclasses.hint_priority = pri; hint_pattern = None} in
  (info, true, Hints.PathAny, Hints.hint_globref (GlobRef.ConstRef c))

let warn_deprecated_hint_constr =
  CWarnings.create ~name:"fragile-hint-constr" ~category:"automation"
    (fun () ->
      Pp.strbrk
        "Declaring arbitrary terms as hints is fragile; it is recommended to \
         declare a toplevel constant instead")

(* Only error when we have to (axioms may be instantiated if from functors)
   XXX maybe error if not from a functor argument?
 *)
let soft_evaluable =
  let open GlobRef in
  let open Tacred in
  function
  | ConstRef c -> EvalConstRef c
  | VarRef id -> EvalVarRef id
  | (IndRef _ | ConstructRef _) as r -> Tacred.error_not_evaluable r

let interp_hints ~poly h =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let fref r =
    let gr = Smartlocate.global_with_alias r in
    Dumpglob.add_glob ?loc:r.CAst.loc gr;
    gr
  in
  let fr r = soft_evaluable (fref r) in
  let fi c =
    let open Hints in
    let open Vernacexpr in
    match c with
    | HintsReference c ->
      let gr = Smartlocate.global_with_alias c in
      (PathHints [gr], hint_globref gr)
    | HintsConstr c ->
      let () = warn_deprecated_hint_constr () in
      let env = Global.env () in
      let sigma = Evd.from_env env in
      let c, uctx = Constrintern.interp_constr env sigma c in
      let uctx = UState.normalize_variables uctx in
      let c = Evarutil.nf_evar (Evd.from_ctx uctx) c in
      let diff = UState.context_set uctx in
      let c =
        if poly then (c, Some diff)
        else
          let () = DeclareUctx.declare_universe_context ~poly:false diff in
          (c, None)
      in
      (PathAny, Hints.hint_constr c) [@ocaml.warning "-3"]
  in
  let fp = Constrintern.intern_constr_pattern env sigma in
  let fres (info, b, r) =
    let path, gr = fi r in
    let info =
      { info with
        Typeclasses.hint_pattern = Option.map fp info.Typeclasses.hint_pattern
      }
    in
    (info, b, path, gr)
  in
  let open Hints in
  let open Vernacexpr in
  let ft = function
    | HintsVariables -> HintsVariables
    | HintsConstants -> HintsConstants
    | HintsReferences lhints -> HintsReferences (List.map fr lhints)
  in
  let fp = Constrintern.intern_constr_pattern (Global.env ()) in
  match h with
  | HintsResolve lhints -> HintsResolveEntry (List.map fres lhints)
  | HintsResolveIFF (l2r, lc, n) ->
    HintsResolveEntry (List.map (project_hint ~poly n l2r) lc)
  | HintsImmediate lhints -> HintsImmediateEntry (List.map fi lhints)
  | HintsUnfold lhints -> HintsUnfoldEntry (List.map fr lhints)
  | HintsTransparency (t, b) -> HintsTransparencyEntry (ft t, b)
  | HintsMode (r, l) -> HintsModeEntry (fref r, l)
  | HintsConstructors lqid ->
    let constr_hints_of_ind qid =
      let ind = Smartlocate.global_inductive_with_alias qid in
      Dumpglob.dump_reference ?loc:qid.CAst.loc "<>"
        (Libnames.string_of_qualid qid)
        "ind";
      List.init (Inductiveops.nconstructors env ind) (fun i ->
          let c = (ind, i + 1) in
          let gr = GlobRef.ConstructRef c in
          ( empty_hint_info
          , true
          , PathHints [gr]
          , hint_globref gr ))
    in
    HintsResolveEntry (List.flatten (List.map constr_hints_of_ind lqid))
  | HintsExtern (pri, patcom, tacexp) ->
    let pat = Option.map (fp sigma) patcom in
    let l = match pat with None -> [] | Some (l, _) -> l in
    let ltacvars =
      List.fold_left (fun accu x -> Id.Set.add x accu) Id.Set.empty l
    in
    let env = Genintern.{(empty_glob_sign env) with ltacvars} in
    let _, tacexp = Genintern.generic_intern env tacexp in
    HintsExternEntry
      ({Typeclasses.hint_priority = Some pri; hint_pattern = pat}, tacexp)
