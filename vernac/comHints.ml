(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
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
  let open Rocqlib in
  let gr = Smartlocate.global_with_alias r in
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let sigma, c = Evd.fresh_global env sigma gr in
  let t = Retyping.get_type_of env sigma c in
  let t =
    Tacred.reduce_to_quantified_ref env sigma (lib_ref "core.iff.type") t
  in
  let sign, ccl = decompose_prod_decls sigma t in
  let a, b =
    match snd (decompose_app sigma ccl) with
    | [|a; b|] -> (a, b)
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
         , [| mkArrow a ERelevance.relevant (Vars.lift 1 b)
            ; mkArrow b ERelevance.relevant (Vars.lift 1 a)
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
  (info, true, Hints.hint_globref (GlobRef.ConstRef c))

let warning_deprecated_hint_constr =
  CWarnings.create_warning ~from:[CWarnings.CoreCategories.automation; Deprecation.Version.v8_20] ~name:"fragile-hint-constr" ~default:AsError ()

let warn_deprecated_hint_constr =
  CWarnings.create_in warning_deprecated_hint_constr
    (fun () ->
      Pp.strbrk
        "Declaring arbitrary terms as hints is fragile and deprecated; it is \
         recommended to declare a toplevel constant instead")

(* Only error when we have to (axioms may be instantiated if from functors)
   XXX maybe error if not from a functor argument?
 *)
let soft_evaluable = Tacred.soft_evaluable_of_global_reference

(* Slightly more lenient global hint syntax for backwards compatibility *)
let rectify_hint_constr h = match h with
| Vernacexpr.HintsReference _ -> h
| Vernacexpr.HintsConstr c ->
  let open Constrexpr in
  match c.CAst.v with
  | CAppExpl ((qid, None), []) -> Vernacexpr.HintsReference qid
  | _ -> Vernacexpr.HintsConstr c

(* Hint Extern names *)

open Libnames

module FullPath =
struct
  type t = full_path
  let equal = eq_full_path
  let to_string = string_of_path
  let repr sp =
    let dir,id = repr_path sp in
    id, (DirPath.repr dir)
end

module KnTab = Nametab.Make(FullPath)(KerName)

type nametab = {
  tab_cstr : KnTab.t;
}

let empty_nametab = {
  tab_cstr = KnTab.empty;
}

let nametab = Summary.ref empty_nametab ~name:"hintextern-nametab"

[@@@ocaml.warning "-32"]
let push_extern vis sp kn =
  let tab = !nametab in
  let tab_cstr = KnTab.push vis sp kn tab.tab_cstr in
  nametab := { tab_cstr }

let locate_extern qid =
  let tab = !nametab in
  KnTab.locate qid tab.tab_cstr

type hint_extern_name_obj = { dummy : string }  (* todo: needed?? *)

let cache_hintextern_name o = ()
let load_hintextern_name i ((sp,kn), n) = Printf.eprintf "load_hintextern_name\n%!"; ()
let open_hintextern_name i ((sp,kn), n) = Printf.eprintf "open_hintextern_name\n%!"; ()
let subst_hintextern_name = Libobject.ident_subst_function
let classify_hintextern_name obj = Libobject.Substitute
let discharge_hintextern_name obj = Some obj

let (objConstant2 : (Id.t * hint_extern_name_obj) Libobject.Dyn.tag) =
  let open Libobject in
  declare_named_object_full
    {(default_object "hintextern-name") with
     cache_function = cache_hintextern_name;
     load_function = load_hintextern_name;  (* Until *)
     open_function = simple_open ~cat:Hints.hint_cat open_hintextern_name;  (* Exactly *)
     subst_function = subst_hintextern_name;
     classify_function = classify_hintextern_name;
     discharge_function = discharge_hintextern_name;
    }

let inExternName v = Printf.eprintf "inExternName\n%!"; Libobject.Dyn.Easy.inj v objConstant2

(* let x = inExternName ("foo", {dummy=""}) *)

let interp_hints ~poly h =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let fref r =
    let gr = Smartlocate.global_with_alias r in
    Dumpglob.add_glob ?loc:r.CAst.loc gr;
    gr
  in
  let fr r = soft_evaluable ?loc:r.CAst.loc (fref r) in
  let fi c =
    let open Hints in
    let open Vernacexpr in
    match rectify_hint_constr c with
    | HintsReference c ->
      let gr = Smartlocate.global_with_alias c in
      (hint_globref gr)
    | HintsConstr c ->
      let () = warn_deprecated_hint_constr () in
      let env = Global.env () in
      let sigma = Evd.from_env env in
      let c, uctx = Constrintern.interp_constr env sigma c in
      let uctx = UState.normalize_variables uctx in
      let c = Evarutil.nf_evar (Evd.from_ctx uctx) c in
      let c =
        if poly then (c, Some (UState.sort_context_set uctx))
        else
          let () = Global.push_context_set (UState.context_set uctx) in
          (c, None)
      in
      (Hints.hint_constr c) [@ocaml.warning "-3"]
  in
  let fp = Constrintern.intern_constr_pattern env sigma in
  let fres (info, b, r) =
    let gr = fi r in
    let info =
      { info with
        Typeclasses.hint_pattern = Option.map fp info.Typeclasses.hint_pattern
      }
    in
    (info, b, gr)
  in
  let open Hints in
  let open Vernacexpr in
  let ft = function
    | HintsVariables -> HintsVariables
    | HintsConstants -> HintsConstants
    | HintsProjections -> HintsProjections
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
          , hint_globref gr ))
    in
    HintsResolveEntry (List.flatten (List.map constr_hints_of_ind lqid))
  | HintsExtern (pri, patcom, tacexp, name) ->
    let pat = Option.map (fp sigma) patcom in
    let ltacvars = match pat with None -> Id.Set.empty | Some (l, _) -> l in
    let env = Genintern.{(empty_glob_sign ~strict:true env) with ltacvars} in
    let _, tacexp = Genintern.generic_intern env tacexp in
    let extern_name = match name with
    | Some (CAst.{v=Name lname}, _) -> let _ = Lib.add_leaf (inExternName (lname, {dummy=""})) in None (* todo: shouldn't be None *)
    | _ -> None
    in
(*
    try to create object
      give error if already present
      push_extern      (* todo: call push_extern here *)
*)
(*    let extern_name = Option.cata (fun n -> Some (Nametab.global n)) None name in *)
    HintsExternEntry
      ({Typeclasses.hint_priority = Some pri; hint_pattern = pat}, tacexp, extern_name)
