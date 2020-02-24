(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pattern
open Genredexpr
open Glob_term
open Tacred
open Util
open Names
open Libnames
open Smartlocate
open Constrexpr
open Termops
open Locus
open Genintern
open CAst
open Constrmetaintern

let intern_evaluable_global_reference ist qid =
  try evaluable_of_global_reference ist.genv (locate_global_with_alias ~head:true qid)
  with Not_found ->
  if qualid_is_ident qid && not ist.strict_check then EvalVarRef (qualid_basename qid)
  else Nametab.error_global_not_found qid

let intern_evaluable_reference_or_by_notation ist = function
  | {v=AN r} -> intern_evaluable_global_reference ist r
  | {v=ByNotation (ntn,sc);loc} ->
      evaluable_of_global_reference ist.genv
      (Notation.interp_notation_as_global_reference ?loc
        GlobRef.(function ConstRef _ | VarRef _ -> true | _ -> false) ntn sc)

let short_name strict = function
  | {v=AN qid} when qualid_is_ident qid && not strict ->
    Some (make ?loc:qid.CAst.loc @@ qualid_basename qid)
  | _ -> None

let find_var id ist = Id.Set.mem id ist.ltacvars

let find_hyp id ist =
  Id.List.mem id (ids_of_named_context (Environ.named_context ist.genv))

(* Globalize a reduction expression *)
let intern_evaluable ist r =
  let f ist r =
    let e = intern_evaluable_reference_or_by_notation ist r in
    let na = short_name ist.strict_check r in
    ArgArg (e,na)
  in
  match r with
  | {v=AN qid} when qualid_is_ident qid && find_var (qualid_basename qid) ist ->
    ArgVar (make ?loc:qid.CAst.loc @@ qualid_basename qid)
  | {v=AN qid} when qualid_is_ident qid && not ist.strict_check && find_hyp (qualid_basename qid) ist ->
    let id = qualid_basename qid in
      ArgArg (EvalVarRef id, Some (make ?loc:qid.CAst.loc id))
  | _ -> f ist r

let intern_unfold ist (l,qid) = (l,intern_evaluable ist qid)

let intern_flag ist red =
  { red with rConst = List.map (intern_evaluable ist) red.rConst }

let intern_constr_with_occurrences ist (l,c) = (l,intern_constr ist c)

let dummy_pat = PRel 0

let intern_typed_pattern_or_ref_with_occurrences ist (l,p) =
  let interp_ref r =
    try Inl (intern_evaluable ist r)
    with e when CErrors.noncritical e ->
      (* Compatibility. In practice, this means that the code above
         is useless. Still the idea of having either an evaluable
         ref or a pattern seems interesting, with "head" reduction
         in case of an evaluable ref, and "strong" reduction in the
         subterm matched when a pattern *)
      let r = match r with
      | {v=AN r} -> r
      | {loc} -> (qualid_of_path ?loc (Nametab.path_of_global (smart_global r))) in
      let sign = {
        Constrintern.ltac_vars = ist.ltacvars;
        ltac_bound = Id.Set.empty;
        ltac_extra = ist.extra;
      } in
      let c = Constrintern.interp_reference sign r in
      match DAst.get c with
      | GRef (r,None) ->
          Inl (ArgArg (evaluable_of_global_reference ist.genv r,None))
      | GVar id ->
          let r = evaluable_of_global_reference ist.genv (GlobRef.VarRef id) in
          Inl (ArgArg (r,None))
      | _ ->
          let bound_names = Glob_ops.bound_glob_vars c in
          Inr (bound_names,(c,None),dummy_pat) in
  (l, match p with
  | Inl r -> interp_ref r
  | Inr { v = CAppExpl((None,r,None),[]) } ->
      (* We interpret similarly @ref and ref *)
      interp_ref (make @@ AN r)
  | Inr c ->
      Inr (snd (intern_typed_pattern ist ~as_type:false ~ltacvars:ist.ltacvars c)))

let intern_red_expr ist = function
  | Unfold l -> Unfold (List.map (intern_unfold ist) l)
  | Fold l -> Fold (List.map (intern_constr ist) l)
  | Cbv f -> Cbv (intern_flag ist f)
  | Cbn f -> Cbn (intern_flag ist f)
  | Lazy f -> Lazy (intern_flag ist f)
  | Pattern l -> Pattern (List.map (intern_constr_with_occurrences ist) l)
  | Simpl (f,o) ->
    Simpl (intern_flag ist f,
           Option.map (intern_typed_pattern_or_ref_with_occurrences ist) o)
  | CbvVm o -> CbvVm (Option.map (intern_typed_pattern_or_ref_with_occurrences ist) o)
  | CbvNative o -> CbvNative (Option.map (intern_typed_pattern_or_ref_with_occurrences ist) o)
  | (Red _ | Hnf | ExtraRedExpr _ as r ) -> r
