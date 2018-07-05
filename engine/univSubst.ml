(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Sorts
open Util
open Pp
open Constr
open Univ

let enforce_univ_constraint (u,d,v) =
  match d with
  | Eq -> enforce_eq u v
  | Le -> enforce_leq u v
  | Lt -> enforce_leq (super u) v

let subst_univs_level fn l =
  try Some (fn l)
  with Not_found -> None

let subst_univs_constraint fn (u,d,v as c) cstrs =
  let u' = subst_univs_level fn u in
  let v' = subst_univs_level fn v in
  match u', v' with
  | None, None -> Constraint.add c cstrs
  | Some u, None -> enforce_univ_constraint (u,d,Universe.make v) cstrs
  | None, Some v -> enforce_univ_constraint (Universe.make u,d,v) cstrs
  | Some u, Some v -> enforce_univ_constraint (u,d,v) cstrs

let subst_univs_constraints subst csts =
  Constraint.fold
    (fun c cstrs -> subst_univs_constraint subst c cstrs)
    csts Constraint.empty

let level_subst_of f =
  fun l ->
    try let u = f l in
          match Universe.level u with
          | None -> l
          | Some l -> l
    with Not_found -> l

let subst_univs_fn_constr f c =
  let changed = ref false in
  let fu = Univ.subst_univs_universe f in
  let fi = Univ.Instance.subst_fn (level_subst_of f) in
  let rec aux t =
    match kind t with
    | Sort (Sorts.Type u) ->
      let u' = fu u in
        if u' == u then t else
          (changed := true; mkSort (Sorts.sort_of_univ u'))
    | Const (c, u) ->
      let u' = fi u in
        if u' == u then t
        else (changed := true; mkConstU (c, u'))
    | Ind (i, u) ->
      let u' = fi u in
        if u' == u then t
        else (changed := true; mkIndU (i, u'))
    | Construct (c, u) ->
      let u' = fi u in
        if u' == u then t
        else (changed := true; mkConstructU (c, u'))
    | _ -> map aux t
  in
  let c' = aux c in
    if !changed then c' else c

let subst_univs_constr subst c =
  if Univ.is_empty_subst subst then c
  else
    let f = Univ.make_subst subst in
      subst_univs_fn_constr f c

let subst_univs_constr =
  if Flags.profile then
    let subst_univs_constr_key = CProfile.declare_profile "subst_univs_constr" in
      CProfile.profile2 subst_univs_constr_key subst_univs_constr
  else subst_univs_constr

let normalize_univ_variable ~find =
  let rec aux cur =
    let b = find cur in
    let b' = subst_univs_universe aux b in
      if Universe.equal b' b then b
      else b'
  in aux

let normalize_univ_variable_opt_subst ectx =
  let find l =
    match Univ.LMap.find l ectx with
    | Some b -> b
    | None -> raise Not_found
  in
  normalize_univ_variable ~find

let normalize_univ_variable_subst subst =
  let find l = Univ.LMap.find l subst in
  normalize_univ_variable ~find

let normalize_universe_opt_subst subst =
  let normlevel = normalize_univ_variable_opt_subst subst in
    subst_univs_universe normlevel

let normalize_universe_subst subst =
  let normlevel = normalize_univ_variable_subst subst in
    subst_univs_universe normlevel

let normalize_opt_subst ctx =
  let normalize = normalize_universe_opt_subst ctx in
  Univ.LMap.mapi (fun u -> function
      | None -> None
      | Some v -> Some (normalize v)) ctx

type universe_opt_subst = Universe.t option universe_map

let subst_univs_fn_puniverses f (c, u as cu) =
  let u' = Instance.subst_fn f u in
    if u' == u then cu else (c, u')

let nf_evars_and_universes_opt_subst f subst =
  let subst = normalize_univ_variable_opt_subst subst in
  let lsubst = level_subst_of subst in
  let rec aux c =
    match kind c with
    | Evar (evk, args) ->
      let args = Array.map aux args in
      (match try f (evk, args) with Not_found -> None with
      | None -> mkEvar (evk, args)
      | Some c -> aux c)
    | Const pu ->
      let pu' = subst_univs_fn_puniverses lsubst pu in
        if pu' == pu then c else mkConstU pu'
    | Ind pu ->
      let pu' = subst_univs_fn_puniverses lsubst pu in
        if pu' == pu then c else mkIndU pu'
    | Construct pu ->
      let pu' = subst_univs_fn_puniverses lsubst pu in
        if pu' == pu then c else mkConstructU pu'
    | Sort (Type u) ->
      let u' = Univ.subst_univs_universe subst u in
        if u' == u then c else mkSort (sort_of_univ u')
    | _ -> Constr.map aux c
  in aux

let make_opt_subst s =
  fun x ->
    (match Univ.LMap.find x s with
    | Some u -> u
    | None -> raise Not_found)

let subst_opt_univs_constr s =
  let f = make_opt_subst s in
  subst_univs_fn_constr f

let normalize_univ_variables ctx =
  let ctx = normalize_opt_subst ctx in
  let def, subst =
    Univ.LMap.fold (fun u v (def, subst) ->
      match v with
      | None -> (def, subst)
      | Some b -> (Univ.LSet.add u def, Univ.LMap.add u b subst))
    ctx (Univ.LSet.empty, Univ.LMap.empty)
  in ctx, def, subst

let pr_universe_body = function
  | None -> mt ()
  | Some v -> str" := " ++ Univ.Universe.pr v

let pr_universe_opt_subst = Univ.LMap.pr pr_universe_body
