(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Sorts
open Util
open Constr
open Univ

type 'a universe_map = 'a Level.Map.t
type universe_subst = Universe.t universe_map
type universe_subst_fn = Level.t -> Universe.t
type universe_level_subst_fn = Level.t -> Level.t

let subst_instance fn i =
  Instance.of_array (Array.Smart.map fn (Instance.to_array i))

let subst_univs_universe fn ul =
  let addn n u = iterate Universe.super n u in
  let subst, nosubst =
    List.fold_right (fun (u, n) (subst,nosubst) ->
      try let a' = addn n (fn u) in
            (a' :: subst, nosubst)
      with Not_found -> (subst, (u, n) :: nosubst))
      (Universe.repr ul) ([], [])
  in
  match subst with
  | [] -> ul
  | u :: ul ->
    let substs = List.fold_left Universe.sup u subst in
    List.fold_left (fun acc (u, n) -> Universe.sup acc (addn n (Universe.make u))) substs nosubst

let enforce_univ_constraint (u,d,v) =
  match d with
  | Eq -> enforce_eq u v
  | Le -> enforce_leq u v
  | Lt -> enforce_leq (Universe.super u) v

let subst_univs_level fn l =
  try Some (fn l)
  with Not_found -> None

let subst_univs_constraint fn (u,d,v as c) cstrs =
  let u' = subst_univs_level fn u in
  let v' = subst_univs_level fn v in
  match u', v' with
  | None, None -> Constraints.add c cstrs
  | Some u, None -> enforce_univ_constraint (u,d,Universe.make v) cstrs
  | None, Some v -> enforce_univ_constraint (Universe.make u,d,v) cstrs
  | Some u, Some v -> enforce_univ_constraint (u,d,v) cstrs

let subst_univs_constraints subst csts =
  Constraints.fold
    (fun c cstrs -> subst_univs_constraint subst c cstrs)
    csts Constraints.empty

let level_subst_of f =
  fun l ->
    try let u = f l in
          match Universe.level u with
          | None -> l
          | Some l -> l
    with Not_found -> l

let normalize_univ_variable ~find =
  let rec aux cur =
    let b = find cur in
    let b' = subst_univs_universe aux b in
      if Universe.equal b' b then b
      else b'
  in aux

type universe_opt_subst = Universe.t option universe_map

let normalize_univ_variable_opt_subst ectx =
  let find l =
    match Univ.Level.Map.find l ectx with
    | Some b -> b
    | None -> raise Not_found
  in
  normalize_univ_variable ~find

let normalize_universe_opt_subst subst =
  let normlevel = normalize_univ_variable_opt_subst subst in
    subst_univs_universe normlevel

let normalize_opt_subst ctx =
  let normalize = normalize_universe_opt_subst ctx in
  Univ.Level.Map.mapi (fun u -> function
      | None -> None
      | Some v -> Some (normalize v)) ctx

let normalize_univ_variables ctx =
  let ctx = normalize_opt_subst ctx in
  let def, subst =
    Univ.Level.Map.fold (fun u v (def, subst) ->
      match v with
      | None -> (def, subst)
      | Some b -> (Univ.Level.Set.add u def, Univ.Level.Map.add u b subst))
    ctx (Univ.Level.Set.empty, Univ.Level.Map.empty)
  in ctx, def, subst

let subst_univs_fn_puniverses f (c, u as cu) =
  let u' = subst_instance f u in
    if u' == u then cu else (c, u')

let nf_evars_and_universes_opt_subst f subst =
  let subst = normalize_univ_variable_opt_subst subst in
  let lsubst = level_subst_of subst in
  let rec aux c =
    match kind c with
    | Evar (evk, args) ->
      let args' = List.Smart.map aux args in
      (match try f (evk, args') with Not_found -> None with
      | None -> if args == args' then c else mkEvar (evk, args')
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
      let u' = subst_univs_universe subst u in
      if u' == u then c else mkSort (sort_of_univ u')
    | Case (ci,u,pms,p,iv,t,br) ->
      let u' = subst_instance lsubst u in
      if u' == u then Constr.map aux c
      else Constr.map aux (mkCase (ci,u',pms,p,iv,t,br))
    | Array (u,elems,def,ty) ->
      let u' = subst_instance lsubst u in
      let elems' = CArray.Smart.map aux elems in
      let def' = aux def in
      let ty' = aux ty in
      if u == u' && elems == elems' && def == def' && ty == ty' then c
      else mkArray (u',elems',def',ty')
    | _ -> Constr.map aux c
  in aux

let pr_universe_subst =
  let open Pp in
  Level.Map.pr (fun u -> str" := " ++ Universe.pr u ++ spc ())
