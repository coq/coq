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

let enforce_eq u v c =
  if Universe.equal u v then c else match Universe.level u, Universe.level v with
  | Some u, Some v -> enforce_eq_level u v c
  | _ -> CErrors.anomaly (Pp.str "A universe comparison can only happen between variables.")

let constraint_add_leq v u c =
  let eq (x, n) (y, m) = Int.equal m n && Level.equal x y in
  (* We just discard trivial constraints like u<=u *)
  if eq v u then c
  else
    match v, u with
    | (x,n), (y,m) ->
    let j = m - n in
      if j = -1 (* n = m+1, v+1 <= u <-> v < u *) then
        Constraints.add (x,Lt,y) c
      else if j <= -1 (* n = m+k, v+k <= u and k>0 *) then
        if Level.equal x y then (* u+k <= u with k>0 *)
          Constraints.add (x,Lt,x) c
        else CErrors.anomaly (Pp.str"Unable to handle arbitrary u+k <= v constraints.")
      else if j = 0 then
        Constraints.add (x,Le,y) c
      else (* j >= 1 *) (* m = n + k, u <= v+k *)
        if Level.equal x y then c (* u <= u+k, trivial *)
        else if Level.is_set x then c (* Prop,Set <= u+S k, trivial *)
        else Constraints.add (x,Le,y) c (* u <= v implies u <= v+k *)

let check_univ_leq_one u v =
  let leq (u,n) (v,n') =
    let cmp = Level.compare u v in
      if Int.equal cmp 0 then n <= n'
      else false
  in
  Universe.exists (leq u) v

let check_univ_leq u v =
  Universe.for_all (fun u -> check_univ_leq_one u v) u

let enforce_leq u v c =
  List.fold_left (fun c v -> (List.fold_left (fun c u -> constraint_add_leq u v c) c u)) c v

let enforce_leq u v c =
  if check_univ_leq u v then c
  else enforce_leq (Universe.repr u) (Universe.repr v) c

let get_algebraic = function
| Prop | SProp -> assert false
| Set -> Universe.type0
| Type u -> u

let enforce_eq_sort s1 s2 cst = match s1, s2 with
| (SProp, SProp) | (Prop, Prop) | (Set, Set) -> cst
| (((Prop | Set | Type _) as s1), (Prop | SProp as s2))
| ((Prop | SProp as s1), ((Prop | Set | Type _) as s2)) ->
  raise (UGraph.UniverseInconsistency (Eq, s1, s2, None))
| (Set | Type _), (Set | Type _) ->
  enforce_eq (get_algebraic s1) (get_algebraic s2) cst

let enforce_leq_sort s1 s2 cst = match s1, s2 with
| (SProp, SProp) | (Prop, Prop) | (Set, Set) -> cst
| (Prop, (Set | Type _)) -> cst
| (((Prop | Set | Type _) as s1), (Prop | SProp as s2))
| ((SProp as s1), ((Prop | Set | Type _) as s2)) ->
  raise (UGraph.UniverseInconsistency (Le, s1, s2, None))
| (Set | Type _), (Set | Type _) ->
  enforce_leq (get_algebraic s1) (get_algebraic s2) cst

let enforce_leq_alg_sort s1 s2 g = match s1, s2 with
| (SProp, SProp) | (Prop, Prop) | (Set, Set) -> Constraints.empty, g
| (Prop, (Set | Type _)) -> Constraints.empty, g
| (((Prop | Set | Type _) as s1), (Prop | SProp as s2))
| ((SProp as s1), ((Prop | Set | Type _) as s2)) ->
  if UGraph.cumulative_sprop g && is_sprop s1 then
    Constraints.empty, g
  else
    raise (UGraph.UniverseInconsistency (Le, s1, s2, None))
| (Set | Type _), (Set | Type _) ->
  UGraph.enforce_leq_alg (get_algebraic s1) (get_algebraic s2) g

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
