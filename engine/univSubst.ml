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
type universe_subst_fn = Level.t -> Universe.t option
type universe_level_subst_fn = Level.t -> Level.t

let subst_instance fn i =
  Instance.of_array (Array.Smart.map fn (Instance.to_array i))

let subst_univs_universe fn ul =
  let addn n u = iterate Universe.super n u in
  let subst, nosubst =
    List.fold_right (fun (u, n) (subst,nosubst) ->
        match fn u with
        | Some u' ->
          let a' = addn n u' in
          (a' :: subst, nosubst)
        | None -> (subst, (u, n) :: nosubst))
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
| Prop | SProp | QSort _ -> assert false
| Set -> Universe.type0
| Type u -> u

let enforce_eq_sort s1 s2 cst = match s1, s2 with
| (SProp, SProp) | (Prop, Prop) | (Set, Set) -> cst
| (((Prop | Set | Type _ | QSort _) as s1), (Prop | SProp as s2))
| ((Prop | SProp as s1), ((Prop | Set | Type _ | QSort _) as s2)) ->
  raise (UGraph.UniverseInconsistency (Eq, s1, s2, None))
| (Set | Type _), (Set | Type _) ->
  enforce_eq (get_algebraic s1) (get_algebraic s2) cst
| QSort (q1, u1), QSort (q2, u2) ->
  if QVar.equal q1 q2 then enforce_eq u1 u2 cst
  else raise (UGraph.UniverseInconsistency (Eq, s1, s2, None))
| (QSort _, (Set | Type _)) | ((Set | Type _), QSort _) ->
  raise (UGraph.UniverseInconsistency (Eq, s1, s2, None))

let enforce_leq_sort s1 s2 cst = match s1, s2 with
| (SProp, SProp) | (Prop, Prop) | (Set, Set) -> cst
| (Prop, (Set | Type _)) -> cst
| (((Prop | Set | Type _ | QSort _) as s1), (Prop | SProp as s2))
| ((SProp as s1), ((Prop | Set | Type _ | QSort _) as s2)) ->
  raise (UGraph.UniverseInconsistency (Le, s1, s2, None))
| (Set | Type _), (Set | Type _) ->
  enforce_leq (get_algebraic s1) (get_algebraic s2) cst
| QSort (q1, u1), QSort (q2, u2) ->
  if QVar.equal q1 q2 then enforce_leq u1 u2 cst
  else raise (UGraph.UniverseInconsistency (Eq, s1, s2, None))
| (QSort _, (Set | Type _)) | ((Prop | Set | Type _), QSort _) ->
  raise (UGraph.UniverseInconsistency (Eq, s1, s2, None))

let enforce_leq_alg_sort s1 s2 g = match s1, s2 with
| (SProp, SProp) | (Prop, Prop) | (Set, Set) -> Constraints.empty, g
| (Prop, (Set | Type _)) -> Constraints.empty, g
| (((Prop | Set | Type _ | QSort _) as s1), (Prop | SProp as s2))
| ((SProp as s1), ((Prop | Set | Type _ | QSort _) as s2)) ->
  raise (UGraph.UniverseInconsistency (Le, s1, s2, None))
| (Set | Type _), (Set | Type _) ->
  UGraph.enforce_leq_alg (get_algebraic s1) (get_algebraic s2) g
| QSort (q1, u1), QSort (q2, u2) ->
  if QVar.equal q1 q2 then UGraph.enforce_leq_alg u1 u2 g
  else raise (UGraph.UniverseInconsistency (Eq, s1, s2, None))
| (QSort _, (Set | Type _)) | ((Prop | Set | Type _), QSort _) ->
  raise (UGraph.UniverseInconsistency (Eq, s1, s2, None))

let enforce_univ_constraint (u,d,v) =
  match d with
  | Eq -> enforce_eq u v
  | Le -> enforce_leq u v
  | Lt -> enforce_leq (Universe.super u) v

let subst_univs_constraint fn (u,d,v as c) cstrs =
  let u' = fn u in
  let v' = fn v in
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
  match f l with
  | None  -> l
  | Some u ->
    match Universe.level u with
    | None -> assert false
    | Some l -> l

let subst_univs_fn_puniverses f (c, u as cu) =
  let u' = subst_instance f u in
    if u' == u then cu else (c, u')

let nf_binder_annot frel na =
  let open Context in
  let rel' = frel na.binder_relevance in
  if rel' == na.binder_relevance then na
  else { binder_name = na.binder_name; binder_relevance = rel' }

let nf_evars_and_universes_opt_subst fevar flevel fsort frel c =
  let rec aux c =
    match kind c with
    | Evar (evk, args) ->
      let args' = SList.Smart.map aux args in
      (match try fevar (evk, args') with Not_found -> None with
      | None -> if args == args' then c else mkEvar (evk, args')
      | Some c -> aux c)
    | Const pu ->
      let pu' = subst_univs_fn_puniverses flevel pu in
        if pu' == pu then c else mkConstU pu'
    | Ind pu ->
      let pu' = subst_univs_fn_puniverses flevel pu in
        if pu' == pu then c else mkIndU pu'
    | Construct pu ->
      let pu' = subst_univs_fn_puniverses flevel pu in
        if pu' == pu then c else mkConstructU pu'
    | Sort s ->
      let s' = fsort s in
      if s' == s then c else mkSort s'
    | Case (ci,u,pms,p,iv,t,br) ->
      let u' = subst_instance flevel u in
      let ci' =
        let rel' = frel ci.ci_relevance in
        if rel' == ci.ci_relevance then ci else { ci with ci_relevance = rel' }
      in
      let pms' = Array.Smart.map aux pms in
      let p' = aux_ctx p in
      let iv' = map_invert aux iv in
      let t' = aux t in
      let br' = Array.Smart.map aux_ctx br in
      if ci' == ci && u' == u && pms' == pms && p' == p && iv' == iv && t' == t && br' == br then c
      else mkCase (ci', u', pms', p', iv', t', br')
    | Array (u,elems,def,ty) ->
      let u' = subst_instance flevel u in
      let elems' = CArray.Smart.map aux elems in
      let def' = aux def in
      let ty' = aux ty in
      if u == u' && elems == elems' && def == def' && ty == ty' then c
      else mkArray (u',elems',def',ty')
    | Prod (na, t, u) ->
      let na' = nf_binder_annot frel na in
      let t' = aux t in
      let u' = aux u in
      if na' == na && t' == t && u' == u then c
      else mkProd (na', t', u')
    | Lambda (na, t, u) ->
      let na' = nf_binder_annot frel na in
      let t' = aux t in
      let u' = aux u in
      if na' == na && t' == t && u' == u then c
      else mkLambda (na', t', u')
    | LetIn (na, b, t, u) ->
      let na' = nf_binder_annot frel na in
      let b' = aux b in
      let t' = aux t in
      let u' = aux u in
      if na' == na && b' == b && t' == t && u' == u then c
      else mkLetIn (na', b', t', u')
    | Fix (i, rc) ->
      let rc' = aux_rec rc in
      if rc' == rc then c
      else mkFix (i, rc')
    | CoFix (i, rc) ->
      let rc' = aux_rec rc in
      if rc' == rc then c
      else mkCoFix (i, rc')
    | _ -> Constr.map aux c
  and aux_rec ((nas, tys, bds) as rc) =
    let nas' = Array.Smart.map (fun na -> nf_binder_annot frel na) nas in
    let tys' = Array.Smart.map aux tys in
    let bds' = Array.Smart.map aux bds in
    if nas' == nas && tys' == tys && bds' == bds then rc
    else (nas', tys', bds')
  and aux_ctx ((nas, c) as p) =
    let nas' = Array.Smart.map (fun na -> nf_binder_annot frel na) nas in
    let c' = aux c in
    if nas' == nas && c' == c then p
    else (nas', c')
  in
  aux c

let pr_universe_subst prl =
  let open Pp in
  Level.Map.pr prl (fun u -> str" := " ++ Universe.pr prl u ++ spc ())
