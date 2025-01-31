(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
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
open UVars

type 'a universe_map = 'a Level.Map.t
type universe_subst = Universe.t universe_map
type universe_subst_fn = Level.t -> Universe.t option
type universe_level_subst_fn = Level.t -> Level.t

type quality_subst = Quality.t QVar.Map.t
type quality_subst_fn = QVar.t -> Quality.t

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
  raise (UGraph.UniverseInconsistency (None, (Eq, s1, s2, None)))
| (Set | Type _), (Set | Type _) ->
  enforce_eq (get_algebraic s1) (get_algebraic s2) cst
| QSort (q1, u1), QSort (q2, u2) ->
  if QVar.equal q1 q2 then enforce_eq u1 u2 cst
  else raise (UGraph.UniverseInconsistency (None, (Eq, s1, s2, None)))
| (QSort _, (Set | Type _)) | ((Set | Type _), QSort _) ->
  raise (UGraph.UniverseInconsistency (None, (Eq, s1, s2, None)))

let enforce_leq_sort s1 s2 cst = match s1, s2 with
| (SProp, SProp) | (Prop, Prop) | (Set, Set) -> cst
| (Prop, (Set | Type _)) -> cst
| (((Prop | Set | Type _ | QSort _) as s1), (Prop | SProp as s2))
| ((SProp as s1), ((Prop | Set | Type _ | QSort _) as s2)) ->
  raise (UGraph.UniverseInconsistency (None, (Le, s1, s2, None)))
| (Set | Type _), (Set | Type _) ->
  enforce_leq (get_algebraic s1) (get_algebraic s2) cst
| QSort (q1, u1), QSort (q2, u2) ->
  if QVar.equal q1 q2 then enforce_leq u1 u2 cst
  else raise (UGraph.UniverseInconsistency (None, (Eq, s1, s2, None)))
| (QSort _, (Set | Type _)) | ((Prop | Set | Type _), QSort _) ->
  raise (UGraph.UniverseInconsistency (None, (Eq, s1, s2, None)))

let enforce_leq_alg_sort s1 s2 g = match s1, s2 with
| (SProp, SProp) | (Prop, Prop) | (Set, Set) -> Constraints.empty, g
| (Prop, (Set | Type _)) -> Constraints.empty, g
| (((Prop | Set | Type _ | QSort _) as s1), (Prop | SProp as s2))
| ((SProp as s1), ((Prop | Set | Type _ | QSort _) as s2)) ->
  raise (UGraph.UniverseInconsistency (None, (Le, s1, s2, None)))
| (Set | Type _), (Set | Type _) ->
  UGraph.enforce_leq_alg (get_algebraic s1) (get_algebraic s2) g
| QSort (q1, u1), QSort (q2, u2) ->
  if QVar.equal q1 q2 then UGraph.enforce_leq_alg u1 u2 g
  else raise (UGraph.UniverseInconsistency (None, (Eq, s1, s2, None)))
| (QSort _, (Set | Type _)) | ((Prop | Set | Type _), QSort _) ->
  raise (UGraph.UniverseInconsistency (None, (Eq, s1, s2, None)))

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
  let u' = Instance.subst_fn f u in
    if u' == u then cu else (c, u')

let map_universes_opt_subst_with_binders next aux frel fqual funiv k c =
  let flevel = fqual, level_subst_of funiv in
  let aux_rec ((nas, tys, bds) as rc) =
    let nas' = Array.Smart.map (Context.map_annot_relevance frel) nas in
    let tys' = Array.Fun1.Smart.map aux k tys in
    let k' = iterate next (Array.length tys') k in
    let bds' = Array.Fun1.Smart.map aux k' bds in
    if nas' == nas && tys' == tys && bds' == bds then rc
    else (nas', tys', bds')
  in
  let aux_ctx ((nas, c) as p) =
    let nas' = Array.Smart.map (Context.map_annot_relevance frel) nas in
    let k' = iterate next (Array.length nas) k in
    let c' = aux k' c in
    if nas' == nas && c' == c then p
    else (nas', c')
  in
  match kind c with
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
    let s' = Sorts.subst_fn (fqual, subst_univs_universe funiv) s in
    if s' == s then c else mkSort s'
  | Case (ci,u,pms,(p,rel),iv,t,br) ->
    let u' = Instance.subst_fn flevel u in
    let rel' = frel rel in
    let pms' = Array.Fun1.Smart.map aux k pms in
    let p' = aux_ctx p in
    let iv' = map_invert (aux k) iv in
    let t' = aux k t in
    let br' = Array.Smart.map aux_ctx br in
    if rel' == rel && u' == u && pms' == pms && p' == p && iv' == iv && t' == t && br' == br then c
    else mkCase (ci, u', pms', (p',rel'), iv', t', br')
  | Array (u,elems,def,ty) ->
    let u' = Instance.subst_fn flevel u in
    let elems' = CArray.Fun1.Smart.map aux k elems in
    let def' = aux k def in
    let ty' = aux k ty in
    if u == u' && elems == elems' && def == def' && ty == ty' then c
    else mkArray (u',elems',def',ty')
  | Prod (na, t, u) ->
    let na' = Context.map_annot_relevance frel na in
    let t' = aux k t in
    let u' = aux (next k) u in
    if na' == na && t' == t && u' == u then c
    else mkProd (na', t', u')
  | Lambda (na, t, u) ->
    let na' = Context.map_annot_relevance frel na in
    let t' = aux k t in
    let u' = aux (next k) u in
    if na' == na && t' == t && u' == u then c
    else mkLambda (na', t', u')
  | LetIn (na, b, t, u) ->
    let na' = Context.map_annot_relevance frel na in
    let b' = aux k b in
    let t' = aux k t in
    let u' = aux (next k) u in
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
  | Proj (p, r, v) ->
    let r' = frel r in
    let v' = aux k v in
    if r' == r && v' == v then  c
    else mkProj (p, r', v')
  | _ -> Constr.map_with_binders next aux k c

let nf_evars_and_universes_opt_subst fevar frel fqual funiv c =
  let rec self () c = match Constr.kind c with
  | Evar (evk, args) ->
    let args' = SList.Smart.map (self ()) args in
    begin match try fevar (evk, args') with Not_found -> None with
    | None -> if args == args' then c else mkEvar (evk, args')
    | Some c -> self () c
    end
  | _ -> map_universes_opt_subst_with_binders ignore self frel fqual funiv () c
  in
  self () c

let pr_universe_subst prl =
  let open Pp in
  Level.Map.pr prl (fun u -> str" := " ++ Universe.pr prl u ++ spc ())
