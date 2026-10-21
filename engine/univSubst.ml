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
type universe_level_subst_fn = Level.t -> Universe.t

type quality_subst = Quality.t QVar.Map.t
type quality_subst_fn = QVar.t -> Quality.t

let level_subst_of f =
  fun l ->
  match f l with
  | None  -> Universe.make l
  | Some u -> u

let subst_univs_level fn l =
  match fn l with
  | None -> Universe.make l
  | Some u -> u

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

let enforce_eq u v c = Univ.enforce_eq u v c

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
  if check_univ_leq u v then c
  else Univ.enforce_leq u v c

let enforce_univ_constraint (u,d,v) =
  let open UnivConstraint in
  match d with
  | Eq -> enforce_eq u v
  | Le -> enforce_leq u v

let subst_univs_constraint fn (u,d,v) cstrs =
  let u' = subst_univs_universe fn u in
  let v' = subst_univs_universe fn v in
  enforce_univ_constraint (u',d,v') cstrs

let subst_univs_constraints subst csts =
  UnivConstraints.fold
    (fun c cstrs -> subst_univs_constraint subst c cstrs)
    csts UnivConstraints.empty

let subst_univs_fn_puniverses f (c, u as cu) =
  let u' = Instance.subst_fn f u in
    if u' == u then cu else (c, u')

let map_universes_opt_subst_aux_rec next aux frel k ((nas, tys, bds) as rc) =
  let nas' = Array.Smart.map (Context.map_annot_relevance frel) nas in
  let tys' = Array.Fun1.Smart.map aux k tys in
  let k' = iterate next (Array.length tys') k in
  let bds' = Array.Fun1.Smart.map aux k' bds in
  if nas' == nas && tys' == tys && bds' == bds then rc
  else (nas', tys', bds')

let map_universes_opt_subst_aux_ctx next aux frel k ((nas, c) as p) =
  let nas' = Array.Smart.map (Context.map_annot_relevance frel) nas in
  let k' = iterate next (Array.length nas) k in
  let c' = aux k' c in
  if nas' == nas && c' == c then p
  else (nas', c')

let map_universes_opt_subst_with_binders next aux frel fqual funiv k c =
  let flevel = fqual, level_subst_of funiv in
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
    let s' = Sorts.subst_fn (fqual, subst_univs_level funiv) s in
    if s' == s then c else mkSort s'
  | Case (ci,u,pms,(p,rel),iv,t,br) ->
    let u' = Instance.subst_fn flevel u in
    let rel' = frel rel in
    let pms' = Array.Fun1.Smart.map aux k pms in
    let aux_ctx = map_universes_opt_subst_aux_ctx next aux frel k in
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
    let rc' = map_universes_opt_subst_aux_rec next aux frel k rc in
    if rc' == rc then c
    else mkFix (i, rc')
  | CoFix (i, rc) ->
    let rc' = map_universes_opt_subst_aux_rec next aux frel k rc in
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
