open Util
open Declarations
open Constr
open Stages
open Constraints
open Environ

type variance =
  | Variant   (* co-/contra-/bivariant for Ind/CoInd/Record *)
  | Bivariant (* always bivariant (add constraints in both directions *)

let add_constraint_from_ind env variance cstrnts (ind, _) a1 a2 =
  let recursivity = (lookup_mind ind env).mind_finite in
  match variance, recursivity with
  | Bivariant, _ | _, BiFinite ->
    let cstrnts = add a1 a2 cstrnts in
    add a2 a1 cstrnts
  | Variant, Finite   -> add a1 a2 cstrnts
  | Variant, CoFinite -> add a2 a1 cstrnts

let add_constraint_from_ind_ref env variance cstrnts_ref ind a1 a2 =
  cstrnts_ref := add_constraint_from_ind env variance !cstrnts_ref ind a1 a2;
  true

(* [annotate_body] assigns fresh stage variables to inductive types
  that might appear in non-type positions, i.e. in all places
  relevant during reduction. *)
let rec annotate_body env cstr =
  let fold_map_constrs env cs =
    Array.Smart.fold_left_map (fun env c -> annotate_body env c) env cs in
  match kind cstr with
  | Cast (c, k, t) ->
    let env, c' = annotate_body env c in
    if c == c' then env, cstr else
    env, mkCast (c', k, t)
  | Lambda (n, t, c) ->
    let env, c' = annotate_body env c in
    if c == c' then env, cstr else
    env, mkLambda (n, t, c')
  | LetIn (n, b, t, c) ->
    let env, b' = annotate_body env b in
    let env, c' = annotate_body env c in
    if b == b' && c == c' then env, cstr else
    env, mkLetIn (n, b', t, c')
  | App (f, args) ->
    let env, f' = annotate_body env f in
    let env, args' = fold_map_constrs env args in
    if f == f' && args == args' then env, cstr else
    env, mkApp (f', args')
  | Ind (iu, _) ->
    let s, env = Environ.next_stage_annot env in
    env, mkIndUS iu s
  | Case (ci, p, c, lf) ->
    let env, c' = annotate_body env c in
    let env, lf' = fold_map_constrs env lf in
    if c == c' && lf == lf' then env, cstr else
    env, mkCase (ci, p, c', lf')
  | Fix (voni, (na, lar, vdef)) ->
    let env, vdef' = fold_map_constrs env vdef in
    if vdef == vdef' then env, cstr else
    env, mkFix (voni, (na, lar, vdef'))
  | CoFix (i, (na, lar, vdef)) ->
    let env, vdef' = fold_map_constrs env vdef in
    if vdef == vdef' then env, cstr else
    env, mkCoFix (i, (na, lar, vdef'))
  | Proj (p, c) ->
    let env, c' = annotate_body env c in
    if c == c' then env, cstr else
    env, mkProj (p, c')
  | _ -> env, cstr
