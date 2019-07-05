open Environ
open Declarations
open Stages
open Constraints

let add_constraint_from_ind env cstrnts (ind, _) a1 a2 =
  let recursivity = (lookup_mind ind env).mind_finite in
  match recursivity with
  | Finite   -> add a1 a2 cstrnts
  | CoFinite -> add a2 a1 cstrnts
  | BiFinite ->
    let cstrnts = add a1 a2 cstrnts in
    add a2 a1 cstrnts

let add_constraint_from_ind_ref env cstrnts_ref ind a1 a2 =
  cstrnts_ref := add_constraint_from_ind env !cstrnts_ref ind a1 a2
