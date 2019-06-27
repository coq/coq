open Environ
open Declarations
open Stages

let add_constraint_from_ind env cstrnts_ref (ind, _) a1 a2 =
  let recursivity = (lookup_mind ind env).mind_finite in
  cstrnts_ref := match recursivity with
  | Finite   -> add_constraint a1 a2 !cstrnts_ref
  | CoFinite -> add_constraint a2 a1 !cstrnts_ref
  | BiFinite ->
    let cstrnts = add_constraint a1 a2 !cstrnts_ref in
    add_constraint a2 a1 cstrnts
