open Environ
open Declarations
open Stages
open Constraints

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
