
(* $Id$ *)

open Names

type universe = { u_sp : section_path; u_num : int }

val dummy_univ : universe

val prop_univ : universe
val prop_univ_univ : universe
val prop_univ_univ_univ : universe

type universes

val initial_universes : universes

val super : universe -> universes -> universe * universes

val sup : universe -> universe -> universes -> universe * universes

type constraint_result = 
  | Consistent of universes
  | Inconsistent

type constraint_function = 
    universe -> universe -> universes -> constraint_result

val enforce_gt : constraint_function
val enforce_geq : constraint_function
val enforce_eq : constraint_function

