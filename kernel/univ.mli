
(* $Id$ *)

open Names

type universe = { u_sp : section_path; u_num : int }

val dummy_univ : universe

val prop_univ : universe
val prop_univ_univ : universe
val prop_univ_univ_univ : universe

type universes
