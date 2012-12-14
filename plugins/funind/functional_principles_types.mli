open Names
open Term
open Misctypes

val generate_functional_principle :
  (* do we accept interactive proving *)
  bool ->
  (* induction principle on rel *)
  types ->
  (* *)
  sorts array option ->
  (* Name of the new principle *)
  (Id.t) option ->
  (* the compute functions to use   *)
  constant array ->
  (* We prove the nth- principle *)
  int  ->
  (* The tactic to use to make the proof w.r
     the number of params
  *)
  (constr array -> int -> Tacmach.tactic) ->
  unit

val compute_new_princ_type_from_rel : constr array -> sorts array ->
  types -> types


exception No_graph_found

val make_scheme : (constant*glob_sort) list -> Entries.definition_entry list

val build_scheme : (Id.t*Libnames.reference*glob_sort) list ->  unit
val build_case_scheme : (Id.t*Libnames.reference*glob_sort)  ->  unit

