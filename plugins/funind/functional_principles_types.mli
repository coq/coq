(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Term
open Misctypes

val generate_functional_principle :
  Evd.evar_map ref -> 
  (* do we accept interactive proving *)
  bool ->
  (* induction principle on rel *)
  types ->
  (* *)
  Sorts.t array option ->
  (* Name of the new principle *)
  (Id.t) option ->
  (* the compute functions to use   *)
  pconstant array ->
  (* We prove the nth- principle *)
  int  ->
  (* The tactic to use to make the proof w.r
     the number of params
  *)
  (EConstr.constr array -> int -> Tacmach.tactic) ->
  unit

val compute_new_princ_type_from_rel : constr array -> Sorts.t array ->
  types -> types


exception No_graph_found

val make_scheme :   Evd.evar_map ref ->
 (pconstant*glob_sort) list -> Safe_typing.private_constants Entries.definition_entry list

val build_scheme : (Id.t*Libnames.reference*glob_sort) list ->  unit
val build_case_scheme : (Id.t*Libnames.reference*glob_sort)  ->  unit

