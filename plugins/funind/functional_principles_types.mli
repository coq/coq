(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Constr

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

exception No_graph_found

val make_scheme :   Evd.evar_map ref ->
 (pconstant*Sorts.family) list -> Safe_typing.private_constants Entries.definition_entry list

val build_scheme : (Id.t*Libnames.qualid*Sorts.family) list ->  unit
val build_case_scheme : (Id.t*Libnames.qualid*Sorts.family)  ->  unit
