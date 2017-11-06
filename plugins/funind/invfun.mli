(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

val invfun :
  Misctypes.quantified_hypothesis ->
  Names.global_reference option ->
  Evar.t Evd.sigma -> Evar.t list Evd.sigma
val derive_correctness :
  (Evd.evar_map ref ->
   (Constr.pconstant * Sorts.family) list ->
   'a Entries.definition_entry list) ->
   Constr.pconstant list -> Names.inductive list -> unit
