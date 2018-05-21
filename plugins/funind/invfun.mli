(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

val invfun :
  Tactypes.quantified_hypothesis ->
  Names.GlobRef.t option ->
  Evar.t Evd.sigma -> Evar.t list Evd.sigma
val derive_correctness :
  (Evd.evar_map ref ->
   (Constr.pconstant * Sorts.family) list ->
   'a Entries.definition_entry list) ->
   Constr.pconstant list -> Names.inductive list -> unit
