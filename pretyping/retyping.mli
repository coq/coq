(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(*i*)
open Names
open Term
open Evd
open Environ
(*i*)

(* This family of functions assumes its constr argument is known to be
   well-typable. It does not type-check, just recompute the type
   without any costly verifications. On non well-typable terms, it
   either produces a wrong result or raise an anomaly. Use with care.
   It doesn't handle predicative universes too. *)

(** The "polyprop" optional argument is used by the extraction to
    disable "Prop-polymorphism", cf comment in [inductive.ml] *)

val get_type_of :
  ?polyprop:bool -> ?refresh:bool -> env -> evar_map -> constr -> types

val get_sort_of :
  ?polyprop:bool -> env -> evar_map -> types -> sorts

val get_sort_family_of :
  ?polyprop:bool -> env -> evar_map -> types -> sorts_family

(* Makes an assumption from a constr *)
val get_assumption_of : env -> evar_map -> constr -> types

(* Makes an unsafe judgment from a constr *)
val get_judgment_of : env -> evar_map -> constr -> unsafe_judgment

val type_of_global_reference_knowing_parameters : env -> evar_map -> constr ->
  constr array -> types

val type_of_global_reference_knowing_conclusion :
  env -> evar_map -> constr -> types -> types
