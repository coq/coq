(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
open Names
open Term
open Pre_env
open Nativevalues
open Nativeinstr

(** This file defines the lambda code generation phase of the native compiler *)
type evars =
    { evars_val : existential -> constr option;
      evars_typ : existential -> types;
      evars_metas : metavariable -> types }

val empty_evars : evars

val decompose_Llam : lambda -> Names.name array * lambda
val decompose_Llam_Llet : lambda -> (Names.name * lambda option) array * lambda

val is_lazy : prefix -> constr -> bool
val mk_lazy : lambda -> lambda

val get_mind_prefix : env -> mutual_inductive -> string

val get_allias : env -> pconstant -> pconstant

val lambda_of_constr : env -> evars -> Constr.constr -> lambda

val compile_static_int31 : bool -> Constr.constr array -> lambda

val compile_dynamic_int31 : bool -> prefix -> constructor -> lambda array ->
			    lambda

val before_match_int31 : inductive -> bool -> prefix -> constructor -> lambda ->
			 lambda

val compile_prim : Primitives.t -> constant -> bool -> prefix -> lambda array ->
		   lambda
