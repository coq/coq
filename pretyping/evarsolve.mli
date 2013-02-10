(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Term
open Evd
open Environ

(** Replace the vars and rels that are aliases to other vars and rels by 
   their representative that is most ancient in the context *)
val expand_vars_in_term : env -> constr -> constr

type conv_fun =
  env ->  evar_map -> conv_pb -> constr -> constr -> evar_map * bool

(** [evar_define choose env ev c] try to instantiate [ev] with [c] (typed in [env]),
   possibly solving related unification problems, possibly leaving open
   some problems that cannot be solved in a unique way (except if choose is
   true); fails if the instance is not valid for the given [ev] *)
val evar_define : conv_fun -> ?choose:bool -> env -> evar_map -> 
  existential -> constr -> evar_map

val solve_refl : ?can_drop:bool -> conv_fun -> env ->  evar_map ->
  existential_key -> constr array -> constr array -> evar_map

val solve_evar_evar : ?force:bool ->
  (env -> evar_map -> existential -> constr -> evar_map) -> conv_fun ->
  env ->  evar_map -> existential -> existential -> evar_map

val solve_simple_eqn : conv_fun -> ?choose:bool -> env ->  evar_map ->
  bool option * existential * constr -> evar_map * bool

val reconsider_conv_pbs : conv_fun -> evar_map -> evar_map * bool

val is_unification_pattern_evar : env -> evar_map -> existential -> constr list ->
  constr -> constr list option

val is_unification_pattern : env * int -> evar_map -> constr -> constr list ->
  constr -> constr list option

val solve_pattern_eqn : env -> constr list -> constr -> constr

val check_evar_instance : evar_map -> existential_key -> constr -> conv_fun ->
  evar_map
