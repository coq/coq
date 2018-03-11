(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open EConstr
open Evd
open Environ

type alias

val of_alias : alias -> EConstr.t

type unification_result =
  | Success of evar_map
  | UnifFailure of evar_map * Pretype_errors.unification_error

val is_success : unification_result -> bool

(** Replace the vars and rels that are aliases to other vars and rels by 
   their representative that is most ancient in the context *)
val expand_vars_in_term : env -> evar_map -> constr -> constr

(** [evar_define choose env ev c] try to instantiate [ev] with [c] (typed in [env]),
   possibly solving related unification problems, possibly leaving open
   some problems that cannot be solved in a unique way (except if choose is
   true); fails if the instance is not valid for the given [ev] *)

type conv_fun =
  env ->  evar_map -> conv_pb -> constr -> constr -> unification_result

type conv_fun_bool =
  env ->  evar_map -> conv_pb -> constr -> constr -> bool

val evar_define : conv_fun -> ?choose:bool -> env -> evar_map -> 
  bool option -> existential -> constr -> evar_map

val refresh_universes :
  ?status:Evd.rigid ->
  ?onlyalg:bool (* Only algebraic universes *) ->
  ?refreshset:bool ->
  (* Also refresh Prop and Set universes, so that the returned type can be any supertype
     of the original type *)
  bool option (* direction: true for levels lower than the existing levels *) ->
  env -> evar_map -> types -> evar_map * types

val solve_refl : ?can_drop:bool -> conv_fun_bool -> env ->  evar_map ->
  bool option -> Evar.t -> constr array -> constr array -> evar_map

val solve_evar_evar : ?force:bool ->
  (env -> evar_map -> bool option -> existential -> constr -> evar_map) ->
  conv_fun ->
  env ->  evar_map -> bool option -> existential -> existential -> evar_map

val solve_simple_eqn : conv_fun -> ?choose:bool -> env ->  evar_map ->
  bool option * existential * constr -> unification_result

val reconsider_unif_constraints : conv_fun -> evar_map -> unification_result

val reconsider_conv_pbs : conv_fun -> evar_map -> unification_result
[@@ocaml.deprecated "Alias for [reconsider_unif_constraints]"]

val is_unification_pattern_evar : env -> evar_map -> existential -> constr list ->
  constr -> alias list option

val is_unification_pattern : env * int -> evar_map -> constr -> constr list ->
  constr -> alias list option

val solve_pattern_eqn : env -> evar_map -> alias list -> constr -> constr

val noccur_evar : env -> evar_map -> Evar.t -> constr -> bool

exception IllTypedInstance of env * types * types

(* May raise IllTypedInstance if types are not convertible *)
val check_evar_instance :
  evar_map -> Evar.t -> constr -> conv_fun -> evar_map

val remove_instance_local_defs :
  evar_map -> Evar.t -> 'a array -> 'a list

val get_type_of_refresh : 
  ?polyprop:bool -> ?lax:bool -> env -> evar_map -> constr -> evar_map * types
