(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Util
open Names
open EConstr
open Misctypes
open Genarg
open Geninterp

(** Coercions from highest level generic arguments to actual data used by Ltac
    interpretation. Those functions examinate dynamic types and try to return
    something sensible according to the object content. *)

exception CannotCoerceTo of string
(** Exception raised whenever a coercion failed. *)

(** {5 High-level access to values}

  The [of_*] functions cast a given argument into a value. The [to_*] do the
  converse, and return [None] if there is a type mismatch.

*)

module Value :
sig
  type t = Val.t

  val of_constr : constr -> t
  val to_constr : t -> constr option
  val of_uconstr : Ltac_pretype.closed_glob_constr -> t
  val to_uconstr : t -> Ltac_pretype.closed_glob_constr option
  val of_int : int -> t
  val to_int : t -> int option
  val to_list : t -> t list option
  val to_option : t -> t option option
  val to_pair : t -> (t * t) option
end

(** {5 Coercion functions} *)

val coerce_to_constr_context : Value.t -> constr

val coerce_var_to_ident : bool -> Environ.env -> Evd.evar_map -> Value.t -> Id.t

val coerce_to_ident_not_fresh : Environ.env -> Evd.evar_map -> Value.t -> Id.t

val coerce_to_intro_pattern : Environ.env -> Evd.evar_map -> Value.t -> Tacexpr.delayed_open_constr intro_pattern_expr

val coerce_to_intro_pattern_naming :
  Environ.env -> Evd.evar_map -> Value.t -> intro_pattern_naming_expr

val coerce_to_hint_base : Value.t -> string

val coerce_to_int : Value.t -> int

val coerce_to_constr : Environ.env -> Value.t -> Ltac_pretype.constr_under_binders

val coerce_to_uconstr : Environ.env -> Value.t -> Ltac_pretype.closed_glob_constr

val coerce_to_closed_constr : Environ.env -> Value.t -> constr

val coerce_to_evaluable_ref :
  Environ.env -> Evd.evar_map -> Value.t -> evaluable_global_reference

val coerce_to_constr_list : Environ.env -> Value.t -> constr list

val coerce_to_intro_pattern_list :
  ?loc:Loc.t -> Environ.env -> Evd.evar_map -> Value.t -> Tacexpr.intro_patterns

val coerce_to_hyp : Environ.env -> Evd.evar_map -> Value.t -> Id.t

val coerce_to_hyp_list : Environ.env -> Evd.evar_map -> Value.t -> Id.t list

val coerce_to_reference : Environ.env -> Evd.evar_map -> Value.t -> global_reference

val coerce_to_quantified_hypothesis : Evd.evar_map -> Value.t -> quantified_hypothesis

val coerce_to_decl_or_quant_hyp : Environ.env -> Evd.evar_map -> Value.t -> quantified_hypothesis

val coerce_to_int_or_var_list : Value.t -> int or_var list

(** {5 Missing generic arguments} *)

val wit_constr_context : (Empty.t, Empty.t, EConstr.constr) genarg_type

val wit_constr_under_binders : (Empty.t, Empty.t, Ltac_pretype.constr_under_binders) genarg_type
