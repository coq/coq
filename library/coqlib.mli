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
open Libnames
open Globnames
open Util

(** This module collects the global references, constructions and
    patterns of the standard library used in ocaml files *)

(** The idea is to migrate to rebindable name-based approach, thus the
    only function this FILE will provide will be:

    [find_reference : string -> global_reference]

    such that [find_reference "core.eq.type"] returns the proper [global_reference]

    [bind_reference : string -> global_reference -> unit]

    will bind a reference.

    A feature based approach would be possible too.

    Contrary to the old approach of raising an anomaly, we expect
    tactics to gracefully fail in the absence of some primitive.

    This is work in progress, see below.
*)

(** {6 ... } *)
(** [find_reference caller_message [dir;subdir;...] s] returns a global
   reference to the name dir.subdir.(...).s; the corresponding module
   must have been required or in the process of being compiled so that
   it must be used lazily; it raises an anomaly with the given message
   if not found *)

type message = string

val find_reference : message -> string list -> string -> global_reference
val coq_reference : message -> string list -> string -> global_reference

(** For tactics/commands requiring vernacular libraries *)
val check_required_library : string list -> unit

(** Search in several modules (not prefixed by "Coq") *)
val gen_reference_in_modules : string->string list list-> string -> global_reference

val arith_modules : string list list
val zarith_base_modules : string list list
val init_modules : string list list

(** {6 Global references } *)

(** Modules *)
val prelude_module : DirPath.t

val logic_module : DirPath.t
val logic_module_name : string list

val logic_type_module : DirPath.t

val jmeq_module : DirPath.t
val jmeq_module_name : string list

val datatypes_module_name : string list

(** Identity  *)
val id : Constant.t
val type_of_id : Constant.t

(** Natural numbers *)
val nat_path : full_path
val glob_nat : global_reference
val path_of_O : constructor
val path_of_S : constructor
val glob_O : global_reference
val glob_S : global_reference

(** Booleans *)
val glob_bool : global_reference
val path_of_true : constructor
val path_of_false : constructor
val glob_true : global_reference
val glob_false : global_reference


(** Equality *)
val glob_eq : global_reference
val glob_identity : global_reference
val glob_jmeq : global_reference

(** {6 ... } *)
(** Constructions and patterns related to Coq initial state are unknown
   at compile time. Therefore, we can only provide methods to build
   them at runtime. This is the purpose of the [constr delayed] and
   [constr_pattern delayed] types. Objects of this time needs to be
   forced with [delayed_force] to get the actual constr or pattern 
   at runtime. *)

type coq_bool_data = {
  andb : global_reference;
  andb_prop : global_reference;
  andb_true_intro : global_reference}
val build_bool_type : coq_bool_data delayed

(** {6 For Equality tactics } *)
type coq_sigma_data = {
  proj1 : global_reference;
  proj2 : global_reference;
  elim  : global_reference;
  intro : global_reference;
  typ   : global_reference }

val build_sigma_set : coq_sigma_data delayed
val build_sigma_type : coq_sigma_data delayed
val build_sigma : coq_sigma_data delayed

(* val build_sigma_type_in : Environ.env -> coq_sigma_data Univ.in_universe_context_set *)
(* val build_sigma_in : Environ.env -> coq_sigma_data Univ.in_universe_context_set *)
(* val build_prod_in : Environ.env -> coq_sigma_data Univ.in_universe_context_set *)
(* val build_coq_eq_data_in : Environ.env -> coq_eq_data Univ.in_universe_context_set *)

(** Non-dependent pairs in Set from Datatypes *)
val build_prod : coq_sigma_data delayed

type coq_eq_data = {
  eq   : global_reference;
  ind  : global_reference;
  refl : global_reference;
  sym  : global_reference;
  trans: global_reference;
  congr: global_reference }

val build_coq_eq_data : coq_eq_data delayed

val build_coq_identity_data : coq_eq_data delayed
val build_coq_jmeq_data : coq_eq_data delayed

val build_coq_eq       : global_reference delayed (** = [(build_coq_eq_data()).eq] *)
val build_coq_eq_refl  : global_reference delayed (** = [(build_coq_eq_data()).refl] *)
val build_coq_eq_sym   : global_reference delayed (** = [(build_coq_eq_data()).sym] *)
val build_coq_f_equal2 : global_reference delayed

(** Data needed for discriminate and injection *)

type coq_inversion_data = {
  inv_eq   : global_reference; (** : forall params, args -> Prop *)
  inv_ind  : global_reference; (** : forall params P (H : P params) args, eq params args 
			 ->  P args *)
  inv_congr: global_reference  (** : forall params B (f:t->B) args, eq params args -> 
			 f params = f args *)
}

val build_coq_inversion_eq_data : coq_inversion_data delayed
val build_coq_inversion_identity_data : coq_inversion_data delayed
val build_coq_inversion_jmeq_data : coq_inversion_data delayed
val build_coq_inversion_eq_true_data : coq_inversion_data delayed

(** Specif *)
val build_coq_sumbool : global_reference delayed

(** {6 ... } *)
(** Connectives 
   The False proposition *)
val build_coq_False : global_reference delayed

(** The True proposition and its unique proof *)
val build_coq_True : global_reference delayed
val build_coq_I : global_reference delayed

(** Negation *)
val build_coq_not : global_reference delayed

(** Conjunction *)
val build_coq_and : global_reference delayed
val build_coq_conj : global_reference delayed
val build_coq_iff : global_reference delayed

val build_coq_iff_left_proj : global_reference delayed
val build_coq_iff_right_proj : global_reference delayed

(** Disjunction *)
val build_coq_or : global_reference delayed

(** Existential quantifier *)
val build_coq_ex : global_reference delayed

val coq_eq_ref : global_reference lazy_t
val coq_identity_ref : global_reference lazy_t
val coq_jmeq_ref : global_reference lazy_t
val coq_eq_true_ref : global_reference lazy_t
val coq_existS_ref : global_reference lazy_t
val coq_existT_ref : global_reference lazy_t
val coq_exist_ref : global_reference lazy_t
val coq_not_ref : global_reference lazy_t
val coq_False_ref : global_reference lazy_t
val coq_sumbool_ref : global_reference lazy_t
val coq_sig_ref : global_reference lazy_t

val coq_or_ref : global_reference lazy_t
val coq_iff_ref : global_reference lazy_t
