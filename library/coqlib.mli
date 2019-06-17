(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open Names

(** Indirection between logical names and global references.

    This module provides a mechanism to bind “names” to constants and to look up
    these constants using their names.

    The two main functions are [register_ref n r] which binds the name [n] to
    the reference [r] and [lib_ref n] which returns the previously registered
    reference under name [n].

    The first function is meant to be available through the vernacular command
    [Register r as n], so that plug-ins can refer to a constant without knowing
    its user-facing name, the precise module path in which it is defined, etc.

    For instance, [lib_ref "core.eq.type"] returns the proper [GlobRef.t] for
    the type of the core equality type.
*)

(** Registers a global reference under the given name. *)
val register_ref : string -> GlobRef.t -> unit

(** Retrieves the reference bound to the given name (by a previous call to {!register_ref}).
    Raises an error if no reference is bound to this name. *)
val lib_ref : string -> GlobRef.t

(** Checks whether a name refers to a registered constant.
    For any name [n], if [has_ref n] returns [true], [lib_ref n] will succeed. *)
val has_ref : string -> bool

(** Checks whether a name is bound to a known inductive. *)
val check_ind_ref : string -> inductive -> bool

(** List of all currently bound names. *)
val get_lib_refs : unit -> (string * GlobRef.t) list

(* Exceptions to deprecation *)

(** {2 For Equality tactics} *)

type coq_sigma_data = {
  proj1 : GlobRef.t;
  proj2 : GlobRef.t;
  elim  : GlobRef.t;
  intro : GlobRef.t;
  typ   : GlobRef.t }

val build_sigma_set : coq_sigma_data delayed
val build_sigma_type : coq_sigma_data delayed
val build_sigma : coq_sigma_data delayed

type coq_eq_data = {
  eq   : GlobRef.t;
  ind  : GlobRef.t;
  refl : GlobRef.t;
  sym  : GlobRef.t;
  trans: GlobRef.t;
  congr: GlobRef.t }

val build_coq_eq_data : coq_eq_data delayed
val build_coq_identity_data : coq_eq_data delayed
val build_coq_jmeq_data : coq_eq_data delayed

(* XXX: Some tactics special case JMeq, they should instead check for
   the constant, not the module *)
(** For tactics/commands requiring vernacular libraries *)
val check_required_library : string list -> unit

(* Used by obligations *)
val datatypes_module_name : string list

(* Used by ind_schemes *)
val logic_module_name : string list

(* Used by tactics *)
val jmeq_module_name : string list


(*************************************************************************)
(** {2 DEPRECATED}                                                            *)
(*************************************************************************)

(** All the functions below are deprecated and should go away in the
    next coq version ... *)

(** [find_reference caller_message [dir;subdir;...] s] returns a global
   reference to the name dir.subdir.(...).s; the corresponding module
   must have been required or in the process of being compiled so that
   it must be used lazily; it raises an anomaly with the given message
   if not found *)
val find_reference : string -> string list -> string -> GlobRef.t
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]

(** This just prefixes find_reference with Coq... *)
val coq_reference  : string -> string list -> string -> GlobRef.t
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]

(** Search in several modules (not prefixed by "Coq") *)
val gen_reference_in_modules : string->string list list-> string -> GlobRef.t
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]

val arith_modules : string list list
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]
val zarith_base_modules : string list list
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]
val init_modules : string list list
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]

(** {6 Global references } *)

(** Modules *)
val logic_module : ModPath.t
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]

val logic_type_module : DirPath.t
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]

(** Identity  *)
val id : Constant.t
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]
val type_of_id : Constant.t
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]

(** Natural numbers *)

val nat_path : Libnames.full_path
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]

val glob_nat : GlobRef.t
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]
val path_of_O : constructor
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]
val path_of_S : constructor
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]
val glob_O : GlobRef.t
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]
val glob_S : GlobRef.t
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]

(** Booleans *)
val glob_bool : GlobRef.t
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]

val path_of_true : constructor
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]
val path_of_false : constructor
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]
val glob_true : GlobRef.t
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]
val glob_false : GlobRef.t
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]

(** Equality *)
val glob_eq : GlobRef.t
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]
val glob_identity : GlobRef.t
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]
val glob_jmeq : GlobRef.t
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]

(** {6 ... } *)
(** Constructions and patterns related to Coq initial state are unknown
   at compile time. Therefore, we can only provide methods to build
   them at runtime. This is the purpose of the [constr delayed] and
   [constr_pattern delayed] types. Objects of this time needs to be
   forced with [delayed_force] to get the actual constr or pattern
   at runtime. *)

type coq_bool_data = {
  andb : GlobRef.t;
  andb_prop : GlobRef.t;
  andb_true_intro : GlobRef.t
}

val build_bool_type : coq_bool_data delayed
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]

(** Non-dependent pairs in Set from Datatypes *)
val build_prod : coq_sigma_data delayed
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]

val build_coq_eq       : GlobRef.t delayed
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]
(** = [(build_coq_eq_data()).eq] *)

val build_coq_eq_refl  : GlobRef.t delayed
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]
(** = [(build_coq_eq_data()).refl] *)

val build_coq_eq_sym   : GlobRef.t delayed
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]
(** = [(build_coq_eq_data()).sym] *)

val build_coq_f_equal2 : GlobRef.t delayed
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]

(** Data needed for discriminate and injection *)

type coq_inversion_data = {
  inv_eq   : GlobRef.t; (** : forall params, args -> Prop *)
  inv_ind  : GlobRef.t; (** : forall params P (H : P params) args, eq params args
			 ->  P args *)
  inv_congr: GlobRef.t  (** : forall params B (f:t->B) args, eq params args ->
			 f params = f args *)
}

val build_coq_inversion_eq_data : coq_inversion_data delayed
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]
val build_coq_inversion_identity_data : coq_inversion_data delayed
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]
val build_coq_inversion_jmeq_data : coq_inversion_data delayed
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]
val build_coq_inversion_eq_true_data : coq_inversion_data delayed
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]

(** Specif *)
val build_coq_sumbool : GlobRef.t delayed
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]

(** {6 ... }
   Connectives
   The False proposition *)
val build_coq_False : GlobRef.t delayed
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]

(** The True proposition and its unique proof *)
val build_coq_True : GlobRef.t delayed
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]
val build_coq_I : GlobRef.t delayed
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]

(** Negation *)
val build_coq_not : GlobRef.t delayed
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]

(** Conjunction *)
val build_coq_and : GlobRef.t delayed
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]
val build_coq_conj : GlobRef.t delayed
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]
val build_coq_iff : GlobRef.t delayed
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]

val build_coq_iff_left_proj : GlobRef.t delayed
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]
val build_coq_iff_right_proj : GlobRef.t delayed
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]

(** Pairs *)
val build_coq_prod : GlobRef.t delayed
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]
val build_coq_pair : GlobRef.t delayed
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]

(** Disjunction *)
val build_coq_or : GlobRef.t delayed
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]

(** Existential quantifier *)
val build_coq_ex : GlobRef.t delayed
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]

val coq_eq_ref : GlobRef.t lazy_t
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]
val coq_identity_ref : GlobRef.t lazy_t
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]
val coq_jmeq_ref : GlobRef.t lazy_t
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]
val coq_eq_true_ref : GlobRef.t lazy_t
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]
val coq_existS_ref : GlobRef.t lazy_t
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]
val coq_existT_ref : GlobRef.t lazy_t
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]
val coq_exist_ref : GlobRef.t lazy_t
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]
val coq_not_ref : GlobRef.t lazy_t
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]
val coq_False_ref : GlobRef.t lazy_t
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]
val coq_sumbool_ref : GlobRef.t lazy_t
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]
val coq_sig_ref : GlobRef.t lazy_t
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]

val coq_or_ref : GlobRef.t lazy_t
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]
val coq_iff_ref : GlobRef.t lazy_t
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]
