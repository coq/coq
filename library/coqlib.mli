(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
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

exception NotFoundRef of string

(** Retrieves the reference bound to the given name (by a previous call to {!register_ref}).
    Raises [NotFoundRef] if no reference is bound to this name. *)
val lib_ref : string -> GlobRef.t

(** As [lib_ref] but returns [None] instead of raising. *)
val lib_ref_opt : string -> GlobRef.t option

(** Checks whether a name refers to a registered constant.
    For any name [n], if [has_ref n] returns [true], [lib_ref n] will succeed. *)
val has_ref : string -> bool

(** Checks whether a name is bound to a known reference. *)
val check_ref : string -> GlobRef.t -> bool

(** Checks whether a name is bound to a known inductive. *)
val check_ind_ref : string -> inductive -> bool [@@ocaml.deprecated "Use Coqlib.check_ref"]

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

val build_sigma_type : coq_sigma_data delayed
val build_sigma : coq_sigma_data delayed
val build_prod : coq_sigma_data delayed

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

(** This just prefixes find_reference with Stdlib... *)
val coq_reference  : string -> string list -> string -> GlobRef.t
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]

(** Search in several modules (not prefixed by "Stdlib") *)
val gen_reference_in_modules : string->string list list-> string -> GlobRef.t
[@@ocaml.deprecated "Please use Coqlib.lib_ref"]
