(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Libnames
open Globnames
open Term
open Util

(** This module collects the global references, constructions and
    patterns of the standard library used in ocaml files *)

(** The idea is to migrate to rebindable name-based approach, thus the
    only function this FILE will provide will be:

    [get_ref : string -> global_reference]

    such that [find_reference "core.eq.type"]
    returns the proper [global_reference]

    [bind_ref : string -> global_reference -> unit]

    will bind a reference.

    A feature based approach would be possible too.

    Contrary to the old approach of raising an anomaly, we expect
    tactics to gracefully fail in the absence of some primitive.

    This is work in progress, see below.
*)

val get_ref    : string -> global_reference
val get_constr : string -> constr

(** Non-lazy, fixed equalities *)
val glob_eq       : global_reference
val glob_identity : global_reference
val glob_jmeq     : global_reference

(** The rest below is ready to go... *)

(** {6 ... } *)
(** [find_reference caller_message [dir;subdir;...] s] returns a global
   reference to the name dir.subdir.(...).s; the corresponding module
   must have been required or in the process of being compiled so that
   it must be used lazyly; it raises an anomaly with the given message
   if not found *)

type message = string

val find_reference : message -> string list -> string -> global_reference

(** This just prefixes find_reference with Coq... *)
val coq_reference  : message -> string list -> string -> global_reference

(** For tactics/commands requiring vernacular libraries *)
val check_required_library : string list -> unit

(** Used in omega/ring: They must query their particular theory XXX PORT to omega.xxx.xxx*)
val arith_modules       : string list list
val zarith_base_modules : string list list
val init_modules        : string list list

(** Search in several modules (not prefixed by "Coq") *)
val gen_constant_in_modules  : string -> string list list -> string -> constr
val gen_reference_in_modules : string -> string list list -> string -> global_reference

(** {6 Global references } *)

(** Modules *)
val prelude_module    : DirPath.t

val logic_module      : DirPath.t
val logic_module_name : string list
val logic_type_module : DirPath.t

val jmeq_module      : DirPath.t
val jmeq_module_name : string list

val datatypes_module_name : string list

(** Natural numbers *)
val nat_path  : full_path
val glob_nat  : global_reference
val path_of_O : constructor
val path_of_S : constructor
val glob_O    : global_reference
val glob_S    : global_reference

(** {6 ... } *)
(** Constructions and patterns related to Coq initial state are unknown
   at compile time.
  *)

(** {6 For Equality tactics } *)
type coq_sigma_data = {
  proj1 : global_reference;
  proj2 : global_reference;
  elim  : global_reference;
  intro : global_reference;
  typ   : global_reference }

val build_prod       : coq_sigma_data delayed
val build_sigma_type : coq_sigma_data delayed
val build_sigma      : coq_sigma_data delayed

type coq_eq_data = {
  eq   : global_reference;
  ind  : global_reference;
  refl : global_reference;
  sym  : global_reference;
  trans: global_reference;
  congr: global_reference }

val build_coq_eq_data       : coq_eq_data delayed
val build_coq_identity_data : coq_eq_data delayed
val build_coq_jmeq_data     : coq_eq_data delayed

(** Data needed for discriminate and injection *)

type coq_inversion_data = {
  inv_eq   : global_reference; (** : forall params, args -> Prop *)
  inv_ind  : global_reference; (** : forall params P (H : P params) args, eq params args 
			 ->  P args *)
  inv_congr: global_reference  (** : forall params B (f:t->B) args, eq params args -> 
			 f params = f args *)
}

val build_coq_inversion_eq_data       : coq_inversion_data delayed
val build_coq_inversion_identity_data : coq_inversion_data delayed
val build_coq_inversion_jmeq_data     : coq_inversion_data delayed
