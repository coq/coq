(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(*i*)
open Names
open Libnames
open Nametab
open Term
open Pattern
(*i*)

(*s This module collects the global references, constructions and
    patterns of the standard library used in ocaml files *)

(*s [find_reference caller_message [dir;subdir;...] s] returns a global
   reference to the name dir.subdir.(...).s; the corresponding module
   must have been required or in the process of being compiled so that
   it must be used lazyly; it raises an anomaly with the given message
   if not found *)

type message = string

val find_reference : message -> string list -> string -> global_reference

(* [coq_reference caller_message [dir;subdir;...] s] returns a
   global reference to the name Coq.dir.subdir.(...).s *)

val coq_reference : message -> string list -> string -> global_reference

(* idem but return a term *)

val coq_constant : message -> string list -> string -> constr

(* Synonyms of [coq_constant] and [coq_reference] *)

val gen_constant : message -> string list -> string -> constr
val gen_reference :  message -> string list -> string -> global_reference

(* Search in several modules (not prefixed by "Coq") *)
val gen_constant_in_modules : string->string list list-> string -> constr
val arith_modules : string list list
val zarith_base_modules : string list list
val init_modules : string list list

(* For tactics/commands requiring vernacular libraries *)
val check_required_library : string list -> unit

(*s Global references *)

(* Modules *)
val logic_module : dir_path
val logic_type_module : dir_path

(* Natural numbers *)
val nat_path : section_path
val glob_nat : global_reference
val path_of_O : constructor
val path_of_S : constructor
val glob_O : global_reference
val glob_S : global_reference

(* Booleans *)
val glob_bool : global_reference
val path_of_true : constructor
val path_of_false : constructor
val glob_true : global_reference
val glob_false : global_reference


(* Equality *)
val glob_eq : global_reference
val glob_identity : global_reference
val glob_jmeq : global_reference

(*s Constructions and patterns related to Coq initial state are unknown
   at compile time. Therefore, we can only provide methods to build
   them at runtime. This is the purpose of the [constr delayed] and
   [constr_pattern delayed] types. Objects of this time needs to be
   applied to [()] to get the actual constr or pattern at runtime *)

type 'a delayed = unit -> 'a

type coq_bool_data = {
  andb : constr;
  andb_prop : constr;
  andb_true_intro : constr}
val build_bool_type : coq_bool_data delayed

(*s For Equality tactics *)
type coq_sigma_data = {
  proj1 : constr;
  proj2 : constr;
  elim  : constr;
  intro : constr;
  typ   : constr }

val build_sigma_set : coq_sigma_data delayed
val build_sigma_type : coq_sigma_data delayed
(* Non-dependent pairs in Set from Datatypes *)
val build_prod : coq_sigma_data delayed

type coq_eq_data = {
  eq   : constr;
  ind  : constr;
  refl : constr;
  sym  : constr;
  trans: constr;
  congr: constr }

val build_coq_eq_data : coq_eq_data delayed
val build_coq_identity_data : coq_eq_data delayed
val build_coq_jmeq_data : coq_eq_data delayed

val build_coq_eq       : constr delayed (* = [(build_coq_eq_data()).eq] *)
val build_coq_eq_sym   : constr delayed (* = [(build_coq_eq_data()).sym] *)
val build_coq_f_equal2 : constr delayed


(* Specif *)
val build_coq_sumbool : constr delayed

(*s Connectives *)
(* The False proposition *)
val build_coq_False : constr delayed

(* The True proposition and its unique proof *)
val build_coq_True : constr delayed
val build_coq_I : constr delayed

(* Negation *)
val build_coq_not : constr delayed

(* Conjunction *)
val build_coq_and : constr delayed
val build_coq_conj : constr delayed
val build_coq_iff : constr delayed

val build_coq_iff_left_proj : constr delayed
val build_coq_iff_right_proj : constr delayed

(* Disjunction *)
val build_coq_or : constr delayed

(* Existential quantifier *)
val build_coq_ex : constr delayed

val coq_eq_ref : global_reference lazy_t
val coq_identity_ref : global_reference lazy_t
val coq_jmeq_ref : global_reference lazy_t
val coq_existS_ref : global_reference lazy_t
val coq_existT_ref : global_reference lazy_t
val coq_not_ref : global_reference lazy_t
val coq_False_ref : global_reference lazy_t
val coq_sumbool_ref : global_reference lazy_t
val coq_sig_ref : global_reference lazy_t

val coq_or_ref : global_reference lazy_t
val coq_iff_ref : global_reference lazy_t
