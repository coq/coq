(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

(*i*)
open Names
open Libnames
open Nametab
open Term
open Pattern
(*i*)

(*s This module collects the global references, constructions and
    patterns of the standard library used in ocaml files *)

(*s Some utilities, the first argument is used for error messages.
    Must be used lazyly. s*)

val gen_reference : string->string list -> string -> global_reference
val gen_constant : string->string list -> string -> constr

(* Search in several modules (not prefixed by "Coq") *)
val gen_constant_in_modules : string->string list list-> string -> constr
val arith_modules : string list list
val zarith_base_modules : string list list
val init_modules : string list list

(*s Global references *)

(* Modules *)
val logic_module : dir_path
val logic_type_module : dir_path

(* Natural numbers *)
val glob_nat : global_reference
val path_of_O : constructor
val path_of_S : constructor
val glob_O : global_reference
val glob_S : global_reference

(* Equality *)
val glob_eq : global_reference
val glob_eqT : global_reference

(*s Constructions and patterns related to Coq initial state are unknown
   at compile time. Therefore, we can only provide methods to build
   them at runtime. This is the purpose of the [constr delayed] and
   [constr_pattern delayed] types. Objects of this time needs to be
   applied to [()] to get the actual constr or pattern at runtime *)

type 'a delayed = unit -> 'a

(*s For Equality tactics *)
type coq_sigma_data = {
  proj1 : constr;
  proj2 : constr;
  elim  : constr;
  intro : constr;
  typ   : constr }

val build_sigma_set : coq_sigma_data delayed
val build_sigma_type : coq_sigma_data delayed

type coq_leibniz_eq_data = {
  eq   : constr;
  refl : constr;
  ind  : constr;
  rrec : constr option;
  rect : constr option;
  congr: constr;
  sym  : constr }

val build_coq_eq_data : coq_leibniz_eq_data delayed
val build_coq_eqT_data : coq_leibniz_eq_data delayed
val build_coq_idT_data : coq_leibniz_eq_data delayed

val build_coq_eq : constr delayed (* = [(build_coq_eq_data()).eq] *)
val build_coq_f_equal2 : constr delayed
val build_coq_eqT : constr delayed
val build_coq_sym_eqT : constr delayed

(* Empty Type *)
val build_coq_EmptyT : constr delayed

(* Unit Type and its unique inhabitant *)
val build_coq_UnitT : constr delayed
val build_coq_IT : constr delayed

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

(* Disjunction *)
val build_coq_or : constr delayed

(* Existential quantifier *)
val build_coq_ex : constr delayed

val coq_eq_ref : global_reference lazy_t
val coq_eqT_ref : global_reference lazy_t
val coq_idT_ref : global_reference lazy_t
val coq_existS_ref : global_reference lazy_t
val coq_existT_ref : global_reference lazy_t
val coq_not_ref : global_reference lazy_t
val coq_False_ref : global_reference lazy_t
val coq_sumbool_ref : global_reference lazy_t
val coq_sig_ref : global_reference lazy_t
