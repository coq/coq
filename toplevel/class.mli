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
open Term
open Classops
open Declare
open Libnames
open Decl_kinds
open Nametab
(*i*)

(* Classes and coercions. *)

(* [try_add_new_coercion_with_target ref s src tg] declares [ref] as a coercion
   from [src] to [tg] *)
val try_add_new_coercion_with_target : global_reference -> strength -> 
  source:cl_typ -> target:cl_typ ->  unit

(* [try_add_new_coercion ref s] declares [ref], assumed to be of type
   [(x1:T1)...(xn:Tn)src->tg], as a coercion from [src] to [tg] *)
val try_add_new_coercion : global_reference -> strength -> unit

(* [try_add_new_coercion_subclass cst s] expects that [cst] denotes a
   transparent constant which unfolds to some class [tg]; it declares
   an identity coercion from [cst] to [tg], named something like
   ["Id_cst_tg"] *)
val try_add_new_coercion_subclass : cl_typ -> strength -> unit

(* [try_add_new_coercion_with_source ref s src] declares [ref] as a coercion
   from [src] to [tg] where the target is inferred from the type of [ref] *)
val try_add_new_coercion_with_source : global_reference -> strength ->
  source:cl_typ -> unit

(* [try_add_new_identity_coercion id s src tg] enriches the
   environment with a new definition of name [id] declared as an
   identity coercion from [src] to [tg] *)
val try_add_new_identity_coercion : identifier -> strength ->
  source:cl_typ -> target:cl_typ -> unit

val add_coercion_hook : Tacexpr.declaration_hook

val add_subclass_hook : Tacexpr.declaration_hook

(* [try_add_new_class ref] declares [ref] as a new class; usually,
   this is done implicitely by [try_add_new_coercion]'s functions *)
val try_add_new_class : global_reference -> strength -> unit

(*s This is used for the discharge *)
type coercion_entry

val add_new_coercion : coercion_entry -> unit

val process_class :
  dir_path -> identifier list -> 
    (cl_typ * cl_info_typ) -> (cl_typ * cl_info_typ)
val process_coercion :
  dir_path -> identifier list -> coercion -> coercion_entry

val class_of_ref : global_reference -> cl_typ
