(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Classops
open Globnames

(** Classes and coercions. *)

(** [try_add_new_coercion_with_target ref s src tg] declares [ref] as a coercion
   from [src] to [tg] *)
val try_add_new_coercion_with_target : global_reference -> local:bool -> 
  Decl_kinds.polymorphic ->
  source:cl_typ -> target:cl_typ ->  unit

(** [try_add_new_coercion ref s] declares [ref], assumed to be of type
   [(x1:T1)...(xn:Tn)src->tg], as a coercion from [src] to [tg] *)
val try_add_new_coercion : global_reference -> local:bool -> 
  Decl_kinds.polymorphic -> unit

(** [try_add_new_coercion_subclass cst s] expects that [cst] denotes a
   transparent constant which unfolds to some class [tg]; it declares
   an identity coercion from [cst] to [tg], named something like
   ["Id_cst_tg"] *)
val try_add_new_coercion_subclass : cl_typ -> local:bool -> 
  Decl_kinds.polymorphic -> unit

(** [try_add_new_coercion_with_source ref s src] declares [ref] as a coercion
   from [src] to [tg] where the target is inferred from the type of [ref] *)
val try_add_new_coercion_with_source : global_reference -> local:bool -> 
  Decl_kinds.polymorphic -> source:cl_typ -> unit

(** [try_add_new_identity_coercion id s src tg] enriches the
   environment with a new definition of name [id] declared as an
   identity coercion from [src] to [tg] *)
val try_add_new_identity_coercion : Id.t -> local:bool -> 
  Decl_kinds.polymorphic -> source:cl_typ -> target:cl_typ -> unit

val add_coercion_hook : Decl_kinds.polymorphic -> unit Lemmas.declaration_hook

val add_subclass_hook : Decl_kinds.polymorphic -> unit Lemmas.declaration_hook

val class_of_global : global_reference -> cl_typ
