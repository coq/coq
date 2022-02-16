(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Coercionops

(** Classes and coercions. *)

(** [try_add_new_coercion_with_target ref s src tg] declares [ref] as a coercion
   from [src] to [tg] *)
val try_add_new_coercion_with_target
  :  GlobRef.t
  -> local:bool
  -> poly:bool
  -> nonuniform:bool
  -> reversible:bool
  -> source:cl_typ
  -> target:cl_typ
  -> unit

(** [try_add_new_coercion ref s] declares [ref], assumed to be of type
   [(x1:T1)...(xn:Tn)src->tg], as a coercion from [src] to [tg] *)
val try_add_new_coercion : GlobRef.t -> local:bool -> poly:bool ->
  nonuniform:bool ->
  reversible:bool -> unit

(** [try_add_new_coercion_subclass cst s] expects that [cst] denotes a
   transparent constant which unfolds to some class [tg]; it declares
   an identity coercion from [cst] to [tg], named something like
   ["Id_cst_tg"] *)
val try_add_new_coercion_subclass : cl_typ -> local:bool -> poly:bool ->
  nonuniform:bool ->
  reversible:bool -> unit

(** [try_add_new_coercion_with_source ref s src] declares [ref] as a coercion
   from [src] to [tg] where the target is inferred from the type of [ref] *)
val try_add_new_coercion_with_source : GlobRef.t -> local:bool ->
  poly:bool -> nonuniform:bool -> reversible:bool -> source:cl_typ -> unit

(** [try_add_new_identity_coercion id s src tg] enriches the
   environment with a new definition of name [id] declared as an
   identity coercion from [src] to [tg] *)
val try_add_new_identity_coercion
  :  Id.t
  -> local:bool
  -> poly:bool -> source:cl_typ -> target:cl_typ -> unit

val add_coercion_hook : poly:bool -> nonuniform:bool -> reversible:bool -> Declare.Hook.t

val add_subclass_hook : poly:bool -> reversible:bool -> Declare.Hook.t

val class_of_global : GlobRef.t -> cl_typ

(** Attribute to silence warning for coercions that don't satisfy
   the uniform inheritance condition. *)
val nonuniform : bool option Attributes.attribute

val change_reverse : GlobRef.t -> reversible:bool -> unit
