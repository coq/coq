(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Mod_subst
open Genarg

type glob_sign = {
  ltacvars : Id.Set.t;
  genv : Environ.env }

(** {5 Internalization functions} *)

type ('raw, 'glb) intern_fun = glob_sign -> 'raw -> glob_sign * 'glb
(** The type of functions used for internalizing generic arguments. *)

val intern : ('raw, 'glb, 'top) genarg_type -> ('raw, 'glb) intern_fun

val generic_intern : (raw_generic_argument, glob_generic_argument) intern_fun

(** {5 Substitution functions} *)

type 'glb subst_fun = substitution -> 'glb -> 'glb
(** The type of functions used for substituting generic arguments. *)

val substitute : ('raw, 'glb, 'top) genarg_type -> 'glb subst_fun

val generic_substitute : glob_generic_argument subst_fun

(** {5 Notation functions} *)

type 'glb ntn_subst_fun = Tactypes.glob_constr_and_expr Id.Map.t -> 'glb -> 'glb

val substitute_notation : ('raw, 'glb, 'top) genarg_type -> 'glb ntn_subst_fun

val generic_substitute_notation : glob_generic_argument ntn_subst_fun

(** Registering functions *)

val register_intern0 : ('raw, 'glb, 'top) genarg_type ->
  ('raw, 'glb) intern_fun -> unit

val register_subst0 : ('raw, 'glb, 'top) genarg_type ->
  'glb subst_fun -> unit

val register_ntn_subst0 : ('raw, 'glb, 'top) genarg_type ->
  'glb ntn_subst_fun -> unit
