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
open Mod_subst
open Genarg

module Store : Store.S

type glob_sign = {
  ltacvars : Id.Set.t;
  genv : Environ.env;
  extra : Store.t;
}

val empty_glob_sign : Environ.env -> glob_sign

(** In globalize tactics, we need to keep the initial [constr_expr] to recompute
   in the environment by the effective calls to Intro, Inversion, etc
   The [constr_expr] field is [None] in TacDef though *)
type glob_constr_and_expr = Glob_term.glob_constr * Constrexpr.constr_expr option
type glob_constr_pattern_and_expr = Id.Set.t * glob_constr_and_expr * Pattern.constr_pattern

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

type 'glb ntn_subst_fun = glob_constr_and_expr Id.Map.t -> 'glb -> 'glb

val substitute_notation : ('raw, 'glb, 'top) genarg_type -> 'glb ntn_subst_fun

val generic_substitute_notation : glob_generic_argument ntn_subst_fun

(** Registering functions *)

val register_intern0 : ('raw, 'glb, 'top) genarg_type ->
  ('raw, 'glb) intern_fun -> unit

val register_subst0 : ('raw, 'glb, 'top) genarg_type ->
  'glb subst_fun -> unit

val register_ntn_subst0 : ('raw, 'glb, 'top) genarg_type ->
  'glb ntn_subst_fun -> unit
