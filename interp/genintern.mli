(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Genarg

module Store : Store.S

type intern_variable_status = {
  intern_ids : Id.Set.t;
  notation_variable_status :
    (bool ref * Notation_term.subscopes option ref * Notation_term.notation_var_binders option ref *
       Notation_term.notation_var_internalization_type)
      Id.Map.t
}

type glob_sign = {
  ltacvars : Id.Set.t;
  genv : Environ.env;
  extra : Store.t;
  intern_sign : intern_variable_status;
  strict_check : bool;
}

val empty_glob_sign : strict:bool -> Environ.env -> glob_sign

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

(** {5 Internalization in tactic patterns} *)

type ('raw,'glb) intern_pat_fun = ?loc:Loc.t -> ('raw,'glb) intern_fun

val intern_pat : ('raw, 'glb, 'top) genarg_type -> ('raw, 'glb) intern_pat_fun

val generic_intern_pat : (raw_generic_argument, glob_generic_argument) intern_pat_fun

(** {5 Notation functions} *)

type 'glb ntn_subst_fun = Id.Set.t -> Glob_term.glob_constr Id.Map.t -> 'glb -> 'glb

val substitute_notation : ('raw, 'glb, 'top) genarg_type -> 'glb ntn_subst_fun

val generic_substitute_notation : glob_generic_argument ntn_subst_fun

(** Registering functions *)

val register_intern0 : ('raw, 'glb, 'top) genarg_type ->
  ('raw, 'glb) intern_fun -> unit

val register_intern_pat : ('raw, 'glb, 'top) genarg_type ->
  ('raw, 'glb) intern_pat_fun -> unit


val register_ntn_subst0 : ('raw, 'glb, 'top) genarg_type ->
  'glb ntn_subst_fun -> unit
