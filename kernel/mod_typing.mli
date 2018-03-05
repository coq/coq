(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Declarations
open Environ
open Entries
open Mod_subst
open Names

(** Main functions for translating module entries *)

(** [translate_module] produces a [module_body] out of a [module_entry].
    In the output fields:
    - [mod_expr] is [Abstract] for a [MType] entry, or [Algebraic] for [MExpr].
    - [mod_type_alg] is [None] only for a [MExpr] without explicit signature.
*)

val translate_module :
  env -> ModPath.t -> inline -> module_entry -> module_body

(** [translate_modtype] produces a [module_type_body] whose [mod_type_alg]
    cannot be [None] (and of course [mod_expr] is [Abstract]). *)

val translate_modtype :
  env -> ModPath.t -> inline -> module_type_entry -> module_type_body

(** Low-level function for translating a module struct entry :
    - We translate to a module when a [ModPath.t] is given,
      otherwise to a module type.
    - The first output is the expanded signature
    - The second output is the algebraic expression, kept mostly for
      the extraction. *)

type 'alg translation =
  module_signature * 'alg * delta_resolver * Univ.ContextSet.t

val translate_mse :
  env -> ModPath.t option -> inline -> module_struct_entry ->
    module_alg_expr translation

(** From an already-translated (or interactive) implementation and
    an (optional) signature entry, produces a final [module_body] *)

val finalize_module :
  env -> ModPath.t -> (module_expression option) translation ->
  (module_type_entry * inline) option ->
  module_body

(** [translate_mse_incl] translate the mse of a module or
    module type given to an Include *)

val translate_mse_incl :
  bool -> env -> ModPath.t -> inline -> module_struct_entry ->
    unit translation
