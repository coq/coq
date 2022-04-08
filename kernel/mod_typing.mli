(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
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
  'a Reduction.universe_state ->
  env -> ModPath.t -> inline -> module_entry -> module_body * 'a

(** [translate_modtype] produces a [module_type_body] whose [mod_type_alg]
    cannot be [None] (and of course [mod_expr] is [Abstract]). *)

val translate_modtype :
  'a Reduction.universe_state ->
  env -> ModPath.t -> inline -> module_type_entry -> module_type_body * 'a

(** Low-level function for translating a module struct entry :
    - We translate to a module when a [ModPath.t] is given,
      otherwise to a module type.
    - The first output is the expanded signature
    - The second output is the algebraic expression, kept mostly for
      the extraction. *)

type 'alg translation =
  module_signature * 'alg * delta_resolver * Univ.Constraints.t

val translate_mse :
  'a Reduction.universe_state ->
  env -> ModPath.t option -> inline -> module_struct_entry ->
  module_signature * (Constr.t * Univ.AbstractContext.t option) module_alg_expr * delta_resolver * 'a

(** From an already-translated (or interactive) implementation and
    an (optional) signature entry, produces a final [module_body] *)

val finalize_module :
  'a Reduction.universe_state ->
  env -> ModPath.t -> module_signature * module_expression option * delta_resolver ->
  (module_type_entry * inline) option ->
  module_body * 'a

(** [translate_mse_incl] translate the mse of a module or
    module type given to an Include *)

val translate_mse_include :
  bool -> 'a Reduction.universe_state -> Environ.env -> ModPath.t -> inline ->
  module_struct_entry -> module_signature * unit * delta_resolver * 'a
