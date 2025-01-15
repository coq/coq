(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Declarations
open Mod_declarations
open Environ
open Entries
open Mod_subst
open Names

(** Main functions for translating module entries *)

type 'a vm_handler = { vm_handler : env -> universes -> Constr.t -> 'a -> 'a * Vmlibrary.indirect_code option }
type 'a vm_state = 'a * 'a vm_handler

(** [translate_module] produces a [module_body] out of a [module_entry].
    In the output fields:
    - [mod_expr] is [Abstract] for a [MType] entry, or [Algebraic] for [MExpr].
    - [mod_type_alg] is [None] only for a [MExpr] without explicit signature.
*)

val translate_module :
  ('a, UGraph.univ_inconsistency) Conversion.universe_state ->
  'b vm_state ->
  env -> ModPath.t -> inline -> module_entry -> module_body * 'a * 'b

(** [translate_modtype] produces a [module_type_body] whose [mod_type_alg]
    cannot be [None] (and of course [mod_expr] is [Abstract]). *)

val translate_modtype :
  ('a, UGraph.univ_inconsistency) Conversion.universe_state ->
  'b vm_state ->
  env -> ModPath.t -> inline -> module_type_entry -> module_type_body * 'a * 'b

(** From an already-translated (or interactive) implementation and
    an (optional) signature entry, produces a final [module_body] *)

val finalize_module :
  ('a, UGraph.univ_inconsistency) Conversion.universe_state ->
  'b vm_state ->
  env -> ModPath.t -> module_signature * delta_resolver ->
  (module_type_entry * inline) option ->
  module_body * 'a * 'b

(** [translate_mse_incl] translate the mse of a module or
    module type given to an Include *)

val translate_mse_include :
  bool -> ('a, UGraph.univ_inconsistency) Conversion.universe_state -> 'b vm_state -> Environ.env -> ModPath.t -> inline ->
  module_struct_entry -> module_signature * unit * delta_resolver * 'a * 'b
