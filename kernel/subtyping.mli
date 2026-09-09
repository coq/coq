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
open Mod_declarations
open Environ

val check_subtypes : ('a, Conversion.graph_inconsistency) Conversion.universe_state -> env -> ModPath.t -> ModPath.t -> module_type_body -> 'a

(** Check that a declaration whose user and canonical names differ is a valid
    alias of the canonical declaration already present in the environment. *)
val check_constant_alias : env -> Constant.t -> Declarations.constant_body -> unit
val check_inductive_alias : env -> MutInd.t -> Declarations.mutual_inductive_body -> unit

val check_polymorphic_universes :
  Environ.env ->
  UVars.AbstractContext.t -> UVars.AbstractContext.t ->
  bool
