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

(** [check_subtypes state env mp_sub mp_super super] checks that the module
    at [mp_sub] has a type which is a subtype of [super] (expected to live
    at [mp_super]).

    [direct] may be set when the fields of the module at [mp_sub] are part
    of [env], unsubstituted — e.g. the current interactive module, a module
    already added to the environment, or a module about to be closed. The
    fields are then looked up in the environment on demand instead of
    walking (and strengthening) the whole signature eagerly, which makes the
    check proportional to the size of [super] instead of the size of the
    subtype's signature. *)
val check_subtypes : ?direct:bool -> ('a, Conversion.graph_inconsistency) Conversion.universe_state -> env -> ModPath.t -> ModPath.t -> module_type_body -> 'a

val check_polymorphic_universes :
  Environ.env ->
  UVars.AbstractContext.t -> UVars.AbstractContext.t ->
  bool
