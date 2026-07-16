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

(** Purely functional cache of successful field subtype checks.

    Cached verdicts remain valid as long as the environment the checks
    were performed in evolves monotonically. Callers are expected to
    store the cache alongside that environment (e.g. as a field of the
    kernel's [safe_environment], or in a state summary), so that
    discarding or rolling back the environment also discards or rolls
    back the cache — the cache must not outlive the environment. *)
module Cache :
sig
  type t
  val empty : t
end

(** [check_subtypes ~cache state env mp_sub mp_super super] checks that
    the module at [mp_sub] has a type which is a subtype of [super]
    (expected to live at [mp_super]), and returns the given cache
    augmented with the field checks performed.

    [direct] may be set when the fields of the module at [mp_sub] are part
    of [env], unsubstituted — e.g. the current interactive module, a module
    already added to the environment, or a module about to be closed. The
    fields are then looked up in the environment on demand instead of
    walking (and strengthening) the whole signature eagerly, which makes the
    check proportional to the size of [super] instead of the size of the
    subtype's signature. *)
val check_subtypes : ?direct:bool -> cache:Cache.t -> ('a, Conversion.graph_inconsistency) Conversion.universe_state -> env -> ModPath.t -> ModPath.t -> module_type_body -> 'a * Cache.t

val check_polymorphic_universes :
  Environ.env ->
  UVars.AbstractContext.t -> UVars.AbstractContext.t ->
  bool
