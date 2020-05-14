(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Constr
open Univ

(** Return the set of all universes appearing in [constr]. *)
val universes_of_constr : constr -> LSet.t
[@@ocaml.deprecated "Use [Vars.universes_of_constr]"]

val restrict_universe_context : lbound:UGraph.Bound.t -> ContextSet.t -> LSet.t -> ContextSet.t
[@@ocaml.deprecated "Use [UState.restrict_universe_context]"]
