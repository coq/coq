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
open Locus
open EConstr

(** {6 Generalize tactics. } *)

val revert        : Id.t list -> unit Proofview.tactic

val bring_hyps : named_context -> unit Proofview.tactic

val generalize      : constr list -> unit Proofview.tactic
val generalize_gen  : (constr Locus.with_occurrences * Name.t) list -> unit Proofview.tactic

val new_generalize_gen  : ((occurrences * constr) * Name.t) list -> unit Proofview.tactic

val generalize_dep  : ?with_let:bool (** Don't lose let bindings *) -> constr  -> unit Proofview.tactic

val abstract_generalize : ?generalize_vars:bool -> ?force_dep:bool -> Id.t -> unit Proofview.tactic
