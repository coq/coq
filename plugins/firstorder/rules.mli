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
open Constr
open EConstr

type tactic = unit Proofview.tactic

type seqtac= (Sequent.t -> tactic) -> Sequent.t -> tactic

type lseqtac= GlobRef.t -> seqtac

type 'a with_backtracking = tactic -> 'a

val wrap : flags:Formula.flags -> int -> bool -> seqtac

val clear_global: GlobRef.t -> tactic

val axiom_tac : Sequent.t -> tactic

val ll_atom_tac : flags:Formula.flags -> Formula.atom -> lseqtac with_backtracking

val and_tac : flags:Formula.flags -> seqtac with_backtracking

val or_tac : flags:Formula.flags -> seqtac with_backtracking

val arrow_tac : flags:Formula.flags -> seqtac with_backtracking

val left_and_tac : flags:Formula.flags -> pinductive -> lseqtac with_backtracking

val left_or_tac : flags:Formula.flags -> pinductive -> lseqtac with_backtracking

val left_false_tac : GlobRef.t -> tactic

val ll_ind_tac : flags:Formula.flags -> pinductive -> constr list -> lseqtac with_backtracking

val ll_arrow_tac : flags:Formula.flags -> constr -> constr -> constr -> lseqtac with_backtracking

val forall_tac : flags:Formula.flags -> seqtac with_backtracking

val left_exists_tac : flags:Formula.flags -> pinductive -> lseqtac with_backtracking

val ll_forall_tac : flags:Formula.flags -> types -> lseqtac with_backtracking
