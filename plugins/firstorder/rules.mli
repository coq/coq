(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
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

val wrap : int -> bool -> seqtac

val basename_of_global: GlobRef.t -> Id.t

val clear_global: GlobRef.t -> tactic

val axiom_tac : constr -> Sequent.t -> tactic

val ll_atom_tac : constr -> lseqtac with_backtracking

val and_tac : seqtac with_backtracking

val or_tac : seqtac with_backtracking

val arrow_tac : seqtac with_backtracking

val left_and_tac : pinductive -> lseqtac with_backtracking

val left_or_tac : pinductive -> lseqtac with_backtracking

val left_false_tac : GlobRef.t -> tactic

val ll_ind_tac : pinductive -> constr list -> lseqtac with_backtracking

val ll_arrow_tac : constr -> constr -> constr -> lseqtac with_backtracking

val forall_tac : seqtac with_backtracking

val left_exists_tac : pinductive -> lseqtac with_backtracking

val ll_forall_tac : types -> lseqtac with_backtracking

val normalize_evaluables : tactic
