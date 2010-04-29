(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Term
open Tacmach
open Names
open Libnames

type seqtac= (Sequent.t -> tactic) -> Sequent.t -> tactic

type lseqtac= global_reference -> seqtac

type 'a with_backtracking = tactic -> 'a

val wrap : int -> bool -> seqtac

val basename_of_global: global_reference -> identifier

val clear_global: global_reference -> tactic

val axiom_tac : constr -> Sequent.t -> tactic

val ll_atom_tac : constr -> lseqtac with_backtracking

val and_tac : seqtac with_backtracking

val or_tac : seqtac with_backtracking

val arrow_tac : seqtac with_backtracking

val left_and_tac : inductive -> lseqtac with_backtracking

val left_or_tac : inductive -> lseqtac with_backtracking

val left_false_tac : global_reference -> tactic

val ll_ind_tac : inductive -> constr list -> lseqtac with_backtracking

val ll_arrow_tac : constr -> constr -> constr -> lseqtac with_backtracking

val forall_tac : seqtac with_backtracking

val left_exists_tac : inductive -> lseqtac with_backtracking

val ll_forall_tac : types -> lseqtac with_backtracking

val normalize_evaluables : tactic
