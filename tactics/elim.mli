(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open EConstr
open Tactypes

(** Eliminations tactics. *)

type branch_args = private {
  ity        : Constr.pinductive;  (** the type we were eliminating on *)
  branchnum  : int;         (** the branch number *)
  nassums    : int;         (** number of assumptions/letin to be introduced *)
  branchsign : bool list;   (** the signature of the branch.
                                true=assumption, false=let-in *)
  branchnames : intro_patterns}

type branch_assumptions = private {
  ba        : branch_args;       (** the branch args *)
  assums    : named_context}   (** the list of assumptions introduced *)

val case_then_using :
  or_and_intro_pattern option -> (branch_args -> unit Proofview.tactic) ->
  constr option -> inductive * EInstance.t -> constr * types -> unit Proofview.tactic

val case_nodep_then_using :
  or_and_intro_pattern option -> (branch_args -> unit Proofview.tactic) ->
  constr option -> inductive * EInstance.t -> constr * types -> unit Proofview.tactic

val introCaseAssumsThen : Tactics.evars_flag ->
  (intro_patterns -> branch_assumptions -> unit Proofview.tactic) ->
    branch_args -> unit Proofview.tactic

val h_decompose       : inductive list -> constr -> unit Proofview.tactic
val h_decompose_or    : constr -> unit Proofview.tactic
val h_decompose_and   : constr -> unit Proofview.tactic
val h_double_induction : quantified_hypothesis -> quantified_hypothesis-> unit Proofview.tactic
