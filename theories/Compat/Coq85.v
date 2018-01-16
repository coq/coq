(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Compatibility file for making Coq act similar to Coq v8.5 *)

(** Any compatibility changes to make future versions of Coq behave like Coq 8.6
    are likely needed to make them behave like Coq 8.5. *)
Local Set Warnings Append "-masking-absolute-name".
Require Export Coq.Compat.Coq86.

(** We use some deprecated options in this file, so we disable the
    corresponding warning, to silence the build of this file. *)
Local Set Warnings "-deprecated-option".

(* In 8.5, "intros [|]", taken e.g. on a goal "A\/B->C", does not
   behave as "intros [H|H]" but leave instead hypotheses quantified in
   the goal, here producing subgoals A->C and B->C. *)

Global Unset Bracketing Last Introduction Pattern.
Global Unset Regular Subst Tactic.
Global Unset Structural Injection.
Global Unset Shrink Abstract.
Global Unset Shrink Obligations.
Global Set Refolding Reduction.

(** The resolution algorithm for type classes has changed. *)
Global Set Typeclasses Legacy Resolution.
Global Set Typeclasses Limit Intros.
Global Unset Typeclasses Filtered Unification.

(** Allow silently letting unification constraints float after a "." *)
Global Unset Solve Unification Constraints.
