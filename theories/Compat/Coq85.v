(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Compatibility file for making Coq act similar to Coq v8.5 *)

(** Any compatibility changes to make future versions of Coq behave like Coq 8.6
    are likely needed to make them behave like Coq 8.5. *)
Require Export Coq.Compat.Coq86.

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

(** In Coq 8.5, [] meant Vector, and [ ] meant list.  Restore this
    behavior, to allow user-defined [] to not override vector
    notations.  See https://coq.inria.fr/bugs/show_bug.cgi?id=4785. *)

Require Coq.Lists.List.
Require Coq.Vectors.VectorDef.
Module Export Coq.
Module Export Vectors.
Module VectorDef.
Export Coq.Vectors.VectorDef.
Module VectorNotations.
Export Coq.Vectors.VectorDef.VectorNotations.
Notation "[]" := (VectorDef.nil _) : vector_scope.
End VectorNotations.
End VectorDef.
End Vectors.
End Coq.
