(** Compatibility options *)

(** The options to make code compatible with Coq 8.5 are the following 
  (loaded by -compat 8.5).
*)

(** We use some deprecated options in this file, so we disable the
    corresponding warning, to silence the build of this file. *)
Local Set Warnings "-deprecated-option".

(* In 8.5, "intros [|]", taken e.g. on a goal "A\/B->C", does not
   behave as "intros [H|H]" but leave instead hypotheses quantified in
   the goal, here producing subgoals A->C and B->C. *)

Global Unset Bracketing Last Introduction Pattern.

(** Subst has some irregularities *)

Global Unset Regular Subst Tactic.

(** Injection does not ?? *)
Global Unset Structural Injection.

(** [abstract]ed proofs and Program obligations were not shrinked.
  Shrinking removes abstractions by unused variables in these cases *)
Global Unset Shrink Abstract.
Global Unset Shrink Obligations.

(** Refolding was used not only by [cbn] but also during unification,
  resulting in blowups sometimes. *)
Global Set Refolding Reduction.

(** The resolution algorithm for type classes has changed. *)
Global Set Typeclasses Legacy Resolution.

(** The resolution algorithm tried to limit introductions (and hence
  eta-expansions). Can be very expensive as well *)
Global Set Typeclasses Limit Intros.

(** The unification strategy for typeclasses eauto has changed, 
  Filtered Unification is not on by default in 8.6 though. *)
Global Unset Typeclasses Filtered Unification.

(** Allow silently letting unification constraints float after a ".", now
  disallowed by default (one gets unification errors instead) *)
Global Unset Solve Unification Constraints.
