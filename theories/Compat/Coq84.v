(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Compatibility file for making Coq act similar to Coq v8.4 *)
(** See https://coq.inria.fr/bugs/show_bug.cgi?id=4319 for updates *)
(** This is required in Coq 8.5 to use the [omega] tactic; in Coq 8.4, it's automatically available.  But ZArith_base puts infix ~ at level 7, and we don't want that, so we don't [Import] it. *)
Require Coq.omega.Omega.
Ltac omega := Coq.omega.Omega.omega.

(** The number of arguments given in [match] statements has changed from 8.4 to 8.5. *)
Global Set Asymmetric Patterns.

(** See bug 3545 *)
Global Set Universal Lemma Under Conjunction.

(** In 8.4, [admit] created a new axiom; in 8.5, it just shelves the goal. *)
Axiom proof_admitted : False.
Ltac admit := clear; abstract case proof_admitted.

(** In 8.5, [refine] leaves over dependent subgoals. *)
Tactic Notation "refine" uconstr(term) := refine term; shelve_unifiable.

(** In 8.4, [constructor (tac)] allowed backtracking across the use of [constructor]; it has been subsumed by [constructor; tac]. *)
Ltac constructor_84 := constructor.
Ltac constructor_84_n n := constructor n.
Ltac constructor_84_tac tac := once (constructor; tac).

Tactic Notation "constructor" := constructor_84.
Tactic Notation "constructor" int_or_var(n) := constructor_84_n n.
Tactic Notation "constructor" "(" tactic(tac) ")" := constructor_84_tac tac.

(** Some tactic notations do not factor well with tactics; we add global parsing entries for some tactics that would otherwise be overwritten by custom variants. See https://coq.inria.fr/bugs/show_bug.cgi?id=4392. *)
Tactic Notation "reflexivity" := reflexivity.
Tactic Notation "assumption" := assumption.
Tactic Notation "etransitivity" := etransitivity.
Tactic Notation "cut" constr(c) := cut c.
Tactic Notation "exact_no_check" constr(c) := exact_no_check c.
Tactic Notation "vm_cast_no_check" constr(c) := vm_cast_no_check c.
Tactic Notation "casetype" constr(c) := casetype c.
Tactic Notation "elimtype" constr(c) := elimtype c.
Tactic Notation "lapply" constr(c) := lapply c.
Tactic Notation "transitivity" constr(c) := transitivity c.
Tactic Notation "left" := left.
Tactic Notation "eleft" := eleft.
Tactic Notation "right" := right.
Tactic Notation "eright" := eright.
Tactic Notation "constructor" := constructor.
Tactic Notation "econstructor" := econstructor.
Tactic Notation "symmetry" := symmetry.
Tactic Notation "split" := split.
Tactic Notation "esplit" := esplit.

Global Set Regular Subst Tactic.

(** Some names have changed in the standard library, so we add aliases. *)
Require Coq.ZArith.Int.
Module Export Coq.
  Module Export ZArith.
    Module Int.
      Module Z_as_Int.
        Include Coq.ZArith.Int.Z_as_Int.
        (* FIXME: Should these get a (compat "8.4")?  Or be moved to Z_as_Int, probably? *)
        Notation plus := Coq.ZArith.Int.Z_as_Int.add (only parsing).
        Notation minus := Coq.ZArith.Int.Z_as_Int.sub (only parsing).
        Notation mult := Coq.ZArith.Int.Z_as_Int.mul (only parsing).
      End Z_as_Int.
    End Int.
  End ZArith.
End Coq.

(** Many things now import [PeanoNat] rather than [NPeano], so we require it so that the old absolute names in [NPeano.Nat] are available. *)
Require Coq.Numbers.Natural.Peano.NPeano.
