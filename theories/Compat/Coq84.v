(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Compatibility file for making Coq act similar to Coq v8.4 *)

(** Any compatibility changes to make future versions of Coq behave like Coq 8.5 are likely needed to make them behave like Coq 8.4. *)
Require Export Coq.Compat.Coq85.

(** See https://coq.inria.fr/bugs/show_bug.cgi?id=4319 for updates *)
(** This is required in Coq 8.5 to use the [omega] tactic; in Coq 8.4, it's automatically available.  But ZArith_base puts infix ~ at level 7, and we don't want that, so we don't [Import] it. *)
Require Coq.omega.Omega.
Ltac omega := Coq.omega.Omega.omega.

(** The number of arguments given in [match] statements has changed from 8.4 to 8.5. *)
Global Set Asymmetric Patterns.

(** The automatic elimination schemes for records were dropped by default in 8.5.  This restores the default behavior of Coq 8.4. *)
Global Set Nonrecursive Elimination Schemes.

(** See bug 3545 *)
Global Set Universal Lemma Under Conjunction.

(** Feature introduced in 8.5, disabled by default and configurable since 8.6. *)
Global Unset Refolding Reduction.

(** In 8.4, [constructor (tac)] allowed backtracking across the use of [constructor]; it has been subsumed by [constructor; tac]. *)
Ltac constructor_84_n n := constructor n.
Ltac constructor_84_tac tac := once (constructor; tac).

Tactic Notation "constructor" := Coq.Init.Notations.constructor.
Tactic Notation "constructor" int_or_var(n) := constructor_84_n n.
Tactic Notation "constructor" "(" tactic(tac) ")" := constructor_84_tac tac.

(** In 8.4, [econstructor (tac)] allowed backtracking across the use of [econstructor]; it has been subsumed by [econstructor; tac]. *)
Ltac econstructor_84_n n := econstructor n.
Ltac econstructor_84_tac tac := once (econstructor; tac).

Tactic Notation "econstructor" := Coq.Init.Notations.econstructor.
Tactic Notation "econstructor" int_or_var(n) := econstructor_84_n n.
Tactic Notation "econstructor" "(" tactic(tac) ")" := econstructor_84_tac tac.

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
Tactic Notation "symmetry" := symmetry.
Tactic Notation "split" := split.
Tactic Notation "esplit" := esplit.

(** Many things now import [PeanoNat] rather than [NPeano], so we require it so that the old absolute names in [NPeano.Nat] are available. *)
Require Coq.Numbers.Natural.Peano.NPeano.

(** The following coercions were declared by default in Specif.v. *)
Coercion sig_of_sig2 : sig2 >-> sig.
Coercion sigT_of_sigT2 : sigT2 >-> sigT.
Coercion sigT_of_sig : sig >-> sigT.
Coercion sig_of_sigT : sigT >-> sig.
Coercion sigT2_of_sig2 : sig2 >-> sigT2.
Coercion sig2_of_sigT2 : sigT2 >-> sig2.

(** In 8.4, the statement of admitted lemmas did not depend on the section
    variables. *)
Unset Keep Admitted Variables.
