(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

Require Import Decidable.

Open Local Scope nat_scope.

Implicit Types m n x y : nat.

Theorem O_or_S : forall n, {m : nat | S m = n} + {0 = n}.
Proof.
  induction n.
  auto.
  left; exists n; auto.
Defined.

Theorem eq_nat_dec : forall n m, {n = m} + {n <> m}.
Proof.
  induction n; destruct m; auto.
  elim (IHn m); auto.
Defined.

Hint Resolve O_or_S eq_nat_dec: arith.

Theorem dec_eq_nat : forall n m, decidable (n = m).
  intros x y; unfold decidable in |- *; elim (eq_nat_dec x y); auto with arith.
Defined.
