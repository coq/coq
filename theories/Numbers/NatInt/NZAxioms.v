(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*                      Evgeny Makarov, INRIA, 2007                     *)
(************************************************************************)

(*i $Id$ i*)

Require Export NumPrelude.

Module Type NZAxiomsSig.

Parameter Inline NZ : Type.
Parameter Inline NZeq : NZ -> NZ -> Prop.
Parameter Inline NZ0 : NZ.
Parameter Inline NZsucc : NZ -> NZ.
Parameter Inline NZpred : NZ -> NZ.
Parameter Inline NZadd : NZ -> NZ -> NZ.
Parameter Inline NZsub : NZ -> NZ -> NZ.
Parameter Inline NZmul : NZ -> NZ -> NZ.

(* Unary subtraction (opp) is not defined on natural numbers, so we have
   it for integers only *)

Instance NZeq_equiv : Equivalence NZeq.
Instance NZsucc_wd : Proper (NZeq ==> NZeq) NZsucc.
Instance NZpred_wd : Proper (NZeq ==> NZeq) NZpred.
Instance NZadd_wd : Proper (NZeq ==> NZeq ==> NZeq) NZadd.
Instance NZsub_wd : Proper (NZeq ==> NZeq ==> NZeq) NZsub.
Instance NZmul_wd : Proper (NZeq ==> NZeq ==> NZeq) NZmul.

Delimit Scope NatIntScope with NatInt.
Open Local Scope NatIntScope.
Notation "x == y"  := (NZeq x y) (at level 70) : NatIntScope.
Notation "x ~= y" := (~ NZeq x y) (at level 70) : NatIntScope.
Notation "0" := NZ0 : NatIntScope.
Notation S := NZsucc.
Notation P := NZpred.
Notation "1" := (S 0) : NatIntScope.
Notation "x + y" := (NZadd x y) : NatIntScope.
Notation "x - y" := (NZsub x y) : NatIntScope.
Notation "x * y" := (NZmul x y) : NatIntScope.

Axiom NZpred_succ : forall n : NZ, P (S n) == n.

Axiom NZinduction :
  forall A : NZ -> Prop, Proper (NZeq==>iff) A ->
    A 0 -> (forall n : NZ, A n <-> A (S n)) -> forall n : NZ, A n.

Axiom NZadd_0_l : forall n : NZ, 0 + n == n.
Axiom NZadd_succ_l : forall n m : NZ, (S n) + m == S (n + m).

Axiom NZsub_0_r : forall n : NZ, n - 0 == n.
Axiom NZsub_succ_r : forall n m : NZ, n - (S m) == P (n - m).

Axiom NZmul_0_l : forall n : NZ, 0 * n == 0.
Axiom NZmul_succ_l : forall n m : NZ, S n * m == n * m + m.

End NZAxiomsSig.

Module Type NZOrdAxiomsSig.
Declare Module Export NZAxiomsMod : NZAxiomsSig.
Open Local Scope NatIntScope.

Parameter Inline NZlt : NZ -> NZ -> Prop.
Parameter Inline NZle : NZ -> NZ -> Prop.
Parameter Inline NZmin : NZ -> NZ -> NZ.
Parameter Inline NZmax : NZ -> NZ -> NZ.

Instance NZlt_wd : Proper (NZeq ==> NZeq ==> iff) NZlt.
Instance NZle_wd : Proper (NZeq ==> NZeq ==> iff) NZle.
Instance NZmin_wd : Proper (NZeq ==> NZeq ==> NZeq) NZmin.
Instance NZmax_wd : Proper (NZeq ==> NZeq ==> NZeq) NZmax.

Notation "x < y" := (NZlt x y) : NatIntScope.
Notation "x <= y" := (NZle x y) : NatIntScope.
Notation "x > y" := (NZlt y x) (only parsing) : NatIntScope.
Notation "x >= y" := (NZle y x) (only parsing) : NatIntScope.

Axiom NZlt_eq_cases : forall n m : NZ, n <= m <-> n < m \/ n == m.
Axiom NZlt_irrefl : forall n : NZ, ~ (n < n).
Axiom NZlt_succ_r : forall n m : NZ, n < S m <-> n <= m.

Axiom NZmin_l : forall n m : NZ, n <= m -> NZmin n m == n.
Axiom NZmin_r : forall n m : NZ, m <= n -> NZmin n m == m.
Axiom NZmax_l : forall n m : NZ, m <= n -> NZmax n m == n.
Axiom NZmax_r : forall n m : NZ, n <= m -> NZmax n m == m.

End NZOrdAxiomsSig.
