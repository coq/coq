(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*                      Evgeny Makarov, INRIA, 2007                     *)
(************************************************************************)

(*i i*)

Require Export NumPrelude.

Module Type NZAxiomsSig.

Parameter Inline NZ : Set.
Parameter Inline NZeq : NZ -> NZ -> Prop.
Parameter Inline NZ0 : NZ.
Parameter Inline NZsucc : NZ -> NZ.
Parameter Inline NZpred : NZ -> NZ.
Parameter Inline NZplus : NZ -> NZ -> NZ.
Parameter Inline NZminus : NZ -> NZ -> NZ.
Parameter Inline NZtimes : NZ -> NZ -> NZ.

Axiom NZeq_equiv : equiv NZ NZeq.
Add Relation NZ NZeq
 reflexivity proved by (proj1 NZeq_equiv)
 symmetry proved by (proj2 (proj2 NZeq_equiv))
 transitivity proved by (proj1 (proj2 NZeq_equiv))
as NZeq_rel.

Add Morphism NZsucc with signature NZeq ==> NZeq as NZsucc_wd.
Add Morphism NZpred with signature NZeq ==> NZeq as NZpred_wd.
Add Morphism NZplus with signature NZeq ==> NZeq ==> NZeq as NZplus_wd.
Add Morphism NZminus with signature NZeq ==> NZeq ==> NZeq as NZminus_wd.
Add Morphism NZtimes with signature NZeq ==> NZeq ==> NZeq as NZtimes_wd.

Delimit Scope NatIntScope with NatInt.
Open Local Scope NatIntScope.
Notation "x == y"  := (NZeq x y) (at level 70) : NatIntScope.
Notation "x ~= y" := (~ NZeq x y) (at level 70) : NatIntScope.
Notation "0" := NZ0 : NatIntScope.
Notation S := NZsucc.
Notation P := NZpred.
Notation "1" := (S 0) : NatIntScope.
Notation "x + y" := (NZplus x y) : NatIntScope.
Notation "x - y" := (NZminus x y) : NatIntScope.
Notation "x * y" := (NZtimes x y) : NatIntScope.

Axiom NZpred_succ : forall n : NZ, P (S n) == n.

Axiom NZinduction :
  forall A : NZ -> Prop, predicate_wd NZeq A ->
    A 0 -> (forall n : NZ, A n <-> A (S n)) -> forall n : NZ, A n.

Axiom NZplus_0_l : forall n : NZ, 0 + n == n.
Axiom NZplus_succ_l : forall n m : NZ, (S n) + m == S (n + m).

Axiom NZminus_0_r : forall n : NZ, n - 0 == n.
Axiom NZminus_succ_r : forall n m : NZ, n - (S m) == P (n - m).

Axiom NZtimes_0_l : forall n : NZ, 0 * n == 0.
Axiom NZtimes_succ_l : forall n m : NZ, S n * m == n * m + m.

End NZAxiomsSig.

Module Type NZOrdAxiomsSig.
Declare Module Export NZAxiomsMod : NZAxiomsSig.
Open Local Scope NatIntScope.

Parameter Inline NZlt : NZ -> NZ -> Prop.
Parameter Inline NZle : NZ -> NZ -> Prop.
Parameter Inline NZmin : NZ -> NZ -> NZ.
Parameter Inline NZmax : NZ -> NZ -> NZ.

Add Morphism NZlt with signature NZeq ==> NZeq ==> iff as NZlt_wd.
Add Morphism NZle with signature NZeq ==> NZeq ==> iff as NZle_wd.
Add Morphism NZmin with signature NZeq ==> NZeq ==> NZeq as NZmin_wd.
Add Morphism NZmax with signature NZeq ==> NZeq ==> NZeq as NZmax_wd.

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
