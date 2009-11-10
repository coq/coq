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

Parameter Inline t : Type.
Parameter Inline eq : t -> t -> Prop.
Parameter Inline zero : t.
Parameter Inline succ : t -> t.
Parameter Inline pred : t -> t.
Parameter Inline add : t -> t -> t.
Parameter Inline sub : t -> t -> t.
Parameter Inline mul : t -> t -> t.

(* Unary subtraction (opp) is not defined on natural numbers, so we have
   it for integers only *)

Instance eq_equiv : Equivalence eq.
Instance succ_wd : Proper (eq ==> eq) succ.
Instance pred_wd : Proper (eq ==> eq) pred.
Instance add_wd : Proper (eq ==> eq ==> eq) add.
Instance sub_wd : Proper (eq ==> eq ==> eq) sub.
Instance mul_wd : Proper (eq ==> eq ==> eq) mul.

Delimit Scope NumScope with Num.
Local Open Scope NumScope.
Notation "x == y"  := (eq x y) (at level 70) : NumScope.
Notation "x ~= y" := (~ eq x y) (at level 70) : NumScope.
Notation "0" := zero : NumScope.
Notation S := succ.
Notation P := pred.
Notation "1" := (S 0) : NumScope.
Notation "x + y" := (add x y) : NumScope.
Notation "x - y" := (sub x y) : NumScope.
Notation "x * y" := (mul x y) : NumScope.

Axiom pred_succ : forall n, P (S n) == n.

Axiom bi_induction :
  forall A : t -> Prop, Proper (eq==>iff) A ->
    A 0 -> (forall n, A n <-> A (S n)) -> forall n, A n.

Axiom add_0_l : forall n, 0 + n == n.
Axiom add_succ_l : forall n m, (S n) + m == S (n + m).

Axiom sub_0_r : forall n, n - 0 == n.
Axiom sub_succ_r : forall n m, n - (S m) == P (n - m).

Axiom mul_0_l : forall n, 0 * n == 0.
Axiom mul_succ_l : forall n m, S n * m == n * m + m.

End NZAxiomsSig.

Module Type NZOrdAxiomsSig.
Include Type NZAxiomsSig.
Local Open Scope NumScope.

Parameter Inline lt : t -> t -> Prop.
Parameter Inline le : t -> t -> Prop.

Notation "x < y" := (lt x y) : NumScope.
Notation "x <= y" := (le x y) : NumScope.
Notation "x > y" := (lt y x) (only parsing) : NumScope.
Notation "x >= y" := (le y x) (only parsing) : NumScope.

Instance lt_wd : Proper (eq ==> eq ==> iff) lt.
(** Compatibility of [le] can be proved later from [lt_wd] and [lt_eq_cases] *)

Axiom lt_eq_cases : forall n m, n <= m <-> n < m \/ n == m.
Axiom lt_irrefl : forall n, ~ (n < n).
Axiom lt_succ_r : forall n m, n < S m <-> n <= m.

Parameter Inline min : t -> t -> t.
Parameter Inline max : t -> t -> t.
(** Compatibility of [min] and [max] can be proved later *)
Axiom min_l : forall n m, n <= m -> min n m == n.
Axiom min_r : forall n m, m <= n -> min n m == m.
Axiom max_l : forall n m, m <= n -> max n m == n.
Axiom max_r : forall n m, n <= m -> max n m == m.

End NZOrdAxiomsSig.
