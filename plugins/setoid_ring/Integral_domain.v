(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Export Cring.


(* Definition of integral domains: commutative ring without zero divisor *)

Class Integral_domain {R : Type}`{Rcr:Cring R} := {
 integral_domain_product:
   forall x y, x * y == 0 -> x == 0 \/ y == 0;
 integral_domain_one_zero: not (1 == 0)}.

Section integral_domain.

Context {R:Type}`{Rid:Integral_domain R}.

Lemma integral_domain_minus_one_zero: ~ - (1:R) == 0.
red;intro. apply integral_domain_one_zero. 
assert (0 == - (0:R)). cring.
rewrite H0. rewrite <- H. cring.
Qed.


Definition pow (r : R) (n : nat) := Ring_theory.pow_N 1 mul r (N.of_nat n).

Lemma pow_not_zero: forall p n, pow p n == 0 -> p == 0.
induction n. unfold pow; simpl. intros. absurd (1 == 0). 
simpl. apply integral_domain_one_zero.
 trivial. setoid_replace (pow p (S n)) with (p * (pow p n)).
intros. 
case (integral_domain_product p (pow p n) H). trivial. trivial. 
unfold pow; simpl. 
clear IHn. induction n; simpl; try cring. 
 rewrite Ring_theory.pow_pos_succ. cring. apply ring_setoid.
apply ring_mult_comp.
apply ring_mul_assoc.
Qed.

Lemma Rintegral_domain_pow:
  forall c p r, ~c == 0 -> c * (pow p r) == ring0 -> p == ring0.
intros. case (integral_domain_product c (pow p r) H0). intros; absurd (c == ring0); auto. 
intros. apply pow_not_zero with r. trivial. Qed.   

End integral_domain.

