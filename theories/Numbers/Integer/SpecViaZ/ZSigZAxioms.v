(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import ZArith ZAxioms ZDivFloor ZSig.

(** * The interface [ZSig.ZType] implies the interface [ZAxiomsSig]

    It also provides [sgn], [abs], [div], [mod]
*)


Module ZTypeIsZAxioms (Import Z : ZType').

Hint Rewrite
 spec_0 spec_1 spec_add spec_sub spec_pred spec_succ
 spec_mul spec_opp spec_of_Z spec_div spec_modulo
 spec_compare spec_eq_bool spec_max spec_min spec_abs spec_sgn
 : zsimpl.

Ltac zsimpl := autorewrite with zsimpl.
Ltac zcongruence := repeat red; intros; zsimpl; congruence.
Ltac zify := unfold eq, lt, le in *; zsimpl.

Instance eq_equiv : Equivalence eq.
Proof. unfold eq. firstorder. Qed.

Local Obligation Tactic := zcongruence.

Program Instance succ_wd : Proper (eq ==> eq) succ.
Program Instance pred_wd : Proper (eq ==> eq) pred.
Program Instance add_wd : Proper (eq ==> eq ==> eq) add.
Program Instance sub_wd : Proper (eq ==> eq ==> eq) sub.
Program Instance mul_wd : Proper (eq ==> eq ==> eq) mul.

Theorem pred_succ : forall n, pred (succ n) == n.
Proof.
intros. zify. auto with zarith.
Qed.

Section Induction.

Variable A : Z.t -> Prop.
Hypothesis A_wd : Proper (eq==>iff) A.
Hypothesis A0 : A 0.
Hypothesis AS : forall n, A n <-> A (succ n).

Let B (z : Z) := A (of_Z z).

Lemma B0 : B 0.
Proof.
unfold B; simpl.
rewrite <- (A_wd 0); auto.
zify. auto.
Qed.

Lemma BS : forall z : Z, B z -> B (z + 1).
Proof.
intros z H.
unfold B in *. apply -> AS in H.
setoid_replace (of_Z (z + 1)) with (succ (of_Z z)); auto.
zify. auto.
Qed.

Lemma BP : forall z : Z, B z -> B (z - 1).
Proof.
intros z H.
unfold B in *. rewrite AS.
setoid_replace (succ (of_Z (z - 1))) with (of_Z z); auto.
zify. auto with zarith.
Qed.

Lemma B_holds : forall z : Z, B z.
Proof.
intros; destruct (Z_lt_le_dec 0 z).
apply natlike_ind; auto with zarith.
apply B0.
intros; apply BS; auto.
replace z with (-(-z))%Z in * by (auto with zarith).
remember (-z)%Z as z'.
pattern z'; apply natlike_ind.
apply B0.
intros; rewrite Zopp_succ; unfold Zpred; apply BP; auto.
subst z'; auto with zarith.
Qed.

Theorem bi_induction : forall n, A n.
Proof.
intro n. setoid_replace n with (of_Z (to_Z n)).
apply B_holds.
zify. auto.
Qed.

End Induction.

Theorem add_0_l : forall n, 0 + n == n.
Proof.
intros. zify. auto with zarith.
Qed.

Theorem add_succ_l : forall n m, (succ n) + m == succ (n + m).
Proof.
intros. zify. auto with zarith.
Qed.

Theorem sub_0_r : forall n, n - 0 == n.
Proof.
intros. zify. auto with zarith.
Qed.

Theorem sub_succ_r : forall n m, n - (succ m) == pred (n - m).
Proof.
intros. zify. auto with zarith.
Qed.

Theorem mul_0_l : forall n, 0 * n == 0.
Proof.
intros. zify. auto with zarith.
Qed.

Theorem mul_succ_l : forall n m, (succ n) * m == n * m + m.
Proof.
intros. zify. ring.
Qed.

(** Order *)

Lemma compare_spec : forall x y, CompSpec eq lt x y (compare x y).
Proof.
 intros. zify. destruct (Zcompare_spec [x] [y]); auto.
Qed.

Definition eqb := eq_bool.

Lemma eqb_eq : forall x y, eq_bool x y = true <-> x == y.
Proof.
 intros. zify. symmetry. apply Zeq_is_eq_bool.
Qed.

Instance compare_wd : Proper (eq ==> eq ==> Logic.eq) compare.
Proof.
intros x x' Hx y y' Hy. rewrite 2 spec_compare, Hx, Hy; intuition.
Qed.

Instance lt_wd : Proper (eq ==> eq ==> iff) lt.
Proof.
intros x x' Hx y y' Hy; unfold lt; rewrite Hx, Hy; intuition.
Qed.

Theorem lt_eq_cases : forall n m, n <= m <-> n < m \/ n == m.
Proof.
intros. zify. omega.
Qed.

Theorem lt_irrefl : forall n, ~ n < n.
Proof.
intros. zify. omega.
Qed.

Theorem lt_succ_r : forall n m, n < (succ m) <-> n <= m.
Proof.
intros. zify. omega.
Qed.

Theorem min_l : forall n m, n <= m -> min n m == n.
Proof.
intros n m. zify. omega with *.
Qed.

Theorem min_r : forall n m, m <= n -> min n m == m.
Proof.
intros n m. zify. omega with *.
Qed.

Theorem max_l : forall n m, m <= n -> max n m == n.
Proof.
intros n m. zify. omega with *.
Qed.

Theorem max_r : forall n m, n <= m -> max n m == m.
Proof.
intros n m. zify. omega with *.
Qed.

(** Part specific to integers, not natural numbers *)

Program Instance opp_wd : Proper (eq ==> eq) opp.

Theorem succ_pred : forall n, succ (pred n) == n.
Proof.
intros. zify. auto with zarith.
Qed.

Theorem opp_0 : - 0 == 0.
Proof.
intros. zify. auto with zarith.
Qed.

Theorem opp_succ : forall n, - (succ n) == pred (- n).
Proof.
intros. zify. auto with zarith.
Qed.

Theorem abs_eq : forall n, 0 <= n -> abs n == n.
Proof.
intros n. zify. omega with *.
Qed.

Theorem abs_neq : forall n, n <= 0 -> abs n == -n.
Proof.
intros n. zify. omega with *.
Qed.

Theorem sgn_null : forall n, n==0 -> sgn n == 0.
Proof.
intros n. zify. omega with *.
Qed.

Theorem sgn_pos : forall n, 0<n -> sgn n == succ 0.
Proof.
intros n. zify. omega with *.
Qed.

Theorem sgn_neg : forall n, n<0 -> sgn n == opp (succ 0).
Proof.
intros n. zify. omega with *.
Qed.

Program Instance div_wd : Proper (eq==>eq==>eq) div.
Program Instance mod_wd : Proper (eq==>eq==>eq) modulo.

Theorem div_mod : forall a b, ~b==0 -> a == b*(div a b) + (modulo a b).
Proof.
intros a b. zify. intros. apply Z_div_mod_eq_full; auto.
Qed.

Theorem mod_pos_bound :
 forall a b, 0 < b -> 0 <= modulo a b /\ modulo a b < b.
Proof.
intros a b. zify. intros. apply Z_mod_lt; auto with zarith.
Qed.

Theorem mod_neg_bound :
 forall a b, b < 0 -> b < modulo a b /\ modulo a b <= 0.
Proof.
intros a b. zify. intros. apply Z_mod_neg; auto with zarith.
Qed.

End ZTypeIsZAxioms.

Module ZType_ZAxioms (Z : ZType)
 <: ZAxiomsSig <: ZDivSig <: HasCompare Z <: HasEqBool Z <: HasMinMax Z
 := Z <+ ZTypeIsZAxioms.
