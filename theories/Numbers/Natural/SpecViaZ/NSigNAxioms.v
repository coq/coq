(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

Require Import ZArith Nnat NAxioms NDiv NSig.

(** * The interface [NSig.NType] implies the interface [NAxiomsSig] *)

Module NTypeIsNAxioms (Import N : NType').

Hint Rewrite
 spec_0 spec_succ spec_add spec_mul spec_pred spec_sub
 spec_div spec_modulo spec_gcd spec_compare spec_eq_bool
 spec_max spec_min spec_power_pos spec_power
 : nsimpl.
Ltac nsimpl := autorewrite with nsimpl.
Ltac ncongruence := unfold eq; repeat red; intros; nsimpl; congruence.
Ltac zify := unfold eq, lt, le in *; nsimpl.

Local Obligation Tactic := ncongruence.

Instance eq_equiv : Equivalence eq.
Proof. unfold eq. firstorder. Qed.

Program Instance succ_wd : Proper (eq==>eq) succ.
Program Instance pred_wd : Proper (eq==>eq) pred.
Program Instance add_wd : Proper (eq==>eq==>eq) add.
Program Instance sub_wd : Proper (eq==>eq==>eq) sub.
Program Instance mul_wd : Proper (eq==>eq==>eq) mul.

Theorem pred_succ : forall n, pred (succ n) == n.
Proof.
intros. zify. generalize (spec_pos n); omega with *.
Qed.

Definition N_of_Z z := of_N (Zabs_N z).

Section Induction.

Variable A : N.t -> Prop.
Hypothesis A_wd : Proper (eq==>iff) A.
Hypothesis A0 : A 0.
Hypothesis AS : forall n, A n <-> A (succ n).

Let B (z : Z) := A (N_of_Z z).

Lemma B0 : B 0.
Proof.
unfold B, N_of_Z; simpl.
rewrite <- (A_wd 0); auto.
red; rewrite spec_0, spec_of_N; auto.
Qed.

Lemma BS : forall z : Z, (0 <= z)%Z -> B z -> B (z + 1).
Proof.
intros z H1 H2.
unfold B in *. apply -> AS in H2.
setoid_replace (N_of_Z (z + 1)) with (succ (N_of_Z z)); auto.
unfold eq. rewrite spec_succ.
unfold N_of_Z.
rewrite 2 spec_of_N, 2 Z_of_N_abs, 2 Zabs_eq; auto with zarith.
Qed.

Lemma B_holds : forall z : Z, (0 <= z)%Z -> B z.
Proof.
exact (natlike_ind B B0 BS).
Qed.

Theorem bi_induction : forall n, A n.
Proof.
intro n. setoid_replace n with (N_of_Z (to_Z n)).
apply B_holds. apply spec_pos.
red; unfold N_of_Z.
rewrite spec_of_N, Z_of_N_abs, Zabs_eq; auto.
apply spec_pos.
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
intros. zify. generalize (spec_pos n); omega with *.
Qed.

Theorem sub_succ_r : forall n m, n - (succ m) == pred (n - m).
Proof.
intros. zify. omega with *.
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

(** Properties specific to natural numbers, not integers. *)

Theorem pred_0 : pred 0 == 0.
Proof.
zify. auto.
Qed.

Program Instance div_wd : Proper (eq==>eq==>eq) div.
Program Instance mod_wd : Proper (eq==>eq==>eq) modulo.

Theorem div_mod : forall a b, ~b==0 -> a == b*(div a b) + (modulo a b).
Proof.
intros a b. zify. intros. apply Z_div_mod_eq_full; auto.
Qed.

Theorem mod_upper_bound : forall a b, ~b==0 -> modulo a b < b.
Proof.
intros a b. zify. intros.
destruct (Z_mod_lt [a] [b]); auto.
generalize (spec_pos b); auto with zarith.
Qed.

Definition recursion (A : Type) (a : A) (f : N.t -> A -> A) (n : N.t) :=
  Nrect (fun _ => A) a (fun n a => f (N.of_N n) a) (N.to_N n).
Implicit Arguments recursion [A].

Instance recursion_wd (A : Type) (Aeq : relation A) :
 Proper (Aeq ==> (eq==>Aeq==>Aeq) ==> eq ==> Aeq) (@recursion A).
Proof.
unfold eq.
intros a a' Eaa' f f' Eff' x x' Exx'.
unfold recursion.
unfold N.to_N.
rewrite <- Exx'; clear x' Exx'.
replace (Zabs_N [x]) with (N_of_nat (Zabs_nat [x])).
induction (Zabs_nat [x]).
simpl; auto.
rewrite N_of_S, 2 Nrect_step; auto. apply Eff'; auto.
destruct [x]; simpl; auto.
change (nat_of_P p) with (nat_of_N (Npos p)); apply N_of_nat_of_N.
change (nat_of_P p) with (nat_of_N (Npos p)); apply N_of_nat_of_N.
Qed.

Theorem recursion_0 :
  forall (A : Type) (a : A) (f : N.t -> A -> A), recursion a f 0 = a.
Proof.
intros A a f; unfold recursion, N.to_N; rewrite N.spec_0; simpl; auto.
Qed.

Theorem recursion_succ :
  forall (A : Type) (Aeq : relation A) (a : A) (f : N.t -> A -> A),
    Aeq a a -> Proper (eq==>Aeq==>Aeq) f ->
      forall n, Aeq (recursion a f (succ n)) (f n (recursion a f n)).
Proof.
unfold N.eq, recursion; intros A Aeq a f EAaa f_wd n.
replace (N.to_N (succ n)) with (Nsucc (N.to_N n)).
rewrite Nrect_step.
apply f_wd; auto.
unfold N.to_N.
rewrite N.spec_of_N, Z_of_N_abs, Zabs_eq; auto.
 apply N.spec_pos.

fold (recursion a f n).
apply recursion_wd; auto.
red; auto.
unfold N.to_N.

rewrite N.spec_succ.
change ([n]+1)%Z with (Zsucc [n]).
apply Z_of_N_eq_rev.
rewrite Z_of_N_succ.
rewrite 2 Z_of_N_abs.
rewrite 2 Zabs_eq; auto.
generalize (spec_pos n); auto with zarith.
apply spec_pos; auto.
Qed.

End NTypeIsNAxioms.

Module NType_NAxioms (N : NType)
 <: NAxiomsSig <: NDivSig <: HasCompare N <: HasEqBool N <: HasMinMax N
 := N <+ NTypeIsNAxioms.
