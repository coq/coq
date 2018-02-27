(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
(*                      Evgeny Makarov, INRIA, 2007                     *)
(************************************************************************)

Require Import Bool. (* To get the orb and negb function *)
Require Import RelationPairs.
Require Export NStrongRec.

(** In this module, we derive generic implementations of usual operators
   just via the use of a [recursion] function. *)

Module NdefOpsProp (Import N : NAxiomsRecSig').
Include NStrongRecProp N.

(** Nullity Test *)

Definition if_zero (A : Type) (a b : A) (n : N.t) : A :=
  recursion a (fun _ _ => b) n.

Arguments if_zero [A] a b n.

Instance if_zero_wd (A : Type) :
 Proper (Logic.eq ==> Logic.eq ==> N.eq ==> Logic.eq) (@if_zero A).
Proof.
unfold if_zero. (* TODO : solve_proper : SLOW + BUG *)
f_equiv'.
Qed.

Theorem if_zero_0 : forall (A : Type) (a b : A), if_zero a b 0 = a.
Proof.
unfold if_zero; intros; now rewrite recursion_0.
Qed.

Theorem if_zero_succ :
 forall (A : Type) (a b : A) (n : N.t), if_zero a b (S n) = b.
Proof.
intros; unfold if_zero.
now rewrite recursion_succ.
Qed.

(*****************************************************)
(**                   Addition                       *)

Definition def_add (x y : N.t) := recursion y (fun _ => S) x.

Local Infix "+++" := def_add (at level 50, left associativity).

Instance def_add_wd : Proper (N.eq ==> N.eq ==> N.eq) def_add.
Proof.
unfold def_add. f_equiv'.
Qed.

Theorem def_add_0_l : forall y, 0 +++ y == y.
Proof.
intro y. unfold def_add. now rewrite recursion_0.
Qed.

Theorem def_add_succ_l : forall x y, S x +++ y == S (x +++ y).
Proof.
intros x y; unfold def_add.
rewrite recursion_succ; f_equiv'.
Qed.

Theorem def_add_add : forall n m, n +++ m == n + m.
Proof.
intros n m; induct n.
now rewrite def_add_0_l, add_0_l.
intros n H. now rewrite def_add_succ_l, add_succ_l, H.
Qed.

(*****************************************************)
(**                  Multiplication                  *)

Definition def_mul (x y : N.t) := recursion 0 (fun _ p => p +++ x) y.

Local Infix "**" := def_mul (at level 40, left associativity).

Instance def_mul_wd : Proper (N.eq ==> N.eq ==> N.eq) def_mul.
Proof.
unfold def_mul. (* TODO : solve_proper SLOW + BUG *)
f_equiv'.
Qed.

Theorem def_mul_0_r : forall x, x ** 0 == 0.
Proof.
intro. unfold def_mul. now rewrite recursion_0.
Qed.

Theorem def_mul_succ_r : forall x y, x ** S y == x ** y +++ x.
Proof.
intros x y; unfold def_mul.
rewrite recursion_succ; auto with *.
f_equiv'.
Qed.

Theorem def_mul_mul : forall n m, n ** m == n * m.
Proof.
intros n m; induct m.
now rewrite def_mul_0_r, mul_0_r.
intros m IH; now rewrite def_mul_succ_r, mul_succ_r, def_add_add, IH.
Qed.

(*****************************************************)
(**                     Order                        *)

Definition ltb (m : N.t) : N.t -> bool :=
recursion
  (if_zero false true)
  (fun _ f n => recursion false (fun n' _ => f n') n)
  m.

Local Infix "<<" := ltb (at level 70, no associativity).

Instance ltb_wd : Proper (N.eq ==> N.eq ==> Logic.eq) ltb.
Proof.
unfold ltb. f_equiv'.
Qed.

Theorem ltb_base : forall n, 0 << n = if_zero false true n.
Proof.
intro n; unfold ltb; now rewrite recursion_0.
Qed.

Theorem ltb_step :
  forall m n, S m << n = recursion false (fun n' _ => m << n') n.
Proof.
intros m n; unfold ltb at 1.
f_equiv.
rewrite recursion_succ; f_equiv'.
Qed.

(* Above, we rewrite applications of function. Is it possible to rewrite
functions themselves, i.e., rewrite (recursion lt_base lt_step (S n)) to
lt_step n (recursion lt_base lt_step n)? *)

Theorem ltb_0 : forall n, n << 0 = false.
Proof.
cases n.
rewrite ltb_base; now rewrite if_zero_0.
intro n; rewrite ltb_step. now rewrite recursion_0.
Qed.

Theorem ltb_0_succ : forall n, 0 << S n = true.
Proof.
intro n; rewrite ltb_base; now rewrite if_zero_succ.
Qed.

Theorem succ_ltb_mono : forall n m, (S n << S m) = (n << m).
Proof.
intros n m.
rewrite ltb_step. rewrite recursion_succ; f_equiv'.
Qed.

Theorem ltb_lt : forall n m, n << m = true <-> n < m.
Proof.
double_induct n m.
cases m.
rewrite ltb_0. split; intro H; [discriminate H | false_hyp H nlt_0_r].
intro n. rewrite ltb_0_succ. split; intro; [apply lt_0_succ | reflexivity].
intro n. rewrite ltb_0. split; intro H; [discriminate | false_hyp H nlt_0_r].
intros n m. rewrite succ_ltb_mono. now rewrite <- succ_lt_mono.
Qed.

Theorem ltb_ge : forall n m, n << m = false <-> n >= m.
Proof.
intros. rewrite <- not_true_iff_false, ltb_lt. apply nlt_ge.
Qed.

(*****************************************************)
(**                     Even                         *)

Definition even (x : N.t) := recursion true (fun _ p => negb p) x.

Instance even_wd : Proper (N.eq==>Logic.eq) even.
Proof.
unfold even. f_equiv'.
Qed.

Theorem even_0 : even 0 = true.
Proof.
unfold even.
now rewrite recursion_0.
Qed.

Theorem even_succ : forall x, even (S x) = negb (even x).
Proof.
unfold even.
intro x; rewrite recursion_succ; f_equiv'.
Qed.

(*****************************************************)
(**                Division by 2                     *)

Definition half_aux (x : N.t) : N.t * N.t :=
  recursion (0, 0) (fun _ p => let (x1, x2) := p in (S x2, x1)) x.

Definition half (x : N.t) := snd (half_aux x).

Instance half_aux_wd : Proper (N.eq ==> N.eq*N.eq) half_aux.
Proof.
intros x x' Hx. unfold half_aux.
f_equiv; trivial.
intros y y' Hy (u,v) (u',v') (Hu,Hv). compute in *.
rewrite Hu, Hv; auto with *.
Qed.

Instance half_wd : Proper (N.eq==>N.eq) half.
Proof.
unfold half. f_equiv'.
Qed.

Lemma half_aux_0 : half_aux 0 = (0,0).
Proof.
unfold half_aux. rewrite recursion_0; auto.
Qed.

Lemma half_aux_succ : forall x,
 half_aux (S x) = (S (snd (half_aux x)), fst (half_aux x)).
Proof.
intros.
remember (half_aux x) as h.
destruct h as (f,s); simpl in *.
unfold half_aux in *.
rewrite recursion_succ, <- Heqh; simpl; f_equiv'.
Qed.

Theorem half_aux_spec : forall n,
 n == fst (half_aux n) + snd (half_aux n).
Proof.
apply induction.
intros x x' Hx. setoid_rewrite Hx; auto with *.
rewrite half_aux_0; simpl; rewrite add_0_l; auto with *.
intros.
rewrite half_aux_succ. simpl.
rewrite add_succ_l, add_comm; auto.
now f_equiv.
Qed.

Theorem half_aux_spec2 : forall n,
 fst (half_aux n) == snd (half_aux n) \/
 fst (half_aux n) == S (snd (half_aux n)).
Proof.
apply induction.
intros x x' Hx. setoid_rewrite Hx; auto with *.
rewrite half_aux_0; simpl. auto with *.
intros.
rewrite half_aux_succ; simpl.
destruct H; auto with *.
right; now f_equiv.
Qed.

Theorem half_0 : half 0 == 0.
Proof.
unfold half. rewrite half_aux_0; simpl; auto with *.
Qed.

Theorem half_1 : half 1 == 0.
Proof.
unfold half. rewrite one_succ, half_aux_succ, half_aux_0; simpl; auto with *.
Qed.

Theorem half_double : forall n,
 n == 2 * half n \/ n == 1 + 2 * half n.
Proof.
intros. unfold half.
nzsimpl'.
destruct (half_aux_spec2 n) as [H|H]; [left|right].
rewrite <- H at 1. apply half_aux_spec.
rewrite <- add_succ_l. rewrite <- H at 1. apply half_aux_spec.
Qed.

Theorem half_upper_bound : forall n, 2 * half n <= n.
Proof.
intros.
destruct (half_double n) as [E|E]; rewrite E at 2.
apply le_refl.
nzsimpl.
apply le_le_succ_r, le_refl.
Qed.

Theorem half_lower_bound : forall n, n <= 1 + 2 * half n.
Proof.
intros.
destruct (half_double n) as [E|E]; rewrite E at 1.
nzsimpl.
apply le_le_succ_r, le_refl.
apply le_refl.
Qed.

Theorem half_nz : forall n, 1 < n -> 0 < half n.
Proof.
intros n LT.
assert (LE : 0 <= half n) by apply le_0_l.
le_elim LE; auto.
destruct (half_double n) as [E|E];
 rewrite <- LE, mul_0_r, ?add_0_r in E; rewrite E in LT.
order'.
order.
Qed.

Theorem half_decrease : forall n, 0 < n -> half n < n.
Proof.
intros n LT.
destruct (half_double n) as [E|E]; rewrite E at 2; nzsimpl'.
rewrite <- add_0_l at 1.
rewrite <- add_lt_mono_r.
assert (LE : 0 <= half n) by apply le_0_l.
le_elim LE; auto.
rewrite <- LE, mul_0_r in E. rewrite E in LT. destruct (nlt_0_r _ LT).
rewrite <- add_succ_l.
rewrite <- add_0_l at 1.
rewrite <- add_lt_mono_r.
apply lt_0_succ.
Qed.


(*****************************************************)
(**            Power                                 *)

Definition pow (n m : N.t) := recursion 1 (fun _ r => n*r) m.

Local Infix "^^" := pow (at level 30, right associativity).

Instance pow_wd : Proper (N.eq==>N.eq==>N.eq) pow.
Proof.
unfold pow. f_equiv'.
Qed.

Lemma pow_0 : forall n, n^^0 == 1.
Proof.
intros. unfold pow. rewrite recursion_0. auto with *.
Qed.

Lemma pow_succ : forall n m, n^^(S m) == n*(n^^m).
Proof.
intros. unfold pow. rewrite recursion_succ; f_equiv'.
Qed.


(*****************************************************)
(**            Logarithm for the base 2              *)

Definition log (x : N.t) : N.t :=
strong_rec 0
           (fun g x =>
              if x << 2 then 0
              else S (g (half x)))
           x.

Instance log_prewd :
 Proper ((N.eq==>N.eq)==>N.eq==>N.eq)
   (fun g x => if x<<2 then 0 else S (g (half x))).
Proof.
intros g g' Hg n n' Hn.
rewrite Hn.
destruct (n' << 2); auto with *.
f_equiv. apply Hg. now f_equiv.
Qed.

Instance log_wd : Proper (N.eq==>N.eq) log.
Proof.
intros x x' Exx'. unfold log.
apply strong_rec_wd; f_equiv'.
Qed.

Lemma log_good_step : forall n h1 h2,
 (forall m, m < n -> h1 m == h2 m) ->
  (if n << 2 then 0 else S (h1 (half n))) ==
  (if n << 2 then 0 else S (h2 (half n))).
Proof.
intros n h1 h2 E.
destruct (n<<2) eqn:H.
auto with *.
f_equiv. apply E, half_decrease.
rewrite two_succ, <- not_true_iff_false, ltb_lt, nlt_ge, le_succ_l in H.
order'.
Qed.
Hint Resolve log_good_step.

Theorem log_init : forall n, n < 2 -> log n == 0.
Proof.
intros n Hn. unfold log. rewrite strong_rec_fixpoint; auto with *.
replace (n << 2) with true; auto with *.
symmetry. now rewrite ltb_lt.
Qed.

Theorem log_step : forall n, 2 <= n -> log n == S (log (half n)).
Proof.
intros n Hn. unfold log. rewrite strong_rec_fixpoint; auto with *.
replace (n << 2) with false; auto with *.
symmetry. rewrite <- not_true_iff_false, ltb_lt, nlt_ge; auto.
Qed.

Theorem pow2_log : forall n, 0 < n -> half n < 2^^(log n) <= n.
Proof.
intro n; generalize (le_refl n). set (k:=n) at -2. clearbody k.
revert k. pattern n. apply induction; clear n.
intros n n' Hn; setoid_rewrite Hn; auto with *.
intros k Hk1 Hk2.
 le_elim Hk1. destruct (nlt_0_r _ Hk1).
 rewrite Hk1 in Hk2. destruct (nlt_0_r _ Hk2).

intros n IH k Hk1 Hk2.
destruct (lt_ge_cases k 2) as [LT|LE].
(* base *)
rewrite log_init, pow_0 by auto.
rewrite <- le_succ_l, <- one_succ in Hk2.
le_elim Hk2.
rewrite two_succ, <- nle_gt, le_succ_l in LT. destruct LT; auto.
rewrite <- Hk2.
rewrite half_1; auto using lt_0_1, le_refl.
(* step *)
rewrite log_step, pow_succ by auto.
rewrite two_succ, le_succ_l in LE.
destruct (IH (half k)) as (IH1,IH2).
 rewrite <- lt_succ_r. apply lt_le_trans with k; auto.
  now apply half_decrease.
 apply half_nz; auto.
set (K:=2^^log (half k)) in *; clearbody K.
split.
rewrite <- le_succ_l in IH1.
apply mul_le_mono_l with (p:=2) in IH1.
eapply lt_le_trans; eauto.
nzsimpl'.
rewrite lt_succ_r.
eapply le_trans; [ eapply half_lower_bound | ].
nzsimpl'; apply le_refl.
eapply le_trans; [ | eapply half_upper_bound ].
apply mul_le_mono_l; auto.
Qed.

End NdefOpsProp.

