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

Require Import Bool. (* To get the orb and negb function *)
Require Export NStrongRec.

Module NdefOpsPropFunct (Import NAxiomsMod : NAxiomsSig).
Module Export NStrongRecPropMod := NStrongRecPropFunct NAxiomsMod.
Open Local Scope NatScope.

(*****************************************************)
(**                   Addition                       *)

Definition def_add (x y : N) := recursion y (fun _ p => S p) x.

Infix Local "++" := def_add (at level 50, left associativity).

Add Morphism def_add with signature Neq ==> Neq ==> Neq as def_add_wd.
Proof.
unfold def_add.
intros x x' Exx' y y' Eyy'.
apply recursion_wd with (Aeq := Neq).
assumption.
unfold fun2_eq; intros _ _ _ p p' Epp'; now rewrite Epp'.
assumption.
Qed.

Theorem def_add_0_l : forall y : N, 0 ++ y == y.
Proof.
intro y. unfold def_add. now rewrite recursion_0.
Qed.

Theorem def_add_succ_l : forall x y : N, S x ++ y == S (x ++ y).
Proof.
intros x y; unfold def_add.
rewrite (@recursion_succ N Neq); try reflexivity.
unfold fun2_wd. intros _ _ _ m1 m2 H2. now rewrite H2.
Qed.

Theorem def_add_add : forall n m : N, n ++ m == n + m.
Proof.
intros n m; induct n.
now rewrite def_add_0_l, add_0_l.
intros n H. now rewrite def_add_succ_l, add_succ_l, H.
Qed.

(*****************************************************)
(**                  Multiplication                  *)

Definition def_mul (x y : N) := recursion 0 (fun _ p => p ++ x) y.

Infix Local "**" := def_mul (at level 40, left associativity).

Lemma def_mul_step_wd : forall x : N, fun2_wd Neq Neq Neq (fun _ p => def_add p x).
Proof.
unfold fun2_wd. intros. now apply def_add_wd.
Qed.

Lemma def_mul_step_equal :
  forall x x' : N, x == x' ->
    fun2_eq Neq Neq Neq (fun _ p => def_add p x) (fun x p => def_add p x').
Proof.
unfold fun2_eq; intros; apply def_add_wd; assumption.
Qed.

Add Morphism def_mul with signature Neq ==> Neq ==> Neq as def_mul_wd.
Proof.
unfold def_mul.
intros x x' Exx' y y' Eyy'.
apply recursion_wd with (Aeq := Neq).
reflexivity. apply def_mul_step_equal. assumption. assumption.
Qed.

Theorem def_mul_0_r : forall x : N, x ** 0 == 0.
Proof.
intro. unfold def_mul. now rewrite recursion_0.
Qed.

Theorem def_mul_succ_r : forall x y : N, x ** S y == x ** y ++ x.
Proof.
intros x y; unfold def_mul.
now rewrite (@recursion_succ N Neq); [| apply def_mul_step_wd |].
Qed.

Theorem def_mul_mul : forall n m : N, n ** m == n * m.
Proof.
intros n m; induct m.
now rewrite def_mul_0_r, mul_0_r.
intros m IH; now rewrite def_mul_succ_r, mul_succ_r, def_add_add, IH.
Qed.

(*****************************************************)
(**                     Order                        *)

Definition def_ltb (m : N) : N -> bool :=
recursion
  (if_zero false true)
  (fun _ f => fun n => recursion false (fun n' _ => f n') n)
  m.

Infix Local "<<" := def_ltb (at level 70, no associativity).

Lemma lt_base_wd : fun_wd Neq (@eq bool) (if_zero false true).
unfold fun_wd; intros; now apply if_zero_wd.
Qed.

Lemma lt_step_wd :
fun2_wd Neq (fun_eq Neq (@eq bool)) (fun_eq Neq (@eq bool))
  (fun _ f => fun n => recursion false (fun n' _ => f n') n).
Proof.
unfold fun2_wd, fun_eq.
intros x x' Exx' f f' Eff' y y' Eyy'.
apply recursion_wd with (Aeq := @eq bool).
reflexivity.
unfold fun2_eq; intros; now apply Eff'.
assumption.
Qed.

Lemma lt_curry_wd :
  forall m m' : N, m == m' -> fun_eq Neq (@eq bool) (def_ltb m) (def_ltb m').
Proof.
unfold def_ltb.
intros m m' Emm'.
apply recursion_wd with (Aeq := fun_eq Neq (@eq bool)).
apply lt_base_wd.
apply lt_step_wd.
assumption.
Qed.

Add Morphism def_ltb with signature Neq ==> Neq ==> (@eq bool) as def_ltb_wd.
Proof.
intros; now apply lt_curry_wd.
Qed.

Theorem def_ltb_base : forall n : N, 0 << n = if_zero false true n.
Proof.
intro n; unfold def_ltb; now rewrite recursion_0.
Qed.

Theorem def_ltb_step :
  forall m n : N, S m << n = recursion false (fun n' _ => m << n') n.
Proof.
intros m n; unfold def_ltb.
pose proof
  (@recursion_succ
    (N -> bool)
    (fun_eq Neq (@eq bool))
    (if_zero false true)
    (fun _ f => fun n => recursion false (fun n' _ => f n') n)
    lt_base_wd
    lt_step_wd
    m n n) as H.
now rewrite H.
Qed.

(* Above, we rewrite applications of function. Is it possible to rewrite
functions themselves, i.e., rewrite (recursion lt_base lt_step (S n)) to
lt_step n (recursion lt_base lt_step n)? *)

Theorem def_ltb_0 : forall n : N, n << 0 = false.
Proof.
cases n.
rewrite def_ltb_base; now rewrite if_zero_0.
intro n; rewrite def_ltb_step. now rewrite recursion_0.
Qed.

Theorem def_ltb_0_succ : forall n : N, 0 << S n = true.
Proof.
intro n; rewrite def_ltb_base; now rewrite if_zero_succ.
Qed.

Theorem succ_def_ltb_mono : forall n m : N, (S n << S m) = (n << m).
Proof.
intros n m.
rewrite def_ltb_step. rewrite (@recursion_succ bool (@eq bool)); try reflexivity.
unfold fun2_wd; intros; now apply def_ltb_wd.
Qed.

Theorem def_ltb_lt : forall n m : N, n << m = true <-> n < m.
Proof.
double_induct n m.
cases m.
rewrite def_ltb_0. split; intro H; [discriminate H | false_hyp H nlt_0_r].
intro n. rewrite def_ltb_0_succ. split; intro; [apply lt_0_succ | reflexivity].
intro n. rewrite def_ltb_0. split; intro H; [discriminate | false_hyp H nlt_0_r].
intros n m. rewrite succ_def_ltb_mono. now rewrite <- succ_lt_mono.
Qed.

(*
(*****************************************************)
(**                     Even                         *)

Definition even (x : N) := recursion true (fun _ p => negb p) x.

Lemma even_step_wd : fun2_wd Neq (@eq bool) (@eq bool) (fun x p => if p then false else true).
Proof.
unfold fun2_wd.
intros x x' Exx' b b' Ebb'.
unfold eq_bool; destruct b; destruct b'; now simpl.
Qed.

Add Morphism even with signature Neq ==> (@eq bool) as even_wd.
Proof.
unfold even; intros.
apply recursion_wd with (A := bool) (Aeq := (@eq bool)).
now unfold eq_bool.
unfold fun2_eq. intros _ _ _ b b' Ebb'. unfold eq_bool; destruct b; destruct b'; now simpl.
assumption.
Qed.

Theorem even_0 : even 0 = true.
Proof.
unfold even.
now rewrite recursion_0.
Qed.

Theorem even_succ : forall x : N, even (S x) = negb (even x).
Proof.
unfold even.
intro x; rewrite (recursion_succ (@eq bool)); try reflexivity.
unfold fun2_wd.
intros _ _ _ b b' Ebb'. destruct b; destruct b'; now simpl.
Qed.

(*****************************************************)
(**                Division by 2                     *)

Definition half_aux (x : N) : N * N :=
  recursion (0, 0) (fun _ p => let (x1, x2) := p in ((S x2, x1))) x.

Definition half (x : N) := snd (half_aux x).

Definition E2 := prod_rel Neq Neq.

Add Relation (prod N N) E2
reflexivity proved by (prod_rel_refl N N Neq Neq E_equiv E_equiv)
symmetry proved by (prod_rel_symm N N Neq Neq E_equiv E_equiv)
transitivity proved by (prod_rel_trans N N Neq Neq E_equiv E_equiv)
as E2_rel.

Lemma half_step_wd: fun2_wd Neq E2 E2 (fun _ p => let (x1, x2) := p in ((S x2, x1))).
Proof.
unfold fun2_wd, E2, prod_rel.
intros _ _ _ p1 p2 [H1 H2].
destruct p1; destruct p2; simpl in *.
now split; [rewrite H2 |].
Qed.

Add Morphism half with signature Neq ==> Neq as half_wd.
Proof.
unfold half.
assert (H: forall x y, x == y -> E2 (half_aux x) (half_aux y)).
intros x y Exy; unfold half_aux; apply recursion_wd with (Aeq := E2); unfold E2.
unfold E2.
unfold prod_rel; simpl; now split.
unfold fun2_eq, prod_rel; simpl.
intros _ _ _ p1 p2; destruct p1; destruct p2; simpl.
intros [H1 H2]; split; [rewrite H2 | assumption]. reflexivity. assumption.
unfold E2, prod_rel in H. intros x y Exy; apply H in Exy.
exact (proj2 Exy).
Qed.

(*****************************************************)
(**            Logarithm for the base 2              *)

Definition log (x : N) : N :=
strong_rec 0
           (fun x g =>
              if (e x 0) then 0
              else if (e x 1) then 0
              else S (g (half x)))
           x.

Add Morphism log with signature Neq ==> Neq as log_wd.
Proof.
intros x x' Exx'. unfold log.
apply strong_rec_wd with (Aeq := Neq); try (reflexivity || assumption).
unfold fun2_eq. intros y y' Eyy' g g' Egg'.
assert (H : e y 0 = e y' 0); [now apply e_wd|].
rewrite <- H; clear H.
assert (H : e y 1 = e y' 1); [now apply e_wd|].
rewrite <- H; clear H.
assert (H : S (g (half y)) == S (g' (half y')));
[apply succ_wd; apply Egg'; now apply half_wd|].
now destruct (e y 0); destruct (e y 1).
Qed.
*)
End NdefOpsPropFunct.

