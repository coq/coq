(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)


Require Import BinPos BinNat.

Local Open Scope N_scope.

Definition NPgeb (a:N)(b:positive) :=
  match a with
   | 0 => false
   | Npos na => match Pcompare na b Eq with Lt => false | _ => true end
  end.

Local Notation "a >=? b" := (NPgeb a b) (at level 70).

Fixpoint Pdiv_eucl (a b:positive) : N * N :=
  match a with
    | xH =>
       match b with xH => (1, 0) | _ => (0, 1) end
    | xO a' =>
       let (q, r) := Pdiv_eucl a' b in
       let r' := 2 * r in
        if r' >=? b then (2 * q + 1, r' - Npos b)
        else (2 * q, r')
    | xI a' =>
       let (q, r) := Pdiv_eucl a' b in
       let r' := 2 * r + 1 in
        if r' >=? b then (2 * q + 1, r' - Npos b)
        else  (2 * q, r')
  end.

Definition Ndiv_eucl (a b:N) : N * N :=
  match a, b with
   | 0,  _ => (0, 0)
   | _, 0  => (0, a)
   | Npos na, Npos nb => Pdiv_eucl na nb
  end.

Definition Ndiv a b := fst (Ndiv_eucl a b).
Definition Nmod a b := snd (Ndiv_eucl a b).

Infix "/" := Ndiv : N_scope.
Infix "mod" := Nmod (at level 40, no associativity) : N_scope.

(** Auxiliary Results about [NPgeb] *)

Lemma NPgeb_ge : forall a b, NPgeb a b = true -> a >= Npos b.
Proof.
 destruct a; simpl; intros.
 discriminate.
 unfold Nge, Ncompare. now destruct Pcompare.
Qed.

Lemma NPgeb_lt : forall a b, NPgeb a b = false -> a < Npos b.
Proof.
 destruct a; simpl; intros. red; auto.
 unfold Nlt, Ncompare. now destruct Pcompare.
Qed.

Theorem NPgeb_correct: forall (a:N)(b:positive),
  if NPgeb a b then a = a - Npos b + Npos b else True.
Proof.
  destruct a as [|a]; simpl; intros b; auto.
  generalize (Pcompare_Eq_eq a b).
  case_eq (Pcompare a b Eq); intros; auto.
  rewrite H0; auto.
  now rewrite Pminus_mask_diag.
  destruct (Pminus_mask_Gt a b H) as [d [H2 [H3 _]]].
  rewrite H2. rewrite <- H3.
  simpl; f_equal; apply Pplus_comm.
Qed.

Lemma NPgeb_ineq0 : forall a p, a < Npos p -> NPgeb (2*a) p = true ->
 2*a - Npos p < Npos p.
Proof.
intros a p LT GE.
apply Nplus_lt_cancel_l with (Npos p).
rewrite Nplus_comm.
generalize (NPgeb_correct (2*a) p). rewrite GE. intros <-.
rewrite <- (Nmult_1_l (Npos p)). rewrite <- Nmult_plus_distr_r.
destruct a; auto.
Qed.

Lemma NPgeb_ineq1 : forall a p, a < Npos p -> NPgeb (2*a+1) p = true ->
  (2*a+1) - Npos p < Npos p.
Proof.
intros a p LT GE.
apply Nplus_lt_cancel_l with (Npos p).
rewrite Nplus_comm.
generalize (NPgeb_correct (2*a+1) p). rewrite GE. intros <-.
rewrite <- (Nmult_1_l (Npos p)). rewrite <- Nmult_plus_distr_r.
destruct a; auto.
red; simpl. apply Pcompare_eq_Lt; auto.
Qed.

(* Proofs of specifications for these euclidean divisions. *)

Theorem Pdiv_eucl_correct: forall a b,
  let (q,r) := Pdiv_eucl a b in Npos a = q * Npos b + r.
Proof.
  induction a; cbv beta iota delta [Pdiv_eucl]; fold Pdiv_eucl; cbv zeta.
  intros b; generalize (IHa b); case Pdiv_eucl.
    intros q1 r1 Hq1.
    assert (Npos a~1 = 2*q1*Npos b + (2*r1+1))
     by now rewrite Nplus_assoc, <- Nmult_assoc, <- Nmult_plus_distr_l, <- Hq1.
    generalize (NPgeb_correct (2 * r1 + 1) b); case NPgeb; intros H'; auto.
    rewrite Nmult_plus_distr_r, Nmult_1_l.
    rewrite <- Nplus_assoc, (Nplus_comm (Npos b)), <- H'; auto.
  intros b; generalize (IHa b); case Pdiv_eucl.
    intros q1 r1 Hq1.
    assert (Npos a~0 = 2*q1*Npos b + 2*r1)
     by now rewrite <- Nmult_assoc, <- Nmult_plus_distr_l, <- Hq1.
    generalize (NPgeb_correct (2 * r1) b); case NPgeb; intros H'; auto.
    rewrite Nmult_plus_distr_r, Nmult_1_l.
    rewrite <- Nplus_assoc, (Nplus_comm (Npos b)), <- H'; auto.
  destruct b; auto.
Qed.

Theorem Ndiv_eucl_correct: forall a b,
  let (q,r) := Ndiv_eucl a b in a = b * q + r.
Proof.
  destruct a as [|a]; destruct b as [|b]; simpl; auto.
  generalize (Pdiv_eucl_correct a b); case Pdiv_eucl; intros q r.
  destruct q. simpl; auto. rewrite Nmult_comm. intro EQ; exact EQ.
Qed.

Theorem Ndiv_mod_eq : forall a b,
  a = b * (a/b) + (a mod b).
Proof.
  intros; generalize (Ndiv_eucl_correct a b).
  unfold Ndiv, Nmod; destruct Ndiv_eucl; simpl; auto.
Qed.

Theorem Pdiv_eucl_remainder : forall a b:positive,
  snd (Pdiv_eucl a b) < Npos b.
Proof.
  induction a; cbv beta iota delta [Pdiv_eucl]; fold Pdiv_eucl; cbv zeta.
  intros b; generalize (IHa b); case Pdiv_eucl.
    intros q1 r1 Hr1; simpl in Hr1.
    case_eq (NPgeb (2*r1+1) b); intros; unfold snd.
    apply NPgeb_ineq1; auto.
    apply NPgeb_lt; auto.
  intros b; generalize (IHa b); case Pdiv_eucl.
    intros q1 r1 Hr1; simpl in Hr1.
    case_eq (NPgeb (2*r1) b); intros; unfold snd.
    apply NPgeb_ineq0; auto.
    apply NPgeb_lt; auto.
  destruct b; simpl; reflexivity.
Qed.

Theorem Nmod_lt : forall (a b:N), b<>0 -> a mod b < b.
Proof.
  destruct b as [ |b]; intro H; try solve [elim H;auto].
  destruct a as [ |a]; try solve [compute;auto]; unfold Nmod, Ndiv_eucl.
  generalize (Pdiv_eucl_remainder a b); destruct Pdiv_eucl; simpl; auto.
Qed.
