(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2011     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

Require Import ZArithRing.
Require Import ZArith_base.
Require Export Omega.
Require Import Wf_nat.
Open Local Scope Z_scope.


(**********************************************************************)
(** About parity *)

Lemma two_or_two_plus_one :
  forall n:Z, {y : Z | n = 2 * y} + {y : Z | n = 2 * y + 1}.
Proof.
  intro x; destruct x.
  left; split with 0; reflexivity.

  destruct p.
  right; split with (Zpos p); reflexivity.

  left; split with (Zpos p); reflexivity.

  right; split with 0; reflexivity.

  destruct p.
  right; split with (Zneg (1 + p)).
  rewrite BinInt.Zneg_xI.
  rewrite BinInt.Zneg_plus_distr.
  omega.

  left; split with (Zneg p); reflexivity.

  right; split with (-1); reflexivity.
Qed.

(**********************************************************************)
(** The biggest power of 2 that is stricly less than [a]

    Easy to compute: replace all "1" of the binary representation by
    "0", except the first "1" (or the first one :-) *)

Fixpoint floor_pos (a:positive) : positive :=
  match a with
    | xH => 1%positive
    | xO a' => xO (floor_pos a')
    | xI b' => xO (floor_pos b')
  end.

Definition floor (a:positive) := Zpos (floor_pos a).

Lemma floor_gt0 : forall p:positive, floor p > 0.
Proof.
  intro.
  compute in |- *.
  trivial.
Qed.

Lemma floor_ok : forall p:positive, floor p <= Zpos p < 2 * floor p.
Proof.
  unfold floor in |- *.
  intro a; induction a as [p| p| ].

  simpl in |- *.
  repeat rewrite BinInt.Zpos_xI.
  rewrite (BinInt.Zpos_xO (xO (floor_pos p))).
  rewrite (BinInt.Zpos_xO (floor_pos p)).
  omega.

  simpl in |- *.
  repeat rewrite BinInt.Zpos_xI.
  rewrite (BinInt.Zpos_xO (xO (floor_pos p))).
  rewrite (BinInt.Zpos_xO (floor_pos p)).
  rewrite (BinInt.Zpos_xO p).
  omega.

  simpl in |- *; omega.
Qed.

(**********************************************************************)
(** Two more induction principles over [Z]. *)

Theorem Z_lt_abs_rec :
  forall P:Z -> Set,
    (forall n:Z, (forall m:Z, Zabs m < Zabs n -> P m) -> P n) ->
    forall n:Z, P n.
Proof.
  intros P HP p.
  set (Q := fun z => 0 <= z -> P z * P (- z)) in *.
  cut (Q (Zabs p)); [ intros | apply (Z_lt_rec Q); auto with zarith ].
  elim (Zabs_dec p); intro eq; rewrite eq; elim H; auto with zarith.
  unfold Q in |- *; clear Q; intros.
  apply pair; apply HP.
  rewrite Zabs_eq; auto; intros.
  elim (H (Zabs m)); intros; auto with zarith.
  elim (Zabs_dec m); intro eq; rewrite eq; trivial.
  rewrite Zabs_non_eq; auto with zarith.
  rewrite Zopp_involutive; intros.
  elim (H (Zabs m)); intros; auto with zarith.
  elim (Zabs_dec m); intro eq; rewrite eq; trivial.
Qed.

Theorem Z_lt_abs_induction :
  forall P:Z -> Prop,
    (forall n:Z, (forall m:Z, Zabs m < Zabs n -> P m) -> P n) ->
    forall n:Z, P n.
Proof.
  intros P HP p.
  set (Q := fun z => 0 <= z -> P z /\ P (- z)) in *.
  cut (Q (Zabs p)); [ intros | apply (Z_lt_induction Q); auto with zarith ].
  elim (Zabs_dec p); intro eq; rewrite eq; elim H; auto with zarith.
  unfold Q in |- *; clear Q; intros.
  split; apply HP.
  rewrite Zabs_eq; auto; intros.
  elim (H (Zabs m)); intros; auto with zarith.
  elim (Zabs_dec m); intro eq; rewrite eq; trivial.
  rewrite Zabs_non_eq; auto with zarith.
  rewrite Zopp_involutive; intros.
  elim (H (Zabs m)); intros; auto with zarith.
  elim (Zabs_dec m); intro eq; rewrite eq; trivial.
Qed.

(** To do case analysis over the sign of [z] *)

Lemma Zcase_sign :
  forall (n:Z) (P:Prop), (n = 0 -> P) -> (n > 0 -> P) -> (n < 0 -> P) -> P.
Proof.
  intros x P Hzero Hpos Hneg.
  induction  x as [| p| p].
  apply Hzero; trivial.
  apply Hpos; apply Zorder.Zgt_pos_0.
  apply Hneg; apply Zorder.Zlt_neg_0.
Qed.

Lemma sqr_pos : forall n:Z, n * n >= 0.
Proof.
  intro x.
  apply (Zcase_sign x (x * x >= 0)).
  intros H; rewrite H; omega.
  intros H; replace 0 with (0 * 0).
  apply Zmult_ge_compat; omega.
  omega.
  intros H; replace 0 with (0 * 0).
  replace (x * x) with (- x * - x).
  apply Zmult_ge_compat; omega.
  ring.
  omega.
Qed.

(**********************************************************************)
(** A list length in Z, tail recursive.  *)

Require Import List.

Fixpoint Zlength_aux (acc:Z) (A:Type) (l:list A) : Z :=
  match l with
    | nil => acc
    | _ :: l => Zlength_aux (Zsucc acc) A l
  end.

Definition Zlength := Zlength_aux 0.
Implicit Arguments Zlength [A].

Section Zlength_properties.

  Variable A : Type.

  Implicit Type l : list A.

  Lemma Zlength_correct : forall l, Zlength l = Z_of_nat (length l).
  Proof.
    assert (forall l (acc:Z), Zlength_aux acc A l = acc + Z_of_nat (length l)).
    simple induction l.
    simpl in |- *; auto with zarith.
    intros; simpl (length (a :: l0)) in |- *; rewrite Znat.inj_S.
    simpl in |- *; rewrite H; auto with zarith.
    unfold Zlength in |- *; intros; rewrite H; auto.
  Qed.

  Lemma Zlength_nil : Zlength (A:=A) nil = 0.
  Proof.
    auto.
  Qed.

  Lemma Zlength_cons : forall (x:A) l, Zlength (x :: l) = Zsucc (Zlength l).
  Proof.
    intros; do 2 rewrite Zlength_correct.
    simpl (length (x :: l)) in |- *; rewrite Znat.inj_S; auto.
  Qed.

  Lemma Zlength_nil_inv : forall l, Zlength l = 0 -> l = nil.
  Proof.
    intro l; rewrite Zlength_correct.
    case l; auto.
    intros x l'; simpl (length (x :: l')) in |- *.
    rewrite Znat.inj_S.
    intros; exfalso; generalize (Zle_0_nat (length l')); omega.
  Qed.

End Zlength_properties.

Implicit Arguments Zlength_correct [A].
Implicit Arguments Zlength_cons [A].
Implicit Arguments Zlength_nil_inv [A].
