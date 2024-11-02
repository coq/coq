(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import ZArithRing.
Require Import BinInt.
Require Import Znat.
Require Import Wf_nat.
Local Open Scope Z_scope.
Require Zabs Wf_Z.
Require Zeven.

(**********************************************************************)
(** About parity *)

#[deprecated(since="9.0")]
Notation two_or_two_plus_one := Zeven.Z_modulo_2 (only parsing).

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
Proof. reflexivity. Qed.

Lemma floor_ok : forall p:positive, floor p <= Zpos p < 2 * floor p.
Proof.
 unfold floor. intros p; induction p as [p [IH1p IH2p]|p [IH1p IH2]|]; simpl.
 - rewrite !Pos2Z.inj_xI, (Pos2Z.inj_xO (xO _)), Pos2Z.inj_xO.
   split.
   + apply Z.le_trans with (2 * Z.pos p); auto using Z.le_succ_diag_r.
   + apply Z.lt_le_trans with (2 * (Z.pos p + 1)).
     * rewrite Z.mul_add_distr_l, Z.mul_1_r.
       apply Z.add_lt_mono_l; reflexivity.
     * apply Z.mul_le_mono_nonneg_l; trivial using Z.le_0_2.
       rewrite Z.add_1_r. apply Z.le_succ_l. trivial.
 - rewrite (Pos2Z.inj_xO (xO _)), (Pos2Z.inj_xO p), Pos2Z.inj_xO.
   split; auto with zarith.
 - split; auto using Z.le_refl, Z.lt_1_2.
Qed.

(**********************************************************************)
(** Two more induction principles over [Z]. *)

Theorem Z_lt_abs_rec :
  forall P:Z -> Set,
    (forall n:Z, (forall m:Z, Z.abs m < Z.abs n -> P m) -> P n) ->
    forall n:Z, P n.
Proof.
  intros P HP p.
  set (Q := fun z => 0 <= z -> P z * P (- z)).
  enough (H:Q (Z.abs p)) by
    (destruct (Zabs.Zabs_dec p) as [-> | ->]; elim H; auto using Z.abs_nonneg ).
  apply (Wf_Z.Z_lt_rec Q); auto using Z.abs_nonneg.
  subst Q; intros x H.
  split; apply HP.
  - rewrite Z.abs_eq; auto; intros m ?.
    destruct (H (Z.abs m)); auto using Z.abs_nonneg.
    destruct (Zabs.Zabs_dec m) as [-> | ->]; trivial.
  - rewrite Z.abs_neq, Z.opp_involutive; [intros m ?|].
    + destruct (H (Z.abs m)); auto using Z.abs_nonneg.
      destruct (Zabs.Zabs_dec m) as [-> | ->]; trivial.
    + apply Z.opp_le_mono; rewrite Z.opp_involutive; auto.
Qed.

Theorem Z_lt_abs_induction :
  forall P:Z -> Prop,
    (forall n:Z, (forall m:Z, Z.abs m < Z.abs n -> P m) -> P n) ->
    forall n:Z, P n.
Proof.
  intros P HP p.
  set (Q := fun z => 0 <= z -> P z /\ P (- z)) in *.
  enough (Q (Z.abs p)) as H by
    (destruct (Zabs.Zabs_dec p) as [-> | ->]; elim H; auto using Z.abs_nonneg).
  apply (Wf_Z.Z_lt_induction Q); auto using Z.abs_nonneg.
  subst Q; intros ? H.
  split; apply HP.
  - rewrite Z.abs_eq; auto; intros m ?.
    elim (H (Z.abs m)); intros; auto using Z.abs_nonneg.
    elim (Zabs.Zabs_dec m); intro eq; rewrite eq; trivial.
  - rewrite Z.abs_neq, Z.opp_involutive; [intros m ?|].
    + destruct (H (Z.abs m)); auto using Z.abs_nonneg.
      destruct (Zabs.Zabs_dec m) as [-> | ->]; trivial.
    + apply Z.opp_le_mono; rewrite Z.opp_involutive; auto.
Qed.

(** To do case analysis over the sign of [z] *)

Lemma Zcase_sign :
  forall (n:Z) (P:Prop), (n = 0 -> P) -> (n > 0 -> P) -> (n < 0 -> P) -> P.
Proof.
  intros x P Hzero Hpos Hneg.
  destruct x; [apply Hzero|apply Hpos|apply Hneg]; easy.
Qed.

Lemma sqr_pos n : n * n >= 0.
Proof.
 Z.swap_greater. apply Z.square_nonneg.
Qed.

(**********************************************************************)
(** A list length in Z, tail recursive.  *)

Require Import List.

Fixpoint Zlength_aux (acc:Z) (A:Type) (l:list A) : Z :=
  match l with
    | nil => acc
    | _ :: l => Zlength_aux (Z.succ acc) A l
  end.

Definition Zlength := Zlength_aux 0.
Arguments Zlength [A] l.

Section Zlength_properties.

  Variable A : Type.

  Implicit Type l : list A.

  Lemma Zlength_correct l : Zlength l = Z.of_nat (length l).
  Proof.
    assert (H : forall l acc, Zlength_aux acc A l = acc + Z.of_nat (length l)).
    - clear l. intros l; induction l as [|? ? IHl].
      + auto using Z.add_0_r.
      + intros. simpl length; simpl Zlength_aux.
        rewrite IHl, Znat.Nat2Z.inj_succ, Z.add_succ_comm; auto.
    - unfold Zlength. now rewrite H.
  Qed.

  Lemma Zlength_nil : Zlength (A:=A) nil = 0.
  Proof. reflexivity. Qed.

  Lemma Zlength_cons (x:A) l : Zlength (x :: l) = Z.succ (Zlength l).
  Proof.
    intros. now rewrite !Zlength_correct, <- Nat2Z.inj_succ.
  Qed.

  Lemma Zlength_nil_inv l : Zlength l = 0 -> l = nil.
  Proof.
    rewrite Zlength_correct.
    destruct l as [|x l]; auto.
    now rewrite <- Nat2Z.inj_0, Nat2Z.inj_iff.
  Qed.

End Zlength_properties.

Arguments Zlength_correct [A] l.
Arguments Zlength_cons [A] x l.
Arguments Zlength_nil_inv [A] l _.
