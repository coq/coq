(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import ZArithRing.
Require Import ZArith_base.
Require Export Omega.
Require Import Wf_nat.
Local Open Scope Z_scope.


(**********************************************************************)
(** About parity *)

Notation two_or_two_plus_one := Z_modulo_2 (only parsing).

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
 unfold floor. induction p; simpl.
 - rewrite !Pos2Z.inj_xI, (Pos2Z.inj_xO (xO _)), Pos2Z.inj_xO. omega.
 - rewrite (Pos2Z.inj_xO (xO _)), (Pos2Z.inj_xO p), Pos2Z.inj_xO. omega.
 - omega.
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
    (destruct (Zabs_dec p) as [-> | ->]; elim H; auto with zarith).
  apply (Z_lt_rec Q); auto with zarith.
  subst Q; intros x H.
  split; apply HP.
  - rewrite Z.abs_eq; auto; intros.
    destruct (H (Z.abs m)); auto with zarith.
    destruct (Zabs_dec m) as [-> | ->]; trivial.
  - rewrite Z.abs_neq, Z.opp_involutive; auto with zarith; intros.
    destruct (H (Z.abs m)); auto with zarith.
    destruct (Zabs_dec m) as [-> | ->]; trivial.
Qed.

Theorem Z_lt_abs_induction :
  forall P:Z -> Prop,
    (forall n:Z, (forall m:Z, Z.abs m < Z.abs n -> P m) -> P n) ->
    forall n:Z, P n.
Proof.
  intros P HP p.
  set (Q := fun z => 0 <= z -> P z /\ P (- z)) in *.
  enough (Q (Z.abs p)) by
    (destruct (Zabs_dec p) as [-> | ->]; elim H; auto with zarith).
  apply (Z_lt_induction Q); auto with zarith.
  subst Q; intros.
  split; apply HP.
  - rewrite Z.abs_eq; auto; intros.
    elim (H (Z.abs m)); intros; auto with zarith.
    elim (Zabs_dec m); intro eq; rewrite eq; trivial.
  - rewrite Z.abs_neq, Z.opp_involutive; auto with zarith; intros.
    destruct (H (Z.abs m)); auto with zarith.
    destruct (Zabs_dec m) as [-> | ->]; trivial.
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
    clear l. induction l.
    auto with zarith.
    intros. simpl length; simpl Zlength_aux.
     rewrite IHl, Nat2Z.inj_succ; auto with zarith.
    unfold Zlength. now rewrite H.
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
