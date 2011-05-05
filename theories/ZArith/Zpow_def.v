(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import BinInt BinNat Ring_theory.

Local Open Scope Z_scope.

(** [Zpower_pos z n] is the n-th power of [z] when [n] is an binary
      integer (type [positive]) and [z] a signed integer (type [Z]) *)

Notation Zpower_pos := Z.pow_pos (only parsing).
Notation Zpower := Z.pow (only parsing).
Notation Zpower_0_r := Z.pow_0_r (only parsing).
Notation Zpower_succ_r := Z.pow_succ_r (only parsing).
Notation Zpower_neg_r := Z.pow_neg_r (only parsing).

Lemma Zpower_theory : power_theory 1 Zmult (eq (A:=Z)) Z_of_N Zpower.
Proof.
 constructor. intros.
 destruct n;simpl;trivial.
 unfold Zpower_pos.
 rewrite <- (Zmult_1_r (pow_pos _ _ _)). generalize 1.
 induction p; simpl; intros; rewrite ?IHp, ?Zmult_assoc; trivial.
Qed.

Lemma Zpower_Ppow : forall p q, (Zpos p)^(Zpos q) = Zpos (p^q).
Proof.
 intros. unfold Ppow, Zpower, Zpower_pos.
 symmetry. now apply iter_pos_swap_gen.
Qed.

Lemma Zpower_Npow : forall n m,
 (Z_of_N n)^(Z_of_N m) = Z_of_N (n^m).
Proof.
 intros [|n] [|m]; simpl; trivial.
 unfold Zpower_pos. generalize 1. induction m; simpl; trivial.
 apply Zpower_Ppow.
Qed.

(** An alternative Zpower *)

(** This Zpower_alt is extensionnaly equal to Zpower in ZArith,
    but not convertible with it. The number of
    multiplications is logarithmic instead of linear, but
    these multiplications are bigger. Experimentally, it seems
    that Zpower_alt is slightly quicker than Zpower on average,
    but can be quite slower on powers of 2.
*)

Definition Zpower_alt n m :=
  match m with
    | Z0 => 1
    | Zpos p => Piter_op Zmult p n
    | Zneg p => 0
  end.

Infix "^^" := Zpower_alt (at level 30, right associativity) : Z_scope.

Lemma iter_pos_mult_acc : forall f,
 (forall x y:Z, (f x)*y = f (x*y)) ->
 forall p k, iter_pos p _ f k = (iter_pos p _ f 1)*k.
Proof.
 intros f Hf.
 induction p; simpl; intros.
 rewrite IHp. rewrite Hf. f_equal. rewrite (IHp (iter_pos _ _ _ _)).
 rewrite <- Zmult_assoc. f_equal. auto.
 rewrite IHp. rewrite (IHp (iter_pos _ _ _ _)).
 rewrite <- Zmult_assoc. f_equal. auto.
 rewrite Hf. f_equal. now rewrite Zmult_1_l.
Qed.

Lemma Piter_op_square : forall p a,
 Piter_op Zmult p (a*a) = (Piter_op Zmult p a)*(Piter_op Zmult p a).
Proof.
 induction p; simpl; intros; trivial.
 rewrite IHp. rewrite <- !Zmult_assoc. f_equal.
 rewrite Zmult_comm, <- Zmult_assoc.
 f_equal. apply Zmult_comm.
Qed.

Lemma Zpower_equiv : forall a b, a^^b = a^b.
Proof.
 intros a [|p|p]; trivial.
 unfold Zpower_alt, Zpower, Zpower_pos.
 revert a.
 induction p; simpl; intros.
 f_equal.
 rewrite iter_pos_mult_acc.
 now rewrite Piter_op_square, IHp.
 intros. symmetry; apply Zmult_assoc.
 rewrite iter_pos_mult_acc.
 now rewrite Piter_op_square, IHp.
 intros. symmetry; apply Zmult_assoc.
 now rewrite Zmult_1_r.
Qed.

Lemma Zpower_alt_0_r : forall n, n^^0 = 1.
Proof. reflexivity. Qed.

Lemma Zpower_alt_succ_r : forall a b, 0<=b -> a^^(Zsucc b) = a * a^^b.
Proof.
 intros a [|b|b] Hb; [ | |now elim Hb]; simpl.
 now rewrite Zmult_1_r.
 rewrite <- Pplus_one_succ_r. apply Piter_op_succ. apply Zmult_assoc.
Qed.

Lemma Zpower_alt_neg_r : forall a b, b<0 -> a^^b = 0.
Proof.
 now destruct b.
Qed.

Lemma Zpower_alt_Ppow : forall p q, (Zpos p)^^(Zpos q) = Zpos (p^q).
Proof.
 intros. now rewrite Zpower_equiv, Zpower_Ppow.
Qed.
