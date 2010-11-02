(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import BinInt Zmisc Ring_theory.

Local Open Scope Z_scope.

(** [Zpower_pos z n] is the n-th power of [z] when [n] is an binary
      integer (type [positive]) and [z] a signed integer (type [Z]) *)

Definition Zpower_pos (z:Z) (n:positive) :=
 iter_pos n Z (fun x:Z => z * x) 1.

Definition Zpower (x y:Z) :=
    match y with
      | Zpos p => Zpower_pos x p
      | Z0 => 1
      | Zneg p => 0
    end.

Infix "^" := Zpower : Z_scope.

Lemma Zpower_0_r : forall n, n^0 = 1.
Proof. reflexivity. Qed.

Lemma Zpower_succ_r : forall a b, 0<=b -> a^(Zsucc b) = a * a^b.
Proof.
 intros a [|b|b] Hb; [ | |now elim Hb]; simpl.
 reflexivity.
 unfold Zpower_pos. now rewrite Pplus_comm, iter_pos_plus.
Qed.

Lemma Zpower_neg_r : forall a b, b<0 -> a^b = 0.
Proof.
 now destruct b.
Qed.

Lemma Zpower_theory : power_theory 1 Zmult (eq (A:=Z)) Z_of_N Zpower.
Proof.
 constructor. intros.
 destruct n;simpl;trivial.
 unfold Zpower_pos.
 rewrite <- (Zmult_1_r (pow_pos _ _ _)). generalize 1.
 induction p; simpl; intros; rewrite ?IHp, ?Zmult_assoc; trivial.
Qed.

(** An alternative Zpower *)

(** This Zpower_opt is extensionnaly equal to Zpower in ZArith,
    but not convertible with it, and quicker : the number of
    multiplications is logarithmic instead of linear.

    TODO: We should try someday to replace Zpower with this Zpower_opt.
*)

Definition Zpower_opt n m :=
  match m with
    | Z0 => 1
    | Zpos p => Piter_op Zmult p n
    | Zneg p => 0
  end.

Infix "^^" := Zpower_opt (at level 30, right associativity) : Z_scope.

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
 unfold Zpower_opt, Zpower, Zpower_pos.
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

Lemma Zpower_opt_0_r : forall n, n^^0 = 1.
Proof. reflexivity. Qed.

Lemma Zpower_opt_succ_r : forall a b, 0<=b -> a^^(Zsucc b) = a * a^^b.
Proof.
 intros a [|b|b] Hb; [ | |now elim Hb]; simpl.
 now rewrite Zmult_1_r.
 rewrite <- Pplus_one_succ_r. apply Piter_op_succ. apply Zmult_assoc.
Qed.

Lemma Zpower_opt_neg_r : forall a b, b<0 -> a^^b = 0.
Proof.
 now destruct b.
Qed.
