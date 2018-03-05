(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import BinInt.
Local Open Scope Z_scope.

(** An alternative power function for Z *)

(** This [Zpower_alt] is extensionally equal to [Z.pow],
    but not convertible with it. The number of
    multiplications is logarithmic instead of linear, but
    these multiplications are bigger. Experimentally, it seems
    that [Zpower_alt] is slightly quicker than [Z.pow] on average,
    but can be quite slower on powers of 2.
*)

Definition Zpower_alt n m :=
  match m with
    | Z0 => 1
    | Zpos p => Pos.iter_op Z.mul p n
    | Zneg p => 0
  end.

Infix "^^" := Zpower_alt (at level 30, right associativity) : Z_scope.

Lemma Piter_mul_acc : forall f,
 (forall x y:Z, (f x)*y = f (x*y)) ->
 forall p k, Pos.iter f k p = (Pos.iter f 1 p)*k.
Proof.
 intros f Hf.
 induction p; simpl; intros.
 - set (g := Pos.iter f 1 p) in *. now rewrite !IHp, Hf, Z.mul_assoc.
 - set (g := Pos.iter f 1 p) in *. now rewrite !IHp, Z.mul_assoc.
 - now rewrite Hf, Z.mul_1_l.
Qed.

Lemma Piter_op_square : forall p a,
 Pos.iter_op Z.mul p (a*a) = (Pos.iter_op Z.mul p a)*(Pos.iter_op Z.mul p a).
Proof.
 induction p; simpl; intros; trivial. now rewrite IHp, Z.mul_shuffle1.
Qed.

Lemma Zpower_equiv a b : a^^b = a^b.
Proof.
 destruct b as [|p|p]; trivial.
 unfold Zpower_alt, Z.pow, Z.pow_pos.
 revert a.
 induction p; simpl; intros.
 - f_equal.
   rewrite Piter_mul_acc.
   now rewrite Piter_op_square, IHp.
   intros. symmetry; apply Z.mul_assoc.
 - rewrite Piter_mul_acc.
   now rewrite Piter_op_square, IHp.
   intros. symmetry; apply Z.mul_assoc.
 - now Z.nzsimpl.
Qed.

Lemma Zpower_alt_0_r n : n^^0 = 1.
Proof. reflexivity. Qed.

Lemma Zpower_alt_succ_r a b : 0<=b -> a^^(Z.succ b) = a * a^^b.
Proof.
 destruct b as [|b|b]; intros Hb; simpl.
 - now Z.nzsimpl.
 - now rewrite Pos.add_1_r, Pos.iter_op_succ by apply Z.mul_assoc.
 - now elim Hb.
Qed.

Lemma Zpower_alt_neg_r a b : b<0 -> a^^b = 0.
Proof.
 now destruct b.
Qed.

Lemma Zpower_alt_Ppow p q : (Zpos p)^^(Zpos q) = Zpos (p^q).
Proof.
 now rewrite Zpower_equiv, Pos2Z.inj_pow.
Qed.
