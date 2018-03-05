(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* G. Huet 1-9-95 *)

(** We consider a Set [U], given with a commutative-associative operator [op],
    and a congruence [cong]; we show permutation lemmas *)

Section Axiomatisation.

  Variable U : Type.
  Variable op : U -> U -> U.
  Variable cong : U -> U -> Prop.

  Hypothesis op_comm : forall x y:U, cong (op x y) (op y x).
  Hypothesis op_ass : forall x y z:U, cong (op (op x y) z) (op x (op y z)).

  Hypothesis cong_left : forall x y z:U, cong x y -> cong (op x z) (op y z).
  Hypothesis cong_right : forall x y z:U, cong x y -> cong (op z x) (op z y).
  Hypothesis cong_trans : forall x y z:U, cong x y -> cong y z -> cong x z.
  Hypothesis cong_sym : forall x y:U, cong x y -> cong y x.

  (** Remark. we do not need: [Hypothesis cong_refl : (x:U)(cong x x)]. *)

  Lemma cong_congr :
    forall x y z t:U, cong x y -> cong z t -> cong (op x z) (op y t).
  Proof.
    intros; apply cong_trans with (op y z).
    apply cong_left; trivial.
    apply cong_right; trivial.
  Qed.

  Lemma comm_right : forall x y z:U, cong (op x (op y z)) (op x (op z y)).
  Proof.
    intros; apply cong_right; apply op_comm.
  Qed.

  Lemma comm_left : forall x y z:U, cong (op (op x y) z) (op (op y x) z).
  Proof.
    intros; apply cong_left; apply op_comm.
  Qed.

  Lemma perm_right : forall x y z:U, cong (op (op x y) z) (op (op x z) y).
  Proof.
    intros.
    apply cong_trans with (op x (op y z)).
    apply op_ass.
    apply cong_trans with (op x (op z y)).
    apply cong_right; apply op_comm.
    apply cong_sym; apply op_ass.
  Qed.

  Lemma perm_left : forall x y z:U, cong (op x (op y z)) (op y (op x z)).
  Proof.
    intros.
    apply cong_trans with (op (op x y) z).
    apply cong_sym; apply op_ass.
    apply cong_trans with (op (op y x) z).
    apply cong_left; apply op_comm.
    apply op_ass.
  Qed.

  Lemma op_rotate : forall x y z t:U, cong (op x (op y z)) (op z (op x y)).
  Proof.
    intros; apply cong_trans with (op (op x y) z).
    apply cong_sym; apply op_ass.
    apply op_comm.
  Qed.

  (** Needed for treesort ... *)
  Lemma twist :
    forall x y z t:U, cong (op x (op (op y z) t)) (op (op y (op x t)) z).
  Proof.
    intros.
    apply cong_trans with (op x (op (op y t) z)).
    apply cong_right; apply perm_right.
    apply cong_trans with (op (op x (op y t)) z).
    apply cong_sym; apply op_ass.
    apply cong_left; apply perm_left.
  Qed.

End Axiomatisation.
