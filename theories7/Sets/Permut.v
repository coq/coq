(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(* G. Huet 1-9-95 *)

(** We consider a Set [U], given with a commutative-associative operator [op],
    and a congruence [cong]; we show permutation lemmas *)

Section Axiomatisation.

Variable U: Set.

Variable op: U -> U -> U.

Variable cong : U -> U -> Prop.

Hypothesis op_comm : (x,y:U)(cong (op x y) (op y x)).
Hypothesis op_ass  : (x,y,z:U)(cong (op (op x y) z) (op x (op y z))).

Hypothesis cong_left :  (x,y,z:U)(cong x y)->(cong (op x z) (op y z)).
Hypothesis cong_right : (x,y,z:U)(cong x y)->(cong (op z x) (op z y)).
Hypothesis cong_trans : (x,y,z:U)(cong x y)->(cong y z)->(cong x z).
Hypothesis cong_sym : (x,y:U)(cong x y)->(cong y x).

(** Remark. we do not need: [Hypothesis cong_refl : (x:U)(cong x x)]. *)

Lemma cong_congr :
 (x,y,z,t:U)(cong x y)->(cong z t)->(cong (op x z) (op y t)).
Proof.
Intros; Apply cong_trans with (op y z).
Apply cong_left; Trivial.
Apply cong_right; Trivial.
Qed.

Lemma comm_right : (x,y,z:U)(cong (op x (op y z)) (op x (op z y))).
Proof.
Intros; Apply cong_right; Apply op_comm.
Qed.

Lemma comm_left : (x,y,z:U)(cong (op (op x y) z) (op (op y x) z)).
Proof.
Intros; Apply cong_left; Apply op_comm.
Qed.

Lemma perm_right : (x,y,z:U)(cong (op (op x y) z) (op (op x z) y)).
Proof.
Intros.
Apply cong_trans with (op x (op y z)).
Apply op_ass.
Apply cong_trans with (op x (op z y)). 
Apply cong_right; Apply op_comm.
Apply cong_sym; Apply op_ass.
Qed.

Lemma perm_left : (x,y,z:U)(cong (op x (op y z)) (op y (op x z))).
Proof.
Intros.
Apply cong_trans with (op (op x y) z).
Apply cong_sym; Apply op_ass.
Apply cong_trans with (op (op y x) z).
Apply cong_left; Apply op_comm.
Apply op_ass.
Qed.

Lemma op_rotate : (x,y,z,t:U)(cong (op x (op y z)) (op z (op x y))).
Proof.
Intros; Apply cong_trans with (op (op x y) z).
Apply cong_sym; Apply op_ass.
Apply op_comm.
Qed.

(* Needed for treesort ... *)
Lemma twist : (x,y,z,t:U)
   (cong (op x (op (op y z) t)) (op (op y (op x t)) z)).
Proof.
Intros.
Apply cong_trans with (op x (op (op y t) z)).
Apply cong_right; Apply perm_right.
Apply cong_trans with (op (op x (op y t)) z).
Apply cong_sym; Apply op_ass.
Apply cong_left; Apply perm_left.
Qed.

End Axiomatisation.
