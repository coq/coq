(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Export NeqParams.
Require Export NeqAxioms.
Require Export EqParams.
Require Export EqAxioms.


(** This file contains basic properties of disequality *)

Lemma neq_antirefl : (x:N)~(x<>x).
Auto with num.
Qed.
Hints Resolve neq_antirefl : num.

Lemma eq_not_neq_y_x : (x,y:N)(x=y)->~(y<>x).
Intros; Apply eq_not_neq; Auto with num.
Qed.
Hints Immediate eq_not_neq_y_x : num.

Lemma neq_not_eq : (x,y:N)(x<>y)->~(x=y).
Red; Intros; Apply (eq_not_neq x y); Trivial.
Qed.
Hints Immediate neq_not_eq : num.

Lemma neq_not_eq_y_x : (x,y:N)(x<>y)->~(y=x).
Intros; Apply neq_not_eq; Auto with num.
Qed.
Hints Immediate neq_not_eq_y_x : num.

Lemma not_neq_neq_trans : (x,y,z:N)~(x<>y)->(y<>z)->(x<>z).
Intros; Apply neq_sym; Apply neq_not_neq_trans with y; Auto with num.
Qed.
Hints Resolve not_neq_neq_trans : num.

Lemma neq_eq_compat : (x1,x2,y1,y2:N)(x1=y1)->(x2=y2)->(x1<>x2)->(y1<>y2).
Intros.
EAuto with num.
Qed.





