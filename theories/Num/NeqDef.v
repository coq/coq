(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(** DisEquality is defined as the negation of equality *)

Require Params.
Require EqParams.
Require EqAxioms.

Definition neq : N -> N -> Prop := [x,y] ~(x=y).
Infix 6 "<>" neq V8only 70.

(* Proofs of axioms *)
Lemma eq_not_neq : (x,y:N)x=y->~(x<>y).
Unfold neq; Auto with num.
Qed.
Hints Immediate eq_not_neq : num.

Lemma neq_sym : (x,y:N)(x<>y)->(y<>x).
Unfold neq; Auto with num.
Qed.
Hints Resolve neq_sym : num.

Lemma neq_not_neq_trans : (x,y,z:N)(x<>y)->~(y<>z)->(x<>z).
Unfold neq; EAuto with num.
Qed.
Hints Resolve neq_not_neq_trans : num.




