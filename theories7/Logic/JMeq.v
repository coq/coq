(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(** John Major's Equality as proposed by C. Mc Bride *)

Set Implicit Arguments.

Inductive JMeq [A:Set;x:A] : (B:Set)B->Prop := 
	JMeq_refl : (JMeq x x).
Reset JMeq_ind.

Hints Resolve JMeq_refl.

Lemma sym_JMeq : (A,B:Set)(x:A)(y:B)(JMeq x y)->(JMeq y x).
NewDestruct 1; Trivial.
Qed.

Hints Immediate sym_JMeq.

Lemma trans_JMeq : (A,B,C:Set)(x:A)(y:B)(z:C)
	(JMeq x y)->(JMeq y z)->(JMeq x z).
NewDestruct 1; Trivial.
Qed.

Axiom JMeq_eq : (A:Set)(x,y:A)(JMeq x y)->(x=y).

Lemma JMeq_ind : (A:Set)(x,y:A)(P:A->Prop)(P x)->(JMeq x y)->(P y).
Intros A x y P H H'; Case JMeq_eq with 1:=H'; Trivial.
Qed.

Lemma JMeq_rec : (A:Set)(x,y:A)(P:A->Set)(P x)->(JMeq x y)->(P y).
Intros A x y P H H'; Case JMeq_eq with 1:=H'; Trivial.
Qed.

Lemma JMeq_ind_r : (A:Set)(x,y:A)(P:A->Prop)(P y)->(JMeq x y)->(P x).
Intros A x y P H H'; Case JMeq_eq with 1:=(sym_JMeq H'); Trivial.
Qed.

Lemma JMeq_rec_r : (A:Set)(x,y:A)(P:A->Set)(P y)->(JMeq x y)->(P x).
Intros A x y P H H'; Case JMeq_eq with 1:=(sym_JMeq H'); Trivial.
Qed.

(** [JMeq] is equivalent to [(eq_dep Set [X]X)] *)

Require Eqdep.

Lemma JMeq_eq_dep : (A,B:Set)(x:A)(y:B)(JMeq x y)->(eq_dep Set [X]X A x B y).
Proof.
NewDestruct 1.
Apply eq_dep_intro.
Qed.

Lemma eq_dep_JMeq : (A,B:Set)(x:A)(y:B)(eq_dep Set [X]X A x B y)->(JMeq x y).
Proof.
NewDestruct 1.
Apply JMeq_refl. 
Qed.
