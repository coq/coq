(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)
(*i 	$Id$	 i*)

(*s John Major's Equality as proposed by C. Mc Bride *)

Set Implicit Arguments.

Inductive JMeq [A:Set;x:A] : (B:Set)B->Prop := 
	JMeq_refl : (JMeq x x).

Hints Resolve JMeq_refl.

Lemma JMeq_sym : (A,B:Set)(x:A)(y:B)(JMeq x y)->(JMeq y x).
Destruct 1; Trivial.
Save.

Hints Immediate JMeq_sym.

Lemma JMeq_trans : (A,B,C:Set)(x:A)(y:B)(z:C)
	(JMeq x y)->(JMeq y z)->(JMeq x z).
Destruct 1; Trivial.
Save.

Axiom JMeq_eq : (A:Set)(x,y:A)(JMeq x y)->(x=y).

Lemma JMeq_eq_ind : (A:Set)(x,y:A)(P:A->Prop)(P x)->(JMeq x y)->(P y).
Intros A x y P H H'; Case JMeq_eq with 1:=H'; Trivial.
Save.

Lemma JMeq_eq_rec : (A:Set)(x,y:A)(P:A->Set)(P x)->(JMeq x y)->(P y).
Intros A x y P H H'; Case JMeq_eq with 1:=H'; Trivial.
Save.

Lemma JMeq_eq_ind_r : (A:Set)(x,y:A)(P:A->Prop)(P y)->(JMeq x y)->(P x).
Intros A x y P H H'; Case JMeq_eq with 1:=(JMeq_sym H'); Trivial.
Save.

Lemma JMeq_eq_rec_r : (A:Set)(x,y:A)(P:A->Set)(P y)->(JMeq x y)->(P x).
Intros A x y P H H'; Case JMeq_eq with 1:=(JMeq_sym H'); Trivial.
Save.
