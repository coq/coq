(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Inductive T : Set := A: T | B :T->T.

Lemma lem1 : (x,y:T){x=y}+{~x=y}.
Decide Equality.
Qed.

Lemma lem2 : (x,y:T){x=y}+{~x=y}.
Intros x y.
Decide Equality x y.
Qed.

Lemma lem3 : (x,y:T){x=y}+{~x=y}.
Intros x y.
Decide Equality y x.
Qed.

Lemma lem4 : (x,y:T){x=y}+{~x=y}.
Intros x y.
Compare x y; Auto.
Qed.

