(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(** Author: Bruno Barras *)

Section Inverse_Image.

  Variables A,B:Set.
  Variable R : B->B->Prop.
  Variable f:A->B.

  Local Rof : A->A->Prop := [x,y:A](R (f x) (f y)).

  Remark Acc_lemma : (y:B)(Acc B R y)->(x:A)(y=(f x))->(Acc A Rof x).
    NewInduction 1 as [y _ IHAcc]; Intros x H.
    Apply Acc_intro; Intros y0 H1.
    Apply (IHAcc (f y0)); Try Trivial.
    Rewrite H; Trivial.
  Qed.

  Lemma Acc_inverse_image : (x:A)(Acc B R (f x)) -> (Acc A Rof x).
    Intros; Apply (Acc_lemma (f x)); Trivial.
  Qed.

  Theorem wf_inverse_image: (well_founded B R)->(well_founded A Rof).
    Red; Intros; Apply Acc_inverse_image; Auto.
  Qed.

  Variable F : A -> B -> Prop.
  Local RoF : A -> A -> Prop := [x,y]
    (EX b : B | (F x b) & (c:B)(F y c)->(R b c)).

Lemma Acc_inverse_rel :
   (b:B)(Acc B R b)->(x:A)(F x b)->(Acc A RoF x).
NewInduction 1 as [x _ IHAcc]; Intros x0 H2.
Constructor; Intros y H3.
NewDestruct H3.
Apply (IHAcc x1); Auto.
Save.


Theorem wf_inverse_rel : 
   (well_founded B R)->(well_founded A RoF).
    Red; Constructor; Intros.
    Case H0; Intros.
    Apply (Acc_inverse_rel x); Auto.
Save.

End Inverse_Image.


