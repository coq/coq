(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(****************************************************************************)
(*                         Bruno Barras                                     *)
(****************************************************************************)

Section Inverse_Image.

  Variables A,B:Set.
  Variable R : B->B->Prop.
  Variable f:A->B.

  Local Rof : A->A->Prop := [x,y:A](R (f x) (f y)).

  Remark Acc_lemma : (y:B)(Acc B R y)->(x:A)(y=(f x))->(Acc A Rof x).
    Induction 1; Intros.
    Apply Acc_intro; Intros.
    Apply (H1 (f y0)); Try Trivial.
    Rewrite H2; Trivial.
  Save.

  Lemma Acc_inverse_image : (x:A)(Acc B R (f x)) -> (Acc A Rof x).
    Intros; Apply (Acc_lemma (f x)); Trivial.
  Save.

  Theorem wf_inverse_image: (well_founded B R)->(well_founded A Rof).
    Red; Intros; Apply Acc_inverse_image; Auto.
  Save.

End Inverse_Image.


