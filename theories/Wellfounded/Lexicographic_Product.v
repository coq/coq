(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(** Authors: Bruno Barras,Cristina Cornes *)

Require Eqdep.
Require Relation_Operators.
Require Transitive_Closure.

(**  From : Constructing Recursion Operators in Type Theory            
     L. Paulson  JSC (1986) 2, 325-355 *)

Section WfLexicographic_Product.
Variable A:Set.
Variable B:A->Set.
Variable leA: A->A->Prop.
Variable leB: (x:A)(B x)->(B x)->Prop.


Syntactic Definition LexProd := (lexprod A B leA leB).

Hints Resolve t_step Acc_clos_trans wf_clos_trans.

Lemma acc_A_B_lexprod : (x:A)(Acc A leA x)
        ->((x0:A)(clos_trans A leA x0 x)->(well_founded (B x0) (leB x0)))
                ->(y:(B x))(Acc (B x) (leB x) y)
                        ->(Acc (sigS A B) LexProd (existS A B x y)).
Proof.
 Induction 1; Intros x0 H0 H1 H2 y.
 Induction 1;Intros.
 Apply Acc_intro.
 Induction y0.
 Intros x2 y1 H6.
 Simple Inversion H6;Intros.
 Cut (leA x2 x0);Intros.
 Apply H1;Auto with sets.
 Intros.
 Apply H2.
 Apply t_trans with x2 ;Auto with sets.

 Red in H2.
 Apply H2.
 Auto with sets.

 Injection H8.
 Induction 2.
 Injection H9.
 Induction 2;Auto with sets.

 Elim H8.
 Generalize y2 y' H9 H7 .
 Replace x3 with x0.
 Clear  H7 H8 H9 y2 y' x3 H6 y1 x2 y0.
 Intros.
 Apply H5.
 Elim inj_pair2 with A B x0 y' x1 ;Auto with sets.

 Injection H9;Auto with sets.
Qed.

Theorem wf_lexprod: 
   (well_founded A leA) ->((x:A) (well_founded (B x) (leB x))) 
             -> (well_founded (sigS A B) LexProd).
Proof.
 Intros wfA wfB;Unfold well_founded .
 Induction a;Intros.
 Apply acc_A_B_lexprod;Auto with sets;Intros.
 Red in wfB.
 Auto with sets.
Save.


End WfLexicographic_Product.


Section Wf_Symmetric_Product.
  Variable A:Set.
  Variable B:Set.
  Variable leA: A->A->Prop.
  Variable leB: B->B->Prop.

  Syntactic Definition Symprod := (symprod A B leA leB).

(*i
  Local sig_prod:=
         [x:A*B]<{_:A&B}>Case x of [a:A][b:B](existS A [_:A]B a b) end.

Lemma incl_sym_lexprod: (included (A*B) Symprod  
            (R_o_f (A*B) {_:A&B} sig_prod (lexprod A [_:A]B leA [_:A]leB))).
Proof.
 Red.
 Induction x.
 (Induction y1;Intros).
 Red.
 Unfold sig_prod .
 Inversion_clear H.
 (Apply left_lex;Auto with sets).

 (Apply right_lex;Auto with sets).
Save.
i*)

  Lemma Acc_symprod: (x:A)(Acc A leA x)->(y:B)(Acc B leB y)
                        ->(Acc (A*B) Symprod (x,y)).
Proof.
 Induction 1;Intros.
 Elim H2;Intros.
 Apply Acc_intro;Intros.
 Inversion_clear H5;Auto with sets.
 Apply H1;Auto with sets.
 Apply Acc_intro;Auto with sets.
Save.


Lemma wf_symprod: (well_founded A leA)->(well_founded B leB)
                        ->(well_founded (A*B) Symprod).
Proof.
 Red.
 Induction a;Intros.
 Apply Acc_symprod;Auto with sets.
Save.

End Wf_Symmetric_Product.


Section Swap.

  Variable A:Set.
  Variable R:A->A->Prop.

  Syntactic Definition SwapProd :=(swapprod A R).


  Lemma swap_Acc: (x,y:A)(Acc A*A SwapProd (x,y))->(Acc A*A SwapProd (y,x)).
Proof.
 Intros.
 Inversion_clear H.
 Apply Acc_intro.
 NewDestruct y0;Intros.
 Inversion_clear H;Inversion_clear H1;Apply H0.
 Apply sp_swap.
 Apply right_sym;Auto with sets.

 Apply sp_swap.
 Apply left_sym;Auto with sets.

 Apply sp_noswap.
 Apply right_sym;Auto with sets.

 Apply sp_noswap.
 Apply left_sym;Auto with sets.
Save.


  Lemma Acc_swapprod: (x,y:A)(Acc A R x)->(Acc A R y)
                                ->(Acc A*A SwapProd (x,y)).
Proof.
 Induction 1;Intros.
 Cut (y0:A)(R y0 x0)->(Acc ? SwapProd (y0,y)).
 Clear  H1.
 Elim H2;Intros.
 Cut (y:A)(R y x1)->(Acc ? SwapProd (x0,y)).
 Clear  H3.
 Intro.
 Apply Acc_intro.
 Induction y0;Intros.
 Inversion_clear H5.
 Inversion_clear H6;Auto with sets.

 Apply swap_Acc.
 Inversion_clear H6;Auto with sets.

 Intros.
 Apply H3;Auto with sets;Intros.
 Apply Acc_inv with (y1,x1) ;Auto with sets.
 Apply sp_noswap.
 Apply right_sym;Auto with sets.

 Auto with sets.
Save.


  Lemma wf_swapprod: (well_founded A R)->(well_founded A*A SwapProd).
Proof.
 Red.
 Induction a;Intros.
 Apply Acc_swapprod;Auto with sets.
Save.

End Swap.
