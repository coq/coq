(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(** Authors: Bruno Barras, Cristina Cornes *)

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

Notation LexProd := (lexprod A B leA leB).

Hints Resolve t_step Acc_clos_trans wf_clos_trans.

Lemma acc_A_B_lexprod : (x:A)(Acc A leA x)
        ->((x0:A)(clos_trans A leA x0 x)->(well_founded (B x0) (leB x0)))
                ->(y:(B x))(Acc (B x) (leB x) y)
                        ->(Acc (sigS A B) LexProd (existS A B x y)).
Proof.
 NewInduction 1 as [x _ IHAcc]; Intros H2 y.
 NewInduction 1 as [x0 H IHAcc0];Intros.
 Apply Acc_intro.
 NewDestruct y as [x2 y1]; Intro H6.
 Simple Inversion H6; Intro.
 Cut (leA x2 x);Intros.
 Apply IHAcc;Auto with sets.
 Intros.
 Apply H2.
 Apply t_trans with x2 ;Auto with sets.

 Red in H2.
 Apply H2.
 Auto with sets.

 Injection H1.
 NewDestruct 2.
 Injection H3.
 NewDestruct 2;Auto with sets.

 Rewrite <- H1.
 Injection H3; Intros _ Hx1.
 Subst x1.
 Apply IHAcc0.
 Elim inj_pair2 with A B x y' x0; Assumption.
Qed.

Theorem wf_lexprod: 
   (well_founded A leA) ->((x:A) (well_founded (B x) (leB x))) 
             -> (well_founded (sigS A B) LexProd).
Proof.
 Intros wfA wfB;Unfold well_founded .
 NewDestruct a.
 Apply acc_A_B_lexprod;Auto with sets;Intros.
 Red in wfB.
 Auto with sets.
Qed.


End WfLexicographic_Product.


Section Wf_Symmetric_Product.
  Variable A:Set.
  Variable B:Set.
  Variable leA: A->A->Prop.
  Variable leB: B->B->Prop.

  Notation Symprod := (symprod A B leA leB).

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
Qed.
i*)

  Lemma Acc_symprod: (x:A)(Acc A leA x)->(y:B)(Acc B leB y)
                        ->(Acc (A*B) Symprod (x,y)).
 Proof.
 NewInduction 1 as [x _ IHAcc]; Intros y H2.
 NewInduction H2 as [x1 H3 IHAcc1].
 Apply Acc_intro;Intros y H5.
 Inversion_clear H5;Auto with sets.
 Apply IHAcc; Auto.
 Apply Acc_intro;Trivial.
Qed.


Lemma wf_symprod: (well_founded A leA)->(well_founded B leB)
                        ->(well_founded (A*B) Symprod).
Proof.
 Red.
 NewDestruct a.
 Apply Acc_symprod;Auto with sets.
Qed.

End Wf_Symmetric_Product.


Section Swap.

  Variable A:Set.
  Variable R:A->A->Prop.

  Notation SwapProd :=(swapprod A R).


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
Qed.


  Lemma Acc_swapprod: (x,y:A)(Acc A R x)->(Acc A R y)
                                ->(Acc A*A SwapProd (x,y)).
Proof.
 NewInduction 1 as [x0 _ IHAcc0];Intros H2.
 Cut (y0:A)(R y0 x0)->(Acc ? SwapProd (y0,y)).
 Clear  IHAcc0.
 NewInduction H2 as [x1 _ IHAcc1]; Intros H4.
 Cut (y:A)(R y x1)->(Acc ? SwapProd (x0,y)).
 Clear  IHAcc1.
 Intro.
 Apply Acc_intro.
 NewDestruct y; Intro H5.
 Inversion_clear H5.
 Inversion_clear H0;Auto with sets.

 Apply swap_Acc.
 Inversion_clear H0;Auto with sets.

 Intros.
 Apply IHAcc1;Auto with sets;Intros.
 Apply Acc_inv with (y0,x1) ;Auto with sets.
 Apply sp_noswap.
 Apply right_sym;Auto with sets.

 Auto with sets.
Qed.


  Lemma wf_swapprod: (well_founded A R)->(well_founded A*A SwapProd).
Proof.
 Red.
 NewDestruct a;Intros.
 Apply Acc_swapprod;Auto with sets.
Qed.

End Swap.
