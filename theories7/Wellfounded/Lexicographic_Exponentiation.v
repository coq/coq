(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(** Author: Cristina Cornes

    From : Constructing Recursion Operators in Type Theory                
           L. Paulson  JSC (1986) 2, 325-355  *)

Require Eqdep.
Require PolyList.
Require PolyListSyntax.
Require Relation_Operators.
Require Transitive_Closure.

Section Wf_Lexicographic_Exponentiation.
Variable A:Set.
Variable leA: A->A->Prop.

Notation Power := (Pow A leA).
Notation Lex_Exp := (lex_exp A leA).
Notation ltl := (Ltl A leA).
Notation Descl := (Desc A leA).

Notation List := (list A).
Notation Nil := (nil A).
(* useless but symmetric *)
Notation Cons := (cons 1!A).
Notation "<< x , y >>" := (exist List Descl x y) (at level 0)
  V8only (at level 0, x,y at level 100).

V7only[
Syntax constr
  level 1:
    List [ (list A) ] -> ["List"]
  | Nil  [ (nil A) ] -> ["Nil"]
  | Cons [ (cons A) ] -> ["Cons"]
  ;
  level 10:
    Cons2 [ (cons A $e $l) ] -> ["Cons " $e:L " " $l:L ].

Syntax constr
  level 1:
  pair_sig [ (exist (list A) Desc $e $d) ] -> ["<<" $e:L "," $d:L ">>"].
].
Hints Resolve d_one d_nil  t_step.

Lemma left_prefix : (x,y,z:List)(ltl x^y z)-> (ltl x z).
Proof.
 Induction x.
 Induction z.
 Simpl;Intros H.
 Inversion_clear H. 
 Simpl;Intros;Apply (Lt_nil A leA).
 Intros a l HInd.
 Simpl.
 Intros.
 Inversion_clear H.
 Apply (Lt_hd A leA);Auto with sets.
 Apply (Lt_tl A leA).
 Apply (HInd y y0);Auto with sets.
Qed.


Lemma  right_prefix : 
  (x,y,z:List)(ltl x y^z)-> (ltl x y) \/ (EX y':List | x=(y^y') /\ (ltl y' z)).
Proof.
 Intros x y;Generalize x.
 Elim y;Simpl.
 Right.
 Exists x0 ;Auto with sets.
 Intros.
 Inversion H0.
 Left;Apply (Lt_nil A leA).
 Left;Apply (Lt_hd A leA);Auto with sets.
 Generalize (H x1 z H3) .
 Induction 1.
 Left;Apply (Lt_tl A leA);Auto with sets.
 Induction 1.
 Induction 1;Intros.
 Rewrite -> H8.
 Right;Exists x2 ;Auto with sets.
Qed.



Lemma desc_prefix: (x:List)(a:A)(Descl x^(Cons a Nil))->(Descl x).
Proof.
 Intros.
 Inversion H.
 Generalize (app_cons_not_nil H1); Induction 1. 
 Cut (x^(Cons a Nil))=(Cons x0 Nil); Auto with sets.
 Intro.
 Generalize (app_eq_unit H0) .
 Induction 1; Induction 1; Intros.
 Rewrite -> H4; Auto with sets.
 Discriminate H5.
 Generalize (app_inj_tail H0) .
 Induction 1; Intros.
 Rewrite <- H4; Auto with sets.
Qed.

Lemma desc_tail: (x:List)(a,b:A)
          (Descl (Cons b (x^(Cons a Nil))))-> (clos_trans A leA a b).
Proof.
 Intro.
 Apply rev_ind with  A:=A
             P:=[x:List](a,b:A)
          (Descl (Cons b (x^(Cons a Nil))))-> (clos_trans A leA a b).
 Intros.

 Inversion  H.
 Cut (Cons b (Cons a Nil))= ((Nil^(Cons b Nil))^ (Cons a Nil)); Auto with sets; Intro.
 Generalize H0.
 Intro.
 Generalize (app_inj_tail 2!(l^(Cons y Nil)) 3!(Nil^(Cons b Nil)) H4);
 Induction 1.
 Intros.

 Generalize (app_inj_tail H6); Induction 1; Intros.
 Generalize H1.
 Rewrite <- H10; Rewrite <- H7; Intro.
 Apply (t_step A leA); Auto with sets.



 Intros.
 Inversion H0.
 Generalize  (app_cons_not_nil H3); Intro.
 Elim H1.

 Generalize H0.
 Generalize (app_comm_cons (l^(Cons x0 Nil)) (Cons a Nil) b); Induction 1.
 Intro.
 Generalize (desc_prefix (Cons b (l^(Cons x0 Nil))) a H5); Intro.
 Generalize (H x0 b H6).
 Intro.
 Apply t_trans with A:=A  y:=x0; Auto with sets.

 Apply  t_step.
 Generalize H1.
 Rewrite -> H4; Intro.

 Generalize (app_inj_tail H8); Induction 1.
 Intros.
 Generalize H2; Generalize (app_comm_cons l (Cons x0 Nil) b).
 Intro.
 Generalize H10.
 Rewrite ->H12; Intro.
 Generalize (app_inj_tail H13); Induction 1.
 Intros.
 Rewrite <- H11; Rewrite <- H16; Auto with sets.
Qed.


Lemma dist_aux : (z:List)(Descl z)->(x,y:List)z=(x^y)->(Descl x)/\ (Descl y).
Proof.
 Intros z D.
 Elim D.
 Intros.
 Cut (x^y)=Nil;Auto with sets; Intro.
 Generalize (app_eq_nil H0) ; Induction 1.
 Intros.
 Rewrite -> H2;Rewrite -> H3; Split;Apply d_nil.

 Intros.
 Cut (x0^y)=(Cons x Nil); Auto with sets.
 Intros E.
 Generalize (app_eq_unit E); Induction 1.
 Induction 1;Intros.
 Rewrite -> H2;Rewrite -> H3; Split.
 Apply d_nil.

 Apply d_one.

 Induction 1; Intros.
 Rewrite -> H2;Rewrite -> H3; Split.
 Apply d_one.

 Apply d_nil.

 Do 5 Intro.
 Intros Hind.
 Do 2 Intro.
 Generalize x0 .
 Apply rev_ind with A:=A 
      P:=[y0:List]
          (x0:List)
          ((l^(Cons y Nil))^(Cons x Nil))=(x0^y0)->(Descl x0)/\(Descl y0).

 Intro.
 Generalize (app_nil_end x1) ; Induction 1; Induction 1.
 Split. Apply d_conc; Auto with sets.

 Apply d_nil.

 Do 3 Intro.
 Generalize x1 .
 Apply rev_ind with 
  A:=A 
  P:=[l0:List]
     (x1:A)
      (x0:List)
       ((l^(Cons y Nil))^(Cons x Nil))=(x0^(l0^(Cons x1 Nil)))
         ->(Descl x0)/\(Descl (l0^(Cons x1 Nil))).


 Simpl.
 Split.
 Generalize (app_inj_tail H2) ;Induction 1.
 Induction 1;Auto with sets.

 Apply d_one.
 Do 5 Intro.
 Generalize (app_ass x4 (l1^(Cons x2 Nil)) (Cons x3 Nil)) .
 Induction 1.
 Generalize (app_ass x4 l1 (Cons x2 Nil)) ;Induction 1.
 Intro E.
 Generalize (app_inj_tail E) .
 Induction 1;Intros.
 Generalize (app_inj_tail H6) ;Induction 1;Intros.
 Rewrite <- H7;  Rewrite <- H10; Generalize H6.
 Generalize (app_ass x4 l1 (Cons x2 Nil)); Intro E1.
 Rewrite -> E1.
 Intro.
 Generalize (Hind x4 (l1^(Cons x2 Nil))  H11) .
 Induction 1;Split.
 Auto with sets.

 Generalize H14.
 Rewrite <- H10; Intro.
 Apply d_conc;Auto with sets.
Qed.



Lemma dist_Desc_concat : (x,y:List)(Descl x^y)->(Descl x)/\(Descl y).
Proof.
  Intros.
  Apply (dist_aux (x^y) H x y); Auto with sets.
Qed.


Lemma desc_end:(a,b:A)(x:List) 
   (Descl x^(Cons a Nil)) /\ (ltl x^(Cons a Nil) (Cons b Nil))
     -> (clos_trans A leA a b). 

Proof.
 Intros a b x.
 Case x.
 Simpl.
 Induction 1.
 Intros.
 Inversion H1;Auto with sets.
 Inversion H3.

 Induction 1.
 Generalize (app_comm_cons l (Cons a Nil) a0).
 Intros E; Rewrite <- E; Intros.
 Generalize (desc_tail l a a0 H0); Intro.
 Inversion H1.
 Apply t_trans with y:=a0 ;Auto with sets.

 Inversion H4.
Qed.




Lemma  ltl_unit: (x:List)(a,b:A)
 (Descl (x^(Cons a Nil))) -> (ltl x^(Cons a Nil) (Cons b Nil))
               -> (ltl x (Cons b Nil)).
Proof.
 Intro.
 Case x.
 Intros;Apply (Lt_nil A leA).

 Simpl;Intros.
 Inversion_clear H0.
 Apply (Lt_hd A leA  a b);Auto with sets.
 
 Inversion_clear H1.
Qed.


Lemma acc_app: 
    (x1,x2:List)(y1:(Descl x1^x2))
     (Acc Power Lex_Exp (exist List Descl (x1^x2)  y1))
     ->(x:List)
        (y:(Descl x))
         (ltl x (x1^x2))->(Acc Power Lex_Exp (exist List Descl x y)).
Proof.
 Intros.
 Apply (Acc_inv Power Lex_Exp (exist List Descl (x1^x2) y1)).
 Auto with sets.

 Unfold lex_exp ;Simpl;Auto with sets.
Qed.


Theorem wf_lex_exp :
  (well_founded A leA)->(well_founded Power Lex_Exp).
Proof.
 Unfold 2 well_founded .
 Induction a;Intros x y.
 Apply Acc_intro.
 Induction y0.
 Unfold 1 lex_exp ;Simpl.
 Apply rev_ind with A:=A P:=[x:List]
                            (x0:List)
                             (y:(Descl x0))
                              (ltl x0 x)
                               ->(Acc Power Lex_Exp (exist List Descl x0 y)) .
 Intros.
 Inversion_clear H0.

 Intro.
 Generalize (well_founded_ind A (clos_trans A leA) (wf_clos_trans A leA H)).
 Intros GR.
 Apply GR with P:=[x0:A]
                  (l:List)
                   ((x1:List)
                     (y:(Descl x1))
                      (ltl x1 l)
                       ->(Acc Power Lex_Exp (exist List Descl x1 y)))
                    ->(x1:List)
                       (y:(Descl x1))
                        (ltl x1 (l^(Cons x0 Nil)))
                         ->(Acc Power Lex_Exp (exist List Descl x1 y)) .
 Intro;Intros HInd; Intros.
 Generalize (right_prefix x2 l (Cons x1 Nil) H1) .
 Induction 1.
 Intro; Apply (H0 x2 y1 H3).

 Induction 1.
 Intro;Induction 1.
 Clear  H4  H2.
 Intro;Generalize y1 ;Clear  y1.
 Rewrite -> H2.
 Apply rev_ind with A:=A P:=[x3:List]
                            (y1:(Descl (l^x3)))
                             (ltl x3 (Cons x1 Nil))
                              ->(Acc Power Lex_Exp
                                  (exist List Descl (l^x3) y1)) .
 Intros.
 Generalize (app_nil_end l) ;Intros Heq.
 Generalize y1 .
 Clear  y1.
 Rewrite <- Heq.
 Intro.
 Apply Acc_intro.
 Induction y2.
 Unfold 1 lex_exp .
 Simpl;Intros x4 y3. Intros.
 Apply (H0 x4 y3);Auto with sets.

 Intros. 
 Generalize (dist_Desc_concat l (l0^(Cons x4 Nil)) y1) .
 Induction 1.
 Intros.
 Generalize (desc_end x4 x1 l0  (conj ? ? H8 H5)) ; Intros.
 Generalize y1 .
 Rewrite <- (app_ass l l0 (Cons x4 Nil)); Intro.
 Generalize (HInd x4 H9 (l^l0)) ; Intros HInd2.
 Generalize (ltl_unit l0 x4 x1 H8 H5); Intro.
 Generalize (dist_Desc_concat (l^l0) (Cons x4 Nil) y2) .
 Induction 1;Intros.
 Generalize (H4 H12 H10); Intro.
 Generalize (Acc_inv Power Lex_Exp (exist List Descl (l^l0) H12) H14) .
 Generalize (acc_app l l0 H12 H14).
 Intros f g.
 Generalize (HInd2 f);Intro.
 Apply Acc_intro.
 Induction y3.
 Unfold 1 lex_exp ;Simpl; Intros.
 Apply H15;Auto with sets.
Qed.


End Wf_Lexicographic_Exponentiation.
