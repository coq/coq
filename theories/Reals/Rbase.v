(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(***************************************************************************)
(*s              Basic lemmas for the classical reals numbers              *)
(***************************************************************************)

Require Export Raxioms.
Require Export ZArithRing.
Require Omega.
Require Export Field.

(***************************************************************************)
(*s       Instantiating Ring tactic on reals                               *)
(***************************************************************************)

Lemma RTheory : (Ring_Theory Rplus Rmult R1 R0 Ropp [x,y:R]false).
  Split.
  Exact Rplus_sym.
  Symmetry; Apply Rplus_assoc.
  Exact Rmult_sym.
  Symmetry; Apply Rmult_assoc.
  Intro; Apply Rplus_Ol.
  Intro; Apply Rmult_1l.
  Exact Rplus_Ropp_r.
  Intros.
  Rewrite Rmult_sym.
  Rewrite (Rmult_sym n p).
  Rewrite (Rmult_sym m p).
  Apply Rmult_Rplus_distr.
  Intros; Contradiction.
Defined.

Add Field R Rplus Rmult R1 R0 Ropp [x,y:R]false Rinv RTheory Rinv_l
          with minus:=Rminus div:=Rdiv.

(**************************************************************************)
(*s  Relation between orders and equality                                 *)
(**************************************************************************)

(**********)
Lemma Rlt_antirefl:(r:R)~``r<r``.
  Red; Intros; Apply (Rlt_antisym r r H); Auto with zarith real.
Save.
Hints Resolve Rlt_antirefl : real.

Lemma Rlt_not_eq:(r1,r2:R)``r1<r2``->``r1<>r2``.
  Red; Intros r1 r2 H H0; Apply (Rlt_antirefl r1).
  Pattern 2 r1; Rewrite H0; Trivial.
Save.

Lemma Rgt_not_eq:(r1,r2:R)``r1>r2``->``r1<>r2``.
Intros; Apply sym_not_eqT; Apply Rlt_not_eq; Auto with real.
Save.

(**********)
Lemma imp_not_Req:(r1,r2:R)(``r1<r2``\/ ``r1>r2``) -> ``r1<>r2``.
Intros r1 r2 [H|H].
Apply Rlt_not_eq; Auto with real.
Apply Rgt_not_eq; Auto with real.
Save.
Hints Resolve imp_not_Req : real.

(*s Reasoning by case on equalities and order *)

(**********)
Lemma Req_EM:(r1,r2:R)(r1==r2)\/``r1<>r2``.
Intros;Elim (total_order_T r1 r2);Intro.
Case a; Auto with real.
Auto with real.
Save.
Hints Resolve Req_EM : real.

(**********)
Lemma total_order:(r1,r2:R)``r1<r2``\/(r1==r2)\/``r1>r2``.
Intros;Elim (total_order_T r1 r2);Intro;Auto.
Elim a;Intro;Auto.
Save.

(**********)
Lemma not_Req:(r1,r2:R)``r1<>r2``->(``r1<r2``\/``r1>r2``).
Intros; Case (total_order r1 r2); Intros; Auto with real.
Case H0; Intros.
Absurd r1==r2; Auto with real.
Auto with real.
Save.


(*********************************************************************************)
(*s       Order Lemma  : relating [<], [>], [<=] and [>=]  	                 *)
(*********************************************************************************)

(**********)
Lemma Rlt_le:(r1,r2:R)``r1<r2``-> ``r1<=r2``.
Unfold Rle; Auto.
Save.
Hints Resolve Rlt_le : real.

(**********)
Lemma Rle_ge : (r1,r2:R)``r1<=r2`` -> ``r2>=r1``.
Destruct 1; Red; Auto with real.
Save.

(**********)
Lemma Rge_le : (r1,r2:R)``r1>=r2`` -> ``r2<=r1``.
Destruct 1; Red; Auto with real.
Save.

(**********)
Lemma not_Rle:(r1,r2:R)~(``r1<=r2``)->``r1>r2``.
Intros; Unfold Rle in H; Elim (total_order r1 r2); Intro.
Elim H;Left; Assumption.
Elim H0; Intro;Auto.
Elim H;Right; Assumption.
Save.

Hints Immediate Rle_ge Rge_le not_Rle : real.

(**********)
Lemma Rlt_le_not:(r1,r2:R)``r2<r1``->~(``r1<=r2``).
Intros; Red; Intro; Elim H0; Clear H0; Intro.
Exact (Rlt_antisym r1 r2 H0 H).
Case (imp_not_Req r1 r2); Auto with real.
Save.

Lemma Rle_not:(r1,r2:R)``r1>r2`` -> ~(``r1<=r2``).
Proof Rlt_le_not.

Hints Immediate Rlt_le_not : real.

(**********)
Lemma Rlt_ge_not:(r1,r2:R)``r1<r2``->~(``r1>=r2``).
Unfold Rge; Red; Intros.
Apply (Rlt_le_not r2 r1 H).
Red; Case H0; Auto with real.
Save.

Hints Immediate Rlt_ge_not : real.

(**********)
Lemma eq_Rle:(r1,r2:R)r1==r2->``r1<=r2``.
Unfold Rle; Auto.
Save.
Hints Immediate eq_Rle : real.

Lemma eq_Rge:(r1,r2:R)r1==r2->``r1>=r2``.
Unfold Rge; Auto.
Save.
Hints Immediate eq_Rge : real.

Lemma eq_Rle_sym:(r1,r2:R)r2==r1->``r1<=r2``.
Unfold Rle; Auto.
Save.
Hints Immediate eq_Rle_sym : real.

Lemma eq_Rge_sym:(r1,r2:R)r2==r1->``r1>=r2``.
Unfold Rge; Auto.
Save.
Hints Immediate eq_Rge_sym : real.

Lemma Rle_antisym : (r1,r2:R)``r1<=r2`` -> ``r2<=r1``-> r1==r2.
Unfold Rle; Intros.
Case H; Intro; Auto with real.
Case H0; Intro; Auto with real.
Case (Rlt_antisym r1 r2 H1 H2).
Save.
Hints Resolve Rle_antisym : real.

(**********)
Lemma Rle_le_eq:(r1,r2:R)(``r1<=r2``/\``r2<=r1``)<->(r1==r2).
Split; Auto with real.
Intros (H1,H2); Auto with real.
Save.


(**********)
Lemma Rle_trans:(r1,r2,r3:R) ``r1<=r2``->``r2<=r3``->``r1<=r3``.
Intros r1 r2 r3; Unfold Rle; Intros.
Elim H; Elim H0; Intros.
Left; Apply Rlt_trans with r2; Trivial.
Left; Rewrite <- H1; Trivial.
Left; Rewrite H2; Trivial.
Right; Transitivity r2; Trivial.
Save.

(**********)
Lemma Rle_lt_trans:(r1,r2,r3:R)``r1<=r2``->``r2<r3``->``r1<r3``.
Intros; Unfold Rle in H; Elim H; Intro.
Apply (Rlt_trans r1 r2 r3 H1 H0).
Rewrite -> H1; Auto with zarith real.
Save.

(**********)
Lemma Rlt_le_trans:(r1,r2,r3:R)``r1<r2``->``r2<=r3``->``r1<r3``.
Intros; Unfold Rle in H0; Elim H0; Intro.
Apply (Rlt_trans r1 r2 r3 H H1).
Rewrite <- H1; Auto with zarith real.
Save.


(*s Decidability of the order *)
Lemma total_order_Rlt:(r1,r2:R)(sumboolT ``r1<r2`` ~(``r1<r2``)).
Intros;Elim (total_order_T r1 r2);Intros.
Elim a;Intro.
Left;Assumption.
Right;Rewrite b;Apply Rlt_antirefl.
Right;Unfold Rgt in b;Apply Rlt_antisym;Assumption.
Save.

(**********)
Lemma total_order_Rle:(r1,r2:R)(sumboolT ``r1<=r2`` ~(``r1<=r2``)).
Intros;Elim (total_order_T r1 r2);Intros.
Left;Unfold Rle;Elim a;Auto with real.
Right; Auto with real.
Save.

(**********)
Lemma total_order_Rgt:(r1,r2:R)(sumboolT ``r1>r2`` ~(``r1>r2``)).
Unfold Rgt;Intros;Apply total_order_Rlt.
Save.

(**********)
Lemma total_order_Rge:(r1,r2:R)(sumboolT (``r1>=r2``) ~(``r1>=r2``)).
Intros;Elim (total_order_Rle r2 r1);Intro.
Left; Auto with real.
Right; Auto with real.
Save.

Lemma total_order_Rlt_Rle:(r1,r2:R)(sumboolT ``r1<r2`` ``r2<=r1``).
Intros;Elim (total_order_T r1 r2); Intro H.
Case H; Intro.
Left; Trivial.
Right; Auto with real.
Right; Auto with real.
Save.

Lemma total_order_Rle_Rlt_eq :(r1,r2:R)``r1<=r2``-> (sumboolT ``r1<r2`` ``r1==r2``).
Intros r1 r2 H;Elim (total_order_T r1 r2); Trivial; Intro.
Elim (Rlt_le_not r1 r2); Trivial.
Save.


(**********)
Lemma inser_trans_R:(n,m,p,q:R)``n<=m<p``-> (sumboolT ``n<=m<q`` ``q<=m<p``).
Intros n m p q H; Case (total_order_Rlt_Rle m q); Intro.
Left; Case H; Auto.
Right; Case H; Auto.
Save.

(****************************************************************)
(*s        Field Lemmas                                         *)
(* This part contains lemma involving the Fields operations     *)
(****************************************************************)
(*********************************************************)
(*s      Addition                                        *)
(*********************************************************)

Lemma Rplus_ne:(r:R)``r+0==r``/\``0+r==r``.
Intro;Split;Ring.
Save.
Hints Resolve Rplus_ne : real v62.

Lemma Rplus_Or:(r:R)``r+0==r``.
Intro; Ring.
Save.
Hints Resolve Rplus_Or : real.

(**********)
Lemma Rplus_Ropp_l:(r:R)``(-r)+r==0``.
  Intro; Ring.
Save.
Hints Resolve Rplus_Ropp_l : real.


(**********)
Lemma Rplus_Ropp:(x,y:R)``x+y==0``->``y== -x``.
  Intros; Replace y with ``(-x+x)+y``;
  [ Rewrite -> Rplus_assoc; Rewrite -> H; Ring
  | Ring ].
Save.

(*i New i*)
Hint eqT_R_congr : real := Resolve (congr_eqT R).

Lemma Rplus_plus_r:(r,r1,r2:R)(r1==r2)->``r+r1==r+r2``.
  Auto with real.
Save.

(*i Old i*)Hints Resolve Rplus_plus_r : v62.

(**********)
Lemma r_Rplus_plus:(r,r1,r2:R)``r+r1==r+r2``->r1==r2.
  Intros; Transitivity ``(-r+r)+r1``.
  Ring.
  Transitivity ``(-r+r)+r2``.
  Repeat Rewrite -> Rplus_assoc; Rewrite <- H; Reflexivity.
  Ring.
Save.
Hints Resolve r_Rplus_plus : real.

(**********)
Lemma Rplus_ne_i:(r,b:R)``r+b==r`` -> ``b==0``.
  Intros r b; Pattern 2 r; Replace r with ``r+0``;
  EAuto with real.
Save.

(***********************************************************)       
(*s       Multiplication                                   *)
(***********************************************************)

(**********)
Lemma Rinv_r:(r:R)``r<>0``->``r* (/r)==1``.
  Intros; Rewrite -> Rmult_sym; Auto with real.
Save.
Hints Resolve Rinv_r : real.

Lemma Rinv_l_sym:(r:R)``r<>0``->``1==(/r) * r``.
  Symmetry; Auto with real.
Save.

Lemma Rinv_r_sym:(r:R)``r<>0``->``1==r* (/r)``.
  Symmetry; Auto with real.
Save.
Hints Resolve Rinv_l_sym Rinv_r_sym : real.


(**********)
Lemma Rmult_Or :(r:R) ``r*0==0``.
Intro; Ring.
Save.
Hints Resolve Rmult_Or : real v62.

(**********)
Lemma Rmult_Ol:(r:R)(``0*r==0``).
Intro; Ring.
Save.
Hints Resolve Rmult_Ol : real v62.

(**********)
Lemma Rmult_ne:(r:R)``r*1==r``/\``1*r==r``.
Intro;Split;Ring.
Save.
Hints Resolve Rmult_ne : real v62.

(**********)
Lemma Rmult_1r:(r:R)(``r*1==r``).
Intro; Ring.
Save.
Hints Resolve Rmult_1r : real.

(**********)
Lemma Rmult_mult_r:(r,r1,r2:R)r1==r2->``r*r1==r*r2``.
  Auto with real.
Save.

(*i OLD i*)Hints Resolve Rmult_mult_r : v62.

(**********)
Lemma r_Rmult_mult:(r,r1,r2:R)(``r*r1==r*r2``)->``r<>0``->(r1==r2).
  Intros; Transitivity ``(/r * r)*r1``.
  Rewrite Rinv_l; Auto with real.
  Transitivity ``(/r * r)*r2``.
  Repeat Rewrite Rmult_assoc; Rewrite H; Trivial.
  Rewrite Rinv_l; Auto with real.
Save.

(**********)
Lemma without_div_Od:(r1,r2:R)``r1*r2==0`` -> ``r1==0`` \/ ``r2==0``.
  Intros; Case (Req_EM r1 ``0``); [Intro Hz | Intro Hnotz].
  Auto.
  Right; Apply r_Rmult_mult with r1; Trivial.
  Rewrite H; Auto with real.
Save.

(**********)
Lemma without_div_Oi:(r1,r2:R) ``r1==0``\/``r2==0`` -> ``r1*r2==0``.
  Intros r1 r2 [H | H]; Rewrite H; Auto with real.
Save.

Hints Resolve without_div_Oi : real.

(**********)
Lemma without_div_Oi1:(r1,r2:R) ``r1==0`` -> ``r1*r2==0``.
  Auto with real.
Save.

(**********)
Lemma without_div_Oi2:(r1,r2:R) ``r2==0`` -> ``r1*r2==0``.
  Auto with real.
Save.


(**********) 
Lemma without_div_O_contr:(r1,r2:R)``r1*r2<>0`` -> ``r1<>0`` /\ ``r2<>0``.
Intros r1 r2 H; Split; Red; Intro; Apply H; Auto with real.
Save.

(**********) 
Lemma mult_non_zero :(r1,r2:R)``r1<>0`` /\ ``r2<>0`` -> ``r1*r2<>0``.
Red; Intros r1 r2 (H1,H2) H.
Case (without_div_Od r1 r2); Auto with real.
Save.
Hints Resolve mult_non_zero : real.

(**********) 
Lemma Rmult_Rplus_distrl:
   (r1,r2,r3:R) ``(r1+r2)*r3 == (r1*r3)+(r2*r3)``.
Intros; Ring.
Save.

(*s Square function *)

(***********)
Definition Rsqr:R->R:=[r:R]``r*r``.

(***********)
Lemma Rsqr_O:(Rsqr ``0``)==``0``.
  Unfold Rsqr; Auto with real.
Save.

(***********)
Lemma Rsqr_r_R0:(r:R)(Rsqr r)==``0``->``r==0``.
Unfold Rsqr;Intros;Elim (without_div_Od r r H);Trivial.
Save.

(*********************************************************)
(*s      Opposite                                        *)
(*********************************************************)

(**********)
Lemma eq_Ropp:(r1,r2:R)(r1==r2)->``-r1 == -r2``.
  Auto with real.
Save.
Hints Resolve eq_Ropp : real.

(**********)
Lemma Ropp_O:``-0==0``.
  Ring.
Save.
Hints Resolve Ropp_O : real v62.

(**********)
Lemma eq_RoppO:(r:R)``r==0``-> ``-r==0``.
  Intros; Rewrite -> H; Auto with real.
Save.
Hints Resolve eq_RoppO : real.

(**********)
Lemma Ropp_Ropp:(r:R)``-(-r)==r``.
  Intro; Ring.
Save.
Hints Resolve Ropp_Ropp : real.

(*********)
Lemma Ropp_neq:(r:R)``r<>0``->``-r<>0``.
Red;Intros r H H0.
Apply H.
Transitivity ``-(-r)``; Auto with real.
Save.
Hints Resolve Ropp_neq : real.

(**********)
Lemma Ropp_distr1:(r1,r2:R)``-(r1+r2)==(-r1 + -r2)``.
  Intros; Ring.
Save.
Hints Resolve Ropp_distr1 : real.

(*s Opposite and multiplication *)

Lemma Ropp_mul1:(r1,r2:R)``(-r1)*r2 == -(r1*r2)``.
  Intros; Ring.
Save.
Hints Resolve Ropp_mul1 : real.

(**********)
Lemma Ropp_mul2:(r1,r2:R)``(-r1)*(-r2)==r1*r2``.
  Intros; Ring.
Save.
Hints Resolve Ropp_mul2 : real.

(*s Substraction *)

Lemma minus_R0:(r:R)``r-0==r``.
Intro;Ring.
Save.
Hints Resolve minus_R0 : real.

Lemma Rminus_Ropp:(r:R)``0-r==-r``.
Intro;Ring.
Save.
Hints Resolve Rminus_Ropp : real.

(**********)
Lemma Ropp_distr2:(r1,r2:R)``-(r1-r2)==r2-r1``.
  Intros; Ring.
Save.
Hints Resolve Ropp_distr2 : real.

Lemma Ropp_distr3:(r1,r2:R)``-(r2-r1)==r1-r2``.
Intros; Ring.
Save.
Hints Resolve Ropp_distr3 : real. 

(**********)
Lemma eq_Rminus:(r1,r2:R)(r1==r2)->``r1-r2==0``.
  Intros; Rewrite H; Ring.
Save.
Hints Resolve eq_Rminus : real.

(**********)
Lemma Rminus_eq:(r1,r2:R)``r1-r2==0`` -> r1==r2.
  Intros r1 r2; Unfold Rminus; Rewrite -> Rplus_sym; Intro.
  Rewrite <- (Ropp_Ropp r2); Apply (Rplus_Ropp (Ropp r2) r1 H).
Save.
Hints Immediate Rminus_eq : real.

Lemma Rminus_eq_right:(r1,r2:R)``r2-r1==0`` -> r1==r2.
Intros;Generalize (Rminus_eq r2 r1 H);Clear H;Intro H;Rewrite H;Ring.
Save.
Hints Immediate Rminus_eq_right : real.

(**********)
Lemma Rminus_eq_contra:(r1,r2:R)``r1<>r2``->``r1-r2<>0``.
Red; Intros r1 r2 H H0.
Apply H; Auto with real.
Save.
Hints Resolve Rminus_eq_contra : real.

Lemma Rminus_not_eq:(r1,r2:R)``r1-r2<>0``->``r1<>r2``.
Red; Intros; Elim H; Apply eq_Rminus; Auto.
Save.
Hints Resolve Rminus_not_eq : real.

Lemma Rminus_not_eq_right:(r1,r2:R)``r2-r1<>0`` -> ``r1<>r2``.
Red; Intros;Elim H;Rewrite H0; Ring.
Save.
Hints Resolve Rminus_not_eq_right : real. 

(**********)
Lemma Rminus_distr:  (x,y,z:R) ``x*(y-z)==(x*y) - (x*z)``.
Intros; Ring.
Save.

(*s Inverse *)
Lemma Rinv_R1:``/1==1``.
Apply (r_Rmult_mult ``1`` ``/1`` ``1``); Auto with real.
Rewrite (Rinv_r R1 R1_neq_R0);Auto with real.
Save.
Hints Resolve Rinv_R1 : real.

(*********)
Lemma Rinv_neq_R0:(r:R)``r<>0``->``(/r)<>0``.
Red; Intros; Apply R1_neq_R0.
Replace ``1`` with ``(/r) * r``; Auto with real.
Save.
Hints Resolve Rinv_neq_R0 : real.

(*********)
Lemma Rinv_Rinv:(r:R)``r<>0``->``/(/r)==r``.
Intros;Apply (r_Rmult_mult ``/r``); Auto with real.
Transitivity ``1``; Auto with real.
Save.
Hints Resolve Rinv_Rinv : real.

(*********)
Lemma Rinv_Rmult:(r1,r2:R)``r1<>0``->``r2<>0``->``/(r1*r2)==(/r1)*(/r2)``.
Intros; Apply (r_Rmult_mult ``r1*r2``);Auto with real.
Transitivity ``1``; Auto with real.
Transitivity ``(r1*/r1)*(r2*(/r2))``; Auto with real.
Rewrite Rinv_r; Trivial.
Rewrite Rinv_r; Auto with real.
Ring.
Save.

(*********)
Lemma Ropp_Rinv:(r:R)``r<>0``->``-(/r)==/(-r)``.
Intros; Apply (r_Rmult_mult ``-r``);Auto with real.
Transitivity ``1``; Auto with real.
Rewrite (Ropp_mul2 r ``/r``); Auto with real.
Save.

Lemma Rinv_r_simpl_r : (r1,r2:R)``r1<>0``->``r1*(/r1)*r2==r2``.
Intros; Transitivity ``1*r2``; Auto with real.
Rewrite Rinv_r; Auto with real.
Save.

Lemma Rinv_r_simpl_l : (r1,r2:R)``r1<>0``->``r2*r1*(/r1)==r2``.
Intros; Transitivity ``r2*1``; Auto with real.
Transitivity ``r2*(r1*/r1)``; Auto with real.
Save.

Lemma Rinv_r_simpl_m : (r1,r2:R)``r1<>0``->``r1*r2*(/r1)==r2``.
Intros; Transitivity ``r2*1``; Auto with real.
Transitivity ``r2*(r1*/r1)``; Auto with real.
Ring.
Save.
Hints Resolve Rinv_r_simpl_l Rinv_r_simpl_r Rinv_r_simpl_m : real.

(*********)
Lemma Rinv_Rmult_simpl:(a,b,c:R)``a<>0``->``(a*(/b))*(c*(/a))==c*(/b)``.
Intros.
Transitivity ``(a*/a)*(c*(/b))``; Auto with real.
Ring.
Save.

(*s Order and addition *)

Lemma Rlt_compatibility_r:(r,r1,r2:R)``r1<r2``->``r1+r<r2+r``.
Intros.
Rewrite (Rplus_sym r1 r); Rewrite (Rplus_sym r2 r); Auto with real.
Save.

Hints Resolve Rlt_compatibility_r : real.

(**********)
Lemma Rlt_anti_compatibility:  (r,r1,r2:R)``r+r1 < r+r2`` -> ``r1<r2``.
Intros; Cut ``(-r+r)+r1 < (-r+r)+r2``.
Rewrite -> Rplus_Ropp_l.
Elim (Rplus_ne r1); Elim (Rplus_ne r2); Intros; Rewrite <- H3;
 Rewrite <- H1; Auto with zarith real.
Rewrite -> Rplus_assoc; Rewrite -> Rplus_assoc;
 Apply (Rlt_compatibility ``-r`` ``r+r1`` ``r+r2`` H).
Save.

(**********)
Lemma Rle_compatibility:(r,r1,r2:R)``r1<=r2`` -> ``r+r1 <= r+r2 ``.
Unfold Rle; Intros; Elim H; Intro.
Left; Apply (Rlt_compatibility r r1 r2 H0).
Right; Rewrite <- H0; Auto with zarith real.
Save.

(**********)
Lemma Rle_compatibility_r:(r,r1,r2:R)``r1<=r2`` -> ``r1+r<=r2+r``.
Unfold Rle; Intros; Elim H; Intro.
Left; Apply (Rlt_compatibility_r r r1 r2 H0).
Right; Rewrite <- H0; Auto with real.
Save.

Hints Resolve Rle_compatibility Rle_compatibility_r : real.

(**********)
Lemma Rle_anti_compatibility: (r,r1,r2:R)``r+r1<=r+r2`` -> ``r1<=r2``.
Unfold Rle; Intros; Elim H; Intro.
Left; Apply (Rlt_anti_compatibility r r1 r2 H0).
Right; Apply (r_Rplus_plus r r1 r2 H0).
Save.

(**********)
Lemma sum_inequa_Rle_lt:(a,x,b,c,y,d:R)``a<=x`` -> ``x<b`` ->
           ``c<y`` -> ``y<=d`` -> ``a+c < x+y < b+d``.
Intros;Split.
Apply Rlt_le_trans with ``a+y``; Auto with real.
Apply Rlt_le_trans with ``b+y``; Auto with real.
Save.

(*********)
Lemma Rplus_lt:(r1,r2,r3,r4:R)``r1<r2`` -> ``r3<r4`` -> ``r1+r3 < r2+r4``.
Intros; Apply Rlt_trans with ``r2+r3``; Auto with real.
Save.

(*********)
Lemma Rplus_lt_le_lt:(r1,r2,r3,r4:R)``r1<r2`` -> ``r3<=r4`` -> ``r1+r3 < r2+r4``.
Intros; Apply Rlt_le_trans with ``r2+r3``; Auto with real.
Save.

(*********)
Lemma Rplus_le_lt_lt:(r1,r2,r3,r4:R)``r1<=r2`` -> ``r3<r4`` -> ``r1+r3 < r2+r4``.
Intros; Apply Rle_lt_trans with ``r2+r3``; Auto with real.
Save.

Hints Immediate Rplus_lt Rplus_lt_le_lt Rplus_le_lt_lt : real.

(*s Order and Opposite *)

(**********)
Lemma Rgt_Ropp:(r1,r2:R) ``r1 > r2`` -> ``-r1 < -r2``.
Unfold Rgt; Intros.
Apply (Rlt_anti_compatibility ``r2+r1``).
Replace ``r2+r1+(-r1)`` with r2.
Replace ``r2+r1+(-r2)`` with r1.
Trivial.
Ring.
Ring.
Save.
Hints Resolve Rgt_Ropp.

(**********)
Lemma Rlt_Ropp:(r1,r2:R) ``r1 < r2`` -> ``-r1 > -r2``.
Unfold Rgt; Auto with real.
Save.
Hints Resolve Rlt_Ropp : real.

(**********)
Lemma Rle_Ropp:(r1,r2:R) ``r1 <= r2`` -> ``-r1 >= -r2``.
Unfold Rge; Intros r1 r2 [H|H]; Auto with real.
Save.
Hints Resolve Rle_Ropp : real.

(**********)
Lemma Rge_Ropp:(r1,r2:R) ``r1 >= r2`` -> ``-r1 <= -r2``.
Unfold Rge; Intros r1 r2 [H|H]; Auto with real.
Red; Auto with real.
Save.
Hints Resolve Rge_Ropp : real.

(**********)
Lemma Rlt_RO_Ropp:(r:R) ``0 < r`` -> ``0 > -r``.
Intros; Replace ``0`` with ``-0``; Auto with real.
Save.
Hints Resolve Rlt_RO_Ropp : real.

(**********)
Lemma Rgt_RO_Ropp:(r:R) ``0 > r`` -> ``0 < -r``.
Intros; Replace ``0`` with ``-0``; Auto with real.
Save.
Hints Resolve Rgt_RO_Ropp : real.

(**********)
Lemma Rle_RO_Ropp:(r:R) ``0 <= r`` -> ``0 >= -r``.
Intros; Replace ``0`` with ``-0``; Auto with real.
Save.
Hints Resolve Rle_RO_Ropp : real.

(**********)
Lemma Rge_RO_Ropp:(r:R) ``0 >= r`` -> ``0 <= -r``.
Intros; Replace ``0`` with ``-0``; Auto with real.
Save.
Hints Resolve Rge_RO_Ropp : real.

(*s Order and multiplication *)

Lemma  Rlt_monotony_r:(r,r1,r2:R)``0<r`` -> ``r1 < r2`` -> ``r1*r < r2*r``.
Intros; Rewrite (Rmult_sym r1 r); Rewrite (Rmult_sym r2 r); Auto with real.
Save.
Hints Resolve Rlt_monotony_r.

Lemma Rlt_anti_monotony:(r,r1,r2:R)``r < 0`` -> ``r1 < r2`` -> ``r*r1 > r*r2``.
Intros; Replace r with ``-(-r)``; Auto with real.
Rewrite (Ropp_mul1 ``-r``); Rewrite (Ropp_mul1 ``-r``).
Apply Rlt_Ropp; Auto with real.
Save.

(**********)
Lemma Rle_monotony: 
  (r,r1,r2:R)``0 <= r`` -> ``r1 <= r2`` -> ``r*r1 <= r*r2``.
Intros r r1 r2;Unfold Rle;Intros H H0;Elim H;Elim H0;Intros; Auto with real.
Right;Rewrite <- H2;Ring.
Save.
Hints Resolve Rle_monotony : real.

Lemma Rle_monotony_r: 
  (r,r1,r2:R)``0 <= r`` -> ``r1 <= r2`` -> ``r1*r <= r2*r``.
Intros r r1 r2 H;
Rewrite (Rmult_sym r1 r); Rewrite (Rmult_sym r2 r); Auto with real.
Save.
Hints Resolve Rle_monotony_r : real.

Lemma Rle_anti_monotony
	:(r,r1,r2:R)``r <= 0`` -> ``r1 <= r2`` -> ``r*r1 >= r*r2``.
Intros; Replace r with ``-(-r)``; Auto with real.
Rewrite (Ropp_mul1 ``-r``); Rewrite (Ropp_mul1 ``-r``).
Apply Rle_Ropp; Auto with real.
Save.
Hints Resolve Rle_anti_monotony : real.



Lemma Rmult_lt:(r1,r2,r3,r4:R)``r3>0`` -> ``r2>0`` ->
  `` r1 < r2`` -> ``r3 < r4`` -> ``r1*r3 < r2*r4``.
Intros; Apply Rlt_trans with ``r2*r3``; Auto with real.
Save.

(*s Order and Substractions *)
Lemma Rlt_minus:(r1,r2:R)``r1 < r2`` -> ``r1-r2 < 0``.
Intros; Apply (Rlt_anti_compatibility ``r2``).
Replace ``r2+(r1-r2)`` with r1.
Replace  ``r2+0`` with r2; Auto with real.
Ring.
Save.
Hints Resolve Rlt_minus : real.

(**********)
Lemma Rle_minus:(r1,r2:R)``r1 <= r2`` -> ``r1-r2 <= 0``.
Unfold Rle; Intros; Elim H; Auto with real.
Save.

(**********)
Lemma Rminus_lt:(r1,r2:R)``r1-r2 < 0`` -> ``r1 < r2``.
Intros; Replace r1 with ``r1-r2+r2``.
Pattern 3 r2; Replace r2 with ``0+r2``; Auto with real.
Ring.
Save.

(**********)
Lemma Rminus_le:(r1,r2:R)``r1-r2 <= 0`` -> ``r1 <= r2``.
Intros; Replace r1 with ``r1-r2+r2``.
Pattern 3 r2; Replace r2 with ``0+r2``; Auto with real.
Ring.
Save.


(**********)
Lemma tech_Rplus:(r,s:R)``0<=r`` -> ``0<s`` -> ``r+s<>0``.
Intros; Apply sym_not_eqT; Apply Rlt_not_eq.
Rewrite Rplus_sym; Replace ``0`` with ``0+0``; Auto with real.
Save.
Hints Immediate tech_Rplus : real.

(*s Order and the square function *)
Lemma pos_Rsqr:(r:R)``0<=(Rsqr r)``.
Intro; Case (total_order_Rlt_Rle r ``0``); Unfold Rsqr; Intro.
Replace ``r*r`` with ``(-r)*(-r)``; Auto with real.
Replace ``0`` with ``-r*0``; Auto with real.
Replace ``0`` with ``0*r``; Auto with real.
Save.

(***********)
Lemma pos_Rsqr1:(r:R)``r<>0``->``0<(Rsqr r)``.
Intros; Case (not_Req r ``0``); Trivial; Unfold Rsqr; Intro.
Replace ``r*r`` with ``(-r)*(-r)``; Auto with real.
Replace ``0`` with ``-r*0``; Auto with real.
Replace ``0`` with ``0*r``; Auto with real.
Save.
Hints Resolve pos_Rsqr pos_Rsqr1 : real.

(*s Zero is less than one *)
Lemma Rlt_R0_R1:``0<1``.
Replace ``1`` with ``(Rsqr 1)``; Auto with real.
Unfold Rsqr; Auto with real.
Save.
Hints Resolve Rlt_R0_R1 : real.

(*s Order and inverse *)
Lemma Rlt_Rinv:(r:R)``0<r``->``0</r``.
Intros; Change ``/r>0``; Apply not_Rle; Red; Intros.
Absurd ``1<=0``; Auto with real.
Replace ``1`` with ``r*(/r)``; Auto with real.
Replace ``0`` with ``r*0``; Auto with real.
Save.
Hints Resolve Rlt_Rinv : real.

(*********)
Lemma Rlt_Rinv2:(r:R)``r < 0``->``/r < 0``.
Intros; Change ``0>/r``; Apply not_Rle; Red; Intros.
Absurd ``1<=0``; Auto with real.
Replace ``1`` with ``r*(/r)``; Auto with real.
Replace ``0`` with ``r*0``; Auto with real.
Apply Rge_le; Auto with real.
Save.
Hints Resolve Rlt_Rinv2 : real.

(**********)
Lemma Rlt_monotony_rev:
  (r,r1,r2:R)``0<r`` -> ``r*r1 < r*r2`` -> ``r1 < r2``.
Intros; Replace r1 with ``/r*(r*r1)``.
Replace r2 with ``/r*(r*r2)``; Auto with real.
Transitivity ``r*/r*r2``; Auto with real.
Ring.
Transitivity ``r*/r*r1``; Auto with real.
Ring.
Save.

(*********)
Lemma Rinv_lt:(r1,r2:R)``0 < r1*r2`` -> ``r1 < r2`` -> ``/r2 < /r1``.
Intros; Apply Rlt_monotony_rev with ``r1*r2``; Auto with real.
Case (without_div_O_contr r1 r2 ); Intros; Auto with real.
Replace ``r1*r2*/r2`` with r1.
Replace ``r1*r2*/r1`` with r2; Trivial.
Symmetry; Auto with real.
Symmetry; Auto with real.
Save.


(*********************************************************)        
(*s      Greater                                         *)
(*********************************************************)

(**********)
Lemma Rge_ge_eq:(r1,r2:R)``r1 >= r2`` -> ``r2 >= r1`` -> r1==r2.
Intros; Apply Rle_antisym; Auto with real.
Save.

(**********)
Lemma Rlt_not_ge:(r1,r2:R)~(``r1<r2``)->``r1>=r2``.
Intros; Unfold Rge; Elim (total_order r1 r2); Intro.
Absurd ``r1<r2``; Trivial.
Case H0; Auto.
Save.

(**********)
Lemma Rgt_not_le:(r1,r2:R)~(``r1>r2``)->``r1<=r2``.
Intros r1 r2 H; Apply Rge_le.
Exact (Rlt_not_ge r2 r1 H).
Save.

(**********)
Lemma Rgt_ge:(r1,r2:R)``r1>r2`` -> ``r1 >= r2``.
Red; Auto with real.
Save.

(**********)
Lemma Rlt_sym:(r1,r2:R)``r1<r2`` <-> ``r2>r1``.
Split; Unfold Rgt; Auto with real.
Save.

(**********)
Lemma Rle_sym1:(r1,r2:R)``r1<=r2``->``r2>=r1``.
Proof Rle_ge.

(**********)
Lemma Rle_sym2:(r1,r2:R)``r2>=r1`` -> ``r1<=r2``.
Proof [r1,r2](Rge_le r2 r1).

(**********)
Lemma Rle_sym:(r1,r2:R)``r1<=r2``<->``r2>=r1``.
Split; Auto with real.
Save.

(**********)
Lemma Rge_gt_trans:(r1,r2,r3:R)``r1>=r2``->``r2>r3``->``r1>r3``.
Unfold Rgt; Intros; Apply Rlt_le_trans with r2; Auto with real.
Save.

(**********)
Lemma Rgt_ge_trans:(r1,r2,r3:R)``r1>r2`` -> ``r2>=r3`` -> ``r1>r3``.
Unfold Rgt; Intros; Apply Rle_lt_trans with r2; Auto with real.
Save.

(**********)
Lemma Rgt_trans:(r1,r2,r3:R)``r1>r2`` -> ``r2>r3`` -> ``r1>r3``.
Unfold Rgt; Intros; Apply Rlt_trans with r2; Auto with real.
Save.

(**********)
Lemma Rge_trans:(r1,r2,r3:R)``r1>=r2`` -> ``r2>=r3`` -> ``r1>=r3``.
Intros; Apply Rle_ge.
Apply Rle_trans with r2; Auto with real.
Save.

(**********)
Lemma Rgt_RoppO:(r:R)``r>0``->``(-r)<0``.
Intros; Rewrite <- Ropp_O; Auto with real.
Save.

(**********)
Lemma Rlt_RoppO:(r:R)``r<0``->``-r>0``.
Intros; Rewrite <- Ropp_O; Auto with real.
Save.
Hints Resolve Rgt_RoppO Rlt_RoppO: real.

(**********)
Lemma Rlt_r_plus_R1:(r:R)``0<=r`` -> ``0<r+1``.
Intros.
Apply Rlt_le_trans with ``1``; Auto with real.
Pattern 1 ``1``; Replace ``1`` with ``0+1``; Auto with real.
Save.
Hints Resolve Rlt_r_plus_R1: real.

(**********)
Lemma Rlt_r_r_plus_R1:(r:R)``r<r+1``.
Intros.
Pattern 1 r; Replace r with ``r+0``; Auto with real.
Save.
Hints Resolve Rlt_r_r_plus_R1: real.


(**********)
Lemma tech_Rgt_minus:(r1,r2:R)``0<r2``->``r1>r1-r2``.
Red; Unfold Rminus; Intros.
Pattern 2 r1; Replace r1 with ``r1+0``; Auto with real.
Save.

(***********)
Lemma Rgt_plus_plus_r:(r,r1,r2:R)``r1>r2``->``r+r1 > r+r2``.
Unfold Rgt; Auto with real.
Save.
Hints Resolve Rgt_plus_plus_r : real.

(***********)
Lemma Rgt_r_plus_plus:(r,r1,r2:R)``r+r1 > r+r2`` -> ``r1 > r2``.
Unfold Rgt; Intros; Apply (Rlt_anti_compatibility r r2 r1 H).
Save.

(***********)
Lemma Rge_plus_plus_r:(r,r1,r2:R)``r1>=r2`` -> ``r+r1 >= r+r2``.
Intros; Apply Rle_ge; Auto with real.
Save.
Hints Resolve Rge_plus_plus_r : real.

(***********)
Lemma Rge_r_plus_plus:(r,r1,r2:R)``r+r1 >= r+r2`` -> ``r1>=r2``.
Intros; Apply Rle_ge; Apply Rle_anti_compatibility with r; Auto with real.
Save.

(***********)
Lemma Rge_monotony:
 (x,y,z:R) ``z>=0`` -> ``x>=y`` -> ``x*z >= y*z``.
Intros; Apply Rle_ge; Auto with real.
Save.

(***********)
Lemma Rgt_minus:(r1,r2:R)``r1>r2`` -> ``r1-r2 > 0``.
Intros; Replace ``0`` with ``r2-r2``; Auto with real.
Unfold Rgt Rminus; Auto with real.
Save.

(*********)
Lemma minus_Rgt:(r1,r2:R)``r1-r2 > 0`` -> ``r1>r2``.
Intros; Replace r2 with ``r2+0``; Auto with real.
Intros; Replace r1 with ``r2+(r1-r2)``; Auto with real.
Ring.
Save.

(**********)
Lemma Rge_minus:(r1,r2:R)``r1>=r2`` -> ``r1-r2 >= 0``.
Unfold Rge; Intros; Elim H; Intro.
Left; Apply (Rgt_minus r1 r2 H0).
Right; Apply (eq_Rminus r1 r2 H0).
Save.

(*********)
Lemma minus_Rge:(r1,r2:R)``r1-r2 >= 0`` -> ``r1>=r2``.
Intros; Replace r2 with ``r2+0``; Auto with real.
Intros; Replace r1 with ``r2+(r1-r2)``; Auto with real.
Ring.
Save.


(*********)
Lemma Rmult_gt:(r1,r2:R)``r1>0`` -> ``r2>0`` -> ``r1*r2>0``.
Unfold Rgt;Intros.
Replace ``0`` with ``0*r2``; Auto with real.
Save.

(*********)
Lemma Rmult_lt_0
  :(r1,r2,r3,r4:R)``r3>=0``->``r2>0``->``r1<r2``->``r3<r4``->``r1*r3<r2*r4``.
Intros; Apply Rle_lt_trans with ``r2*r3``; Auto with real.
Save.

(*********)
Lemma Rmult_lt_pos:(x,y:R)``0<x`` -> ``0<y`` -> ``0<x*y``.
Proof Rmult_gt.

(***********)
Lemma Rplus_eq_R0_l:(a,b:R)``0<=a`` -> ``0<=b`` -> ``a+b==0`` -> ``a==0``.
Intros a b [H|H] H0 H1; Auto with real.
Absurd ``0<a+b``.
Rewrite H1; Auto with real.
Replace ``0`` with ``0+0``; Auto with real.
Save.


Lemma Rplus_eq_R0
	:(a,b:R)``0<=a`` -> ``0<=b`` -> ``a+b==0`` -> ``a==0``/\``b==0``.
Split.
Apply Rplus_eq_R0_l with b; Auto with real.
Apply Rplus_eq_R0_l with a; Auto with real.
Rewrite Rplus_sym; Auto with real.
Save.


(***********)
Lemma Rplus_Rsr_eq_R0_l:(a,b:R)``(Rsqr a)+(Rsqr b)==0``->``a==0``.
Intros; Apply Rsqr_r_R0; Apply Rplus_eq_R0_l with (Rsqr b); Auto with real.
Save.

Lemma Rplus_Rsr_eq_R0:(a,b:R)``(Rsqr a)+(Rsqr b)==0``->``a==0``/\``b==0``.
Split.
Apply Rplus_Rsr_eq_R0_l with b; Auto with real.
Apply Rplus_Rsr_eq_R0_l with a; Auto with real.
Rewrite Rplus_sym; Auto with real.
Save.


(**********************************************************) 
(*s       Injection from N to R                           *)
(**********************************************************)

(**********)
Lemma S_INR:(n:nat)(INR (S n))==``(INR n)+1``.
Intro; Case n; Auto with real.
Save.

(**********)
Lemma S_O_plus_INR:(n:nat)
    (INR (plus (S O) n))==``(INR (S O))+(INR n)``.
Intro; Simpl; Case n; Intros; Auto with real.
Save.

(**********)
Lemma plus_INR:(n,m:nat)(INR (plus n m))==``(INR n)+(INR m)``. 
Intros n m; Induction n.
Simpl; Auto with real.
Replace (plus (S n) m) with (S (plus n m)); Auto with arith.
Repeat Rewrite S_INR.
Rewrite Hrecn; Ring.
Save.


(**********)
Lemma minus_INR:(n,m:nat)(le m n)->(INR (minus n m))==``(INR n)-(INR m)``.
Intros n m le; Pattern m n; Apply le_elim_rel; Auto with real.
Intros; Rewrite <- minus_n_O; Auto with real.
Intros; Repeat Rewrite S_INR; Simpl.
Rewrite H0; Ring.
Save.

(*********)
Lemma mult_INR:(n,m:nat)(INR (mult n m))==(Rmult (INR n) (INR m)).
Intros n m; Induction n.
Simpl; Auto with real.
Intros; Repeat Rewrite S_INR; Simpl.
Rewrite plus_INR; Rewrite Hrecn; Ring.
Save.

Hints Resolve plus_INR minus_INR mult_INR : real.

(*********)
Lemma INR_lt_0:(n:nat)(lt O n)->``0 < (INR n)``.
Induction 1; Intros; Auto with real.
Rewrite S_INR; Auto with real.
Save.
Hints Resolve INR_lt_0: real.

(**********)
Lemma INR_pos : (p:positive)``0<(INR (convert p))``.
Intro; Apply INR_lt_0.
Simpl; Auto with real.
Apply compare_convert_O.
Save.
Hints Resolve INR_pos : real.

(**********)
Lemma INR_le:(n:nat)``0 <= (INR n)``.
Intro n; Case n.
Simpl; Auto with real.
Auto with arith real.
Save.
Hints Resolve INR_le: real.

(*********)
Lemma INR_le_nm:(n,m:nat)(le n m)->``(INR n)<=(INR m)``.
Induction 1; Intros; Auto with real.
Rewrite S_INR.
Apply Rle_trans with (INR m0); Auto with real.
Save.
Hints Resolve INR_le_nm: real.

(**********)
Lemma not_INR_O:(n:nat)``(INR n)<>0``->~n=O.
Red; Intros n H H1.
Apply H.
Rewrite H1; Trivial.
Save.
Hints Immediate not_INR_O : real.


(**********)
Lemma not_O_INR:(n:nat)~n=O->``(INR n)<>0``.
Intro n; Case n.
Intro; Absurd (0)=(0); Trivial.
Intros; Rewrite S_INR.
Apply Rgt_not_eq; Red; Auto with real.
Save.
Hints Resolve not_O_INR : real.



(**********************************************************) 
(*s      Injection from Z to R                            *)
(**********************************************************)

(**********)
Definition INZ:=inject_nat.

(**********)
Lemma IZN:(z:Z)(`0<=z`)->(Ex [n:nat] z=(INZ n)).
Unfold INZ;Intros;Apply inject_nat_complete;Assumption.
Save.

(**********)
Lemma INR_IZR_INZ:(n:nat)(INR n)==(IZR (INZ n)).
Induction n; Auto with real.
Intros; Simpl; Rewrite bij1; Auto with real.
Save.

Lemma  plus_IZR_NEG_POS : 
	(p,q:positive)(IZR `(POS p)+(NEG q)`)==``(IZR (POS p))+(IZR (NEG q))``.
Intros.
Case (lt_eq_lt_dec (convert p) (convert q)).
Intros [H | H]; Simpl.
Rewrite convert_compare_INFERIEUR; Simpl; Trivial.
Rewrite (true_sub_convert q p).
Rewrite minus_INR; Auto with arith; Ring.
Apply ZC2; Apply convert_compare_INFERIEUR; Trivial.
Rewrite (convert_intro p q); Trivial.
Rewrite convert_compare_EGAL; Simpl; Auto with real.
Intro H; Simpl.
Rewrite convert_compare_SUPERIEUR; Simpl; Auto with arith.
Rewrite (true_sub_convert p q).
Rewrite minus_INR; Auto with arith; Ring.
Apply ZC2; Apply convert_compare_INFERIEUR; Trivial.
Save.

(**********)
Lemma plus_IZR:(z,t:Z)(IZR `z+t`)==``(IZR z)+(IZR t)``.
Destruct z; Destruct t; Intros; Auto with real.
Simpl; Intros; Rewrite convert_add; Auto with real.
Apply plus_IZR_NEG_POS.
Rewrite Zplus_sym; Rewrite Rplus_sym; Apply plus_IZR_NEG_POS.
Simpl; Intros; Rewrite convert_add; Rewrite plus_INR; Auto with real.
Save.

(**********)
Lemma Ropp_Ropp_IZR:(z:Z)(IZR (`-z`))==``-(IZR z)``.
Intro z; Case z; Simpl; Auto with real.
Save.

(**********)
Lemma Z_R_minus:(z1,z2:Z)``(IZR z1)-(IZR z2)``==(IZR `z1-z2`).
Intros; Unfold Rminus; Unfold Zminus.
Rewrite <-(Ropp_Ropp_IZR z2); Symmetry; Apply plus_IZR.
Save. 

(**********)
Lemma lt_O_IZR:(z:Z)``0 < (IZR z)``->`0<z`.
Intro z; Case z; Simpl; Intros.
Absurd ``0<0``; Auto with real.
Unfold Zlt; Simpl; Trivial.
Case Rlt_le_not with 1:=H.
Replace ``0`` with ``-0``; Auto with real.
Save.

(**********)
Lemma lt_IZR:(z1,z2:Z)``(IZR z1)<(IZR z2)``->`z1<z2`.
Intros; Apply Zlt_O_minus_lt. 
Apply lt_O_IZR.
Rewrite <- Z_R_minus.
Exact (Rgt_minus (IZR z2) (IZR z1) H).
Save.

(**********)
Lemma eq_IZR_R0:(z:Z)``(IZR z)==0``->`z=0`.
Destruct z; Simpl; Intros; Auto with zarith.
Case (Rlt_not_eq ``0`` (INR (convert p))); Auto with real.
Case (Rlt_not_eq ``-(INR (convert p))`` ``0`` ); Auto with real.
Apply Rgt_RoppO; Red; Auto with real.
Save.

(**********)
Lemma eq_IZR:(z1,z2:Z)(IZR z1)==(IZR z2)->z1=z2.
Intros;Generalize (eq_Rminus (IZR z1) (IZR z2) H);
 Rewrite (Z_R_minus z1 z2);Intro;Generalize (eq_IZR_R0 `z1-z2` H0);
 Intro;Omega.
Save.

(*********)
Lemma le_O_IZR:(z:Z)``0<= (IZR z)``->`0<=z`.
Unfold Rle; Intros z [H|H].
Red;Intro;Apply (Zlt_le_weak `0` z (lt_O_IZR z H)); Assumption.
Rewrite (eq_IZR_R0 z); Auto with zarith real.
Save.

(**********)
Lemma le_IZR:(z1,z2:Z)``(IZR z1)<=(IZR z2)``->`z1<=z2`.
Unfold Rle; Intros z1 z2 [H|H].
Apply (Zlt_le_weak z1 z2); Auto with real.
Apply lt_IZR; Trivial.
Rewrite (eq_IZR z1 z2); Auto with zarith real.
Save.

(**********)
Lemma le_IZR_R1:(z:Z)``(IZR z)<=1``-> `z<=1`.
Pattern 1 ``1``; Replace ``1`` with (IZR `1`); Intros; Auto.
Apply le_IZR; Trivial.
Save.

(**********)
Lemma IZR_ge: (m,n:Z) `m>= n` -> ``(IZR m)>=(IZR n)``.
Intros;Apply Rlt_not_ge;Red;Intro.
Generalize (lt_IZR m n H0); Intro; Omega.
Save.

Lemma one_IZR_lt1 : (z:Z)``-1<(IZR z)<1``->`z=0`.
Intros z (H1,H2).
Apply Zle_antisym.
Apply Zlt_n_Sm_le; Apply lt_IZR; Trivial.
Replace `0` with (Zs `-1`); Trivial.
Apply Zlt_le_S; Apply lt_IZR; Trivial.
Save.

Lemma one_IZR_r_R1
  : (r:R)(z,x:Z)``r<(IZR z)<=r+1``->``r<(IZR x)<=r+1``->z=x.
Intros r z x (H1,H2) (H3,H4).
Cut `z-x=0`; Auto with zarith.
Apply one_IZR_lt1.
Rewrite <- Z_R_minus; Split.
Replace ``-1`` with ``r-(r+1)``.
Unfold Rminus; Apply Rplus_lt_le_lt; Auto with real.
Ring.
Replace ``1`` with ``(r+1)-r``.
Unfold Rminus; Apply Rplus_le_lt_lt; Auto with real.
Ring.
Save.


(**********)
Lemma single_z_r_R1
  : (r:R)(z,x:Z)``r<(IZR z)``->``(IZR z)<=r+1``->``r<(IZR x)``->``(IZR x)<=r+1``
    ->z=x.
Intros; Apply one_IZR_r_R1 with r; Auto.
Save.

(**********)
Lemma tech_single_z_r_R1
	:(r:R)(z:Z)``r<(IZR z)``->``(IZR z)<=r+1``
         -> (Ex [s:Z] (~s=z/\``r<(IZR s)``/\``(IZR s)<=r+1``))->False.
Intros r z H1 H2 (s, (H3,(H4,H5))).
Apply H3; Apply single_z_r_R1 with r; Trivial.
Save.

