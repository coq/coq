(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(***************************************************************************)
(**              Basic lemmas for the classical reals numbers              *)
(***************************************************************************)

Require Export Raxioms.
Require Export ZArithRing.
Require Omega.
Require Export Field.

(***************************************************************************)
(**       Instantiating Ring tactic on reals                               *)
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
(**  Relation between orders and equality                                 *)
(**************************************************************************)

(**********)
Lemma Rlt_antirefl:(r:R)~``r<r``.
  Generalize Rlt_antisym. Intuition EAuto.
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
Generalize Rlt_not_eq Rgt_not_eq. Intuition EAuto.
Save.
Hints Resolve imp_not_Req : real.

(** Reasoning by case on equalities and order *)

(**********)
Lemma Req_EM:(r1,r2:R)(r1==r2)\/``r1<>r2``.
Intros ; Generalize (total_order_T r1 r2) ; Intuition EAuto with real.
Save.
Hints Resolve Req_EM : real.

(**********)
Lemma total_order:(r1,r2:R)``r1<r2``\/(r1==r2)\/``r1>r2``.
Intros;Generalize (total_order_T r1 r2);Tauto.
Save.

(**********)
Lemma not_Req:(r1,r2:R)``r1<>r2``->(``r1<r2``\/``r1>r2``).
Intros; Generalize (total_order_T r1 r2) ; Tauto.
Save.


(*********************************************************************************)
(**       Order Lemma  : relating [<], [>], [<=] and [>=]  	                 *)
(*********************************************************************************)

(**********)
Lemma Rlt_le:(r1,r2:R)``r1<r2``-> ``r1<=r2``.
Intuition Auto.
Save.
Hints Resolve Rlt_le : real.

(**********)
Lemma Rle_ge : (r1,r2:R)``r1<=r2`` -> ``r2>=r1``.
NewDestruct 1; Red; Auto with real.
Save.

(**********)
Lemma Rge_le : (r1,r2:R)``r1>=r2`` -> ``r2<=r1``.
NewDestruct 1; Red; Auto with real.
Save.

(**********)
Lemma not_Rle:(r1,r2:R)~(``r1<=r2``)->``r1>r2``.
Intros r1 r2 ; Generalize (total_order r1 r2) ; Tauto.
Save.

Hints Immediate Rle_ge Rge_le not_Rle : real.

(**********)
Lemma Rlt_le_not:(r1,r2:R)``r2<r1``->~(``r1<=r2``).
Intros r1 r2 ; Generalize (Rlt_antisym r1 r2) (imp_not_Req r1 r2) ; Intuition.
Save.

Lemma Rle_not:(r1,r2:R)``r1>r2`` -> ~(``r1<=r2``).
Proof Rlt_le_not.

Hints Immediate Rlt_le_not : real.

Lemma Rle_not_lt: (r1, r2:R) ``r2 <= r1`` ->~ (``r1<r2``).
Intros r1 r2. Generalize (Rlt_antisym r1 r2) (imp_not_Req r1 r2); Intuition.
Save.

(**********)
Lemma Rlt_ge_not:(r1,r2:R)``r1<r2``->~(``r1>=r2``).
Generalize Rlt_le_not. Intuition EAuto 3.
Save.

Hints Immediate Rlt_ge_not : real.

(**********)
Lemma eq_Rle:(r1,r2:R)r1==r2->``r1<=r2``.
Unfold Rle; Tauto.
Save.
Hints Immediate eq_Rle : real.

Lemma eq_Rge:(r1,r2:R)r1==r2->``r1>=r2``.
Unfold Rge; Tauto.
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
Intros r1 r2; Generalize (Rlt_antisym r1 r2) ; Intuition.
Save.
Hints Resolve Rle_antisym : real.

(**********)
Lemma Rle_le_eq:(r1,r2:R)(``r1<=r2``/\``r2<=r1``)<->(r1==r2).
Intuition.
Save.

Lemma Rlt_rew : (x,x',y,y':R)``x==x'``->``x'<y'`` -> `` y' == y`` -> ``x < y``.
Intros; Replace x with x'; Replace y with y'; Assumption.
Save.

(**********)
Lemma Rle_trans:(r1,r2,r3:R) ``r1<=r2``->``r2<=r3``->``r1<=r3``.
Generalize trans_eqT Rlt_trans Rlt_rew.
Intuition EAuto 2.
Save.

(**********)
Lemma Rle_lt_trans:(r1,r2,r3:R)``r1<=r2``->``r2<r3``->``r1<r3``.
Generalize Rlt_trans Rlt_rew. Intuition EAuto 2.
Save.

(**********)
Lemma Rlt_le_trans:(r1,r2,r3:R)``r1<r2``->``r2<=r3``->``r1<r3``.
Generalize Rlt_trans Rlt_rew; Intuition EAuto 2.
Save.


(** Decidability of the order *)
Lemma total_order_Rlt:(r1,r2:R)(sumboolT ``r1<r2`` ~(``r1<r2``)).
Intros;Generalize (total_order_T r1 r2) (imp_not_Req r1 r2) ; Intuition.
Save.

(**********)
Lemma total_order_Rle:(r1,r2:R)(sumboolT ``r1<=r2`` ~(``r1<=r2``)).
Intros r1 r2; Generalize (total_order_T r1 r2);Intuition EAuto with real.
Save.

(**********)
Lemma total_order_Rgt:(r1,r2:R)(sumboolT ``r1>r2`` ~(``r1>r2``)).
Intros;Unfold Rgt;Intros;Apply total_order_Rlt.
Save.

(**********)
Lemma total_order_Rge:(r1,r2:R)(sumboolT (``r1>=r2``) ~(``r1>=r2``)).
Intros;Generalize (total_order_Rle r2 r1);Intuition.
Save.

Lemma total_order_Rlt_Rle:(r1,r2:R)(sumboolT ``r1<r2`` ``r2<=r1``).
Intros;Generalize (total_order_T r1 r2); Intuition.
Save.

Lemma Rle_or_lt: (n, m:R)(Rle n m) \/ (Rlt m n).
Intros n m; Elim (total_order_Rlt_Rle m n);Auto with real.
Save.

Lemma total_order_Rle_Rlt_eq :(r1,r2:R)``r1<=r2``-> 
                              (sumboolT ``r1<r2`` ``r1==r2``).
Intros r1 r2 H;Generalize (total_order_T r1 r2); Intuition.
Save.

(**********)
Lemma inser_trans_R:(n,m,p,q:R)``n<=m<p``-> (sumboolT ``n<=m<q`` ``q<=m<p``).
Intros; Generalize (total_order_Rlt_Rle m q); Intuition.
Save.

(****************************************************************)
(**        Field Lemmas                                         *)
(* This part contains lemma involving the Fields operations     *)
(****************************************************************)
(*********************************************************)
(**      Addition                                        *)
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
(**       Multiplication                                   *)
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

(** Square function *)

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
(**      Opposite                                        *)
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

(** Opposite and multiplication *)

Lemma Ropp_mul1:(r1,r2:R)``(-r1)*r2 == -(r1*r2)``.
  Intros; Ring.
Save.
Hints Resolve Ropp_mul1 : real.

(**********)
Lemma Ropp_mul2:(r1,r2:R)``(-r1)*(-r2)==r1*r2``.
  Intros; Ring.
Save.
Hints Resolve Ropp_mul2 : real.

(** Substraction *)

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

Lemma Rplus_Rminus: (p,q:R)``p+(q-p)``==q.
Intros; Ring.
Save.
Hints Resolve Rplus_Rminus:real.

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

(** Inverse *)
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

(** Order and addition *)

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

Lemma Rplus_le:(r1,r2,r3,r4:R)``r1<=r2`` -> ``r3<=r4`` -> ``r1+r3 <= r2+r4``.
Intros; Apply Rle_trans with ``r2+r3``; Auto with real.
Save.

(*********)
Lemma Rplus_lt_le_lt:(r1,r2,r3,r4:R)``r1<r2`` -> ``r3<=r4`` -> 
                     ``r1+r3 < r2+r4``.
Intros; Apply Rlt_le_trans with ``r2+r3``; Auto with real.
Save.

(*********)
Lemma Rplus_le_lt_lt:(r1,r2,r3,r4:R)``r1<=r2`` -> ``r3<r4`` -> 
                                    ``r1+r3 < r2+r4``.
Intros; Apply Rle_lt_trans with ``r2+r3``; Auto with real.
Save.

Hints Immediate Rplus_lt Rplus_le Rplus_lt_le_lt Rplus_le_lt_lt : real.

(** Order and Opposite *)

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

Lemma Ropp_Rlt: (x,y:R) ``-y < -x`` ->``x<y``.
Intros x y H'.
Rewrite <- (Ropp_Ropp x); Rewrite <- (Ropp_Ropp y); Auto with real.
Save.
Hints Resolve Ropp_Rlt : real.

Lemma Rlt_Ropp1:(r1,r2:R) ``r2 < r1`` -> ``-r1 < -r2``.
Auto with real.
Save.
Hints Resolve Rlt_Ropp1 : real.

(**********)
Lemma Rle_Ropp:(r1,r2:R) ``r1 <= r2`` -> ``-r1 >= -r2``.
Unfold Rge; Intros r1 r2 [H|H]; Auto with real.
Save.
Hints Resolve Rle_Ropp : real.

Lemma Ropp_Rle: (x,y:R) ``-y <= -x`` ->``x <= y``.
Intros x y H.
Elim H;Auto with real.
Intro H1;Rewrite <-(Ropp_Ropp x);Rewrite <-(Ropp_Ropp y);Rewrite H1;
  Auto with real.
Save.
Hints Resolve Ropp_Rle : real.

Lemma Rle_Ropp1:(r1,r2:R) ``r2 <= r1`` -> ``-r1 <= -r2``.
Intros r1 r2 H;Elim H;Auto with real.
Intro H1;Rewrite H1;Auto with real.
Save.
Hints Resolve Rle_Ropp1 : real.

(**********)
Lemma Rge_Ropp:(r1,r2:R) ``r1 >= r2`` -> ``-r1 <= -r2``.
Unfold Rge; Intros r1 r2 [H|H]; Auto with real.
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

(** Order and multiplication *)

Lemma  Rlt_monotony_r:(r,r1,r2:R)``0<r`` -> ``r1 < r2`` -> ``r1*r < r2*r``.
Intros; Rewrite (Rmult_sym r1 r); Rewrite (Rmult_sym r2 r); Auto with real.
Save.
Hints Resolve Rlt_monotony_r.

Lemma Rlt_monotony_contra:
  (x, y, z:R) ``0<z`` ->``z*x<z*y`` ->``x<y``.
Intros x y z H H0.
Case (total_order x y); Intros Eq0; Auto; Elim Eq0; Clear Eq0; Intros Eq0.
 Rewrite Eq0 in H0;ElimType False;Apply (Rlt_antirefl ``z*y``);Auto.
Generalize (Rlt_monotony z y x H Eq0);Intro;ElimType False;
 Generalize (Rlt_trans ``z*x`` ``z*y`` ``z*x`` H0 H1);Intro;
 Apply (Rlt_antirefl ``z*x``);Auto.
Save.

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

Lemma Rle_monotony_contra:
  (x, y, z:R) ``0<z`` ->``z*x<=z*y`` ->``x<=y``.
Intros x y z H H0;Case H0; Auto with real.
Intros H1; Apply Rlt_le.
Apply Rlt_monotony_contra with z := z;Auto.
Intros H1;Replace x with (Rmult (Rinv z) (Rmult z x)); Auto with real.
Replace y with (Rmult (Rinv z) (Rmult z y)).
 Rewrite H1;Auto with real.
Rewrite <- Rmult_assoc; Rewrite Rinv_l; Auto with real.
Rewrite <- Rmult_assoc; Rewrite Rinv_l; Auto with real.
Save.

Lemma Rle_anti_monotony
	:(r,r1,r2:R)``r <= 0`` -> ``r1 <= r2`` -> ``r*r1 >= r*r2``.
Intros; Replace r with ``-(-r)``; Auto with real.
Rewrite (Ropp_mul1 ``-r``); Rewrite (Ropp_mul1 ``-r``).
Apply Rle_Ropp; Auto with real.
Save.
Hints Resolve Rle_anti_monotony : real.

Lemma Rle_Rmult_comp:
  (x, y, z, t:R) ``0 <= x`` -> ``0 <= z`` -> ``x <= y`` -> ``z <= t`` ->
  ``x*z <= y*t``.
Intros x y z t H' H'0 H'1 H'2.
Apply Rle_trans with r2 := ``x*t``; Auto with real.
Repeat Rewrite [x:?](Rmult_sym x t).
Apply Rle_monotony; Auto.
Apply Rle_trans with z; Auto.
Save.
Hints Resolve Rle_Rmult_comp :real.

Lemma Rmult_lt:(r1,r2,r3,r4:R)``r3>0`` -> ``r2>0`` ->
  `` r1 < r2`` -> ``r3 < r4`` -> ``r1*r3 < r2*r4``.
Intros; Apply Rlt_trans with ``r2*r3``; Auto with real.
Save.

(** Order and Substractions *)
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

(** Order and the square function *)
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

(** Zero is less than one *)
Lemma Rlt_R0_R1:``0<1``.
Replace ``1`` with ``(Rsqr 1)``; Auto with real.
Unfold Rsqr; Auto with real.
Save.
Hints Resolve Rlt_R0_R1 : real.

(** Order and inverse *)
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

Lemma Rlt_Rinv_R1: (x, y:R) ``1 <= x`` -> ``x<y`` ->``/y< /x``.
Intros x y H' H'0.
Cut (Rlt R0 x); [Intros Lt0 | Apply Rlt_le_trans with r2 := R1]; 
  Auto with real.
Apply Rlt_monotony_contra with z := x; Auto with real.
Rewrite (Rmult_sym x (Rinv x)); Rewrite Rinv_l; Auto with real.
Apply Rlt_monotony_contra with z := y; Auto with real.
Apply Rlt_trans with r2:=x;Auto.
Cut ``y*(x*/y)==x``.
Intro H1;Rewrite H1;Rewrite (Rmult_1r y);Auto.
Rewrite (Rmult_sym x); Rewrite <- Rmult_assoc; Rewrite (Rmult_sym y (Rinv y));
 Rewrite Rinv_l; Auto with real.
Apply imp_not_Req; Right.
Red; Apply Rlt_trans with r2 := x; Auto with real.
Save.
Hints Resolve Rlt_Rinv_R1 :real.

(*********************************************************)        
(**      Greater                                         *)
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
(**       Injection from [N] to [R]                       *)
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
Lemma lt_INR_0:(n:nat)(lt O n)->``0 < (INR n)``.
Induction 1; Intros; Auto with real.
Rewrite S_INR; Auto with real.
Save.
Hints Resolve lt_INR_0: real.

Lemma lt_INR:(n,m:nat)(lt n m)->``(INR n) < (INR m)``.
Induction 1; Intros; Auto with real.
Rewrite S_INR; Auto with real.
Rewrite S_INR; Apply Rlt_trans with (INR m0); Auto with real.
Save.
Hints Resolve lt_INR: real.

Lemma INR_lt_1:(n:nat)(lt (S O) n)->``1 < (INR n)``.
Intros;Replace ``1`` with (INR (S O));Auto with real.
Save.
Hints Resolve INR_lt_1: real.

(**********)
Lemma INR_pos : (p:positive)``0<(INR (convert p))``.
Intro; Apply lt_INR_0.
Simpl; Auto with real.
Apply compare_convert_O.
Save.
Hints Resolve INR_pos : real.

(**********)
Lemma pos_INR:(n:nat)``0 <= (INR n)``.
Intro n; Case n.
Simpl; Auto with real.
Auto with arith real.
Save.
Hints Resolve pos_INR: real.

Lemma INR_lt:(n,m:nat)``(INR n) < (INR m)``->(lt n m).
Double Induction 1 2;Intros.
Simpl;ElimType False;Apply (Rlt_antirefl R0);Auto.
Auto with arith.
Generalize (pos_INR (S n0));Intro;Cut (INR O)==R0;
  [Intro H2;Rewrite H2 in H0;Idtac|Simpl;Trivial]. 
Generalize (Rle_lt_trans ``0`` (INR (S n0)) ``0`` H1 H0);Intro;
  ElimType False;Apply (Rlt_antirefl R0);Auto.
Do 2 Rewrite S_INR in H1;Cut ``(INR n1) < (INR n0)``.
Intro H2;Generalize (H0 n0 H2);Intro;Auto with arith.
Apply (Rlt_anti_compatibility ``1`` (INR n1) (INR n0)).
Rewrite Rplus_sym;Rewrite (Rplus_sym ``1`` (INR n0));Trivial.
Save.
Hints Resolve INR_lt: real.

(*********)
Lemma le_INR:(n,m:nat)(le n m)->``(INR n)<=(INR m)``.
Induction 1; Intros; Auto with real.
Rewrite S_INR.
Apply Rle_trans with (INR m0); Auto with real.
Save.
Hints Resolve le_INR: real.

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

Lemma not_nm_INR:(n,m:nat)~n=m->``(INR n)<>(INR m)``.
Intros n m H; Case (le_or_lt n m); Intros H1.
Case (le_lt_or_eq ? ? H1); Intros H2.
Apply imp_not_Req; Auto with real.
ElimType False;Auto.
Apply sym_not_eqT; Apply imp_not_Req; Auto with real.
Save.
Hints Resolve not_nm_INR : real.

Lemma INR_eq: (n,m:nat)(INR n)==(INR m)->n=m.
Intros;Case (le_or_lt n m); Intros H1.
Case (le_lt_or_eq ? ? H1); Intros H2;Auto.
Cut ~n=m.
Intro H3;Generalize (not_nm_INR n m H3);Intro H4;
  ElimType False;Auto.
Omega.
Symmetry;Cut ~m=n.
Intro H3;Generalize (not_nm_INR m n H3);Intro H4;
  ElimType False;Auto.
Omega.
Save.
Hints Resolve INR_eq : real.

Lemma INR_le: (n, m : nat) (Rle (INR n) (INR m)) ->  (le n m).
Intros;Elim H;Intro.
Generalize (INR_lt n m H0);Intro;Auto with arith.
Generalize (INR_eq n m H0);Intro;Rewrite H1;Auto.
Save.
Hints Resolve INR_le : real.

Lemma not_1_INR:(n:nat)~n=(S O)->``(INR n)<>1``.
Replace ``1``  with (INR (S O)); Auto with real.
Save.
Hints Resolve not_1_INR : real.

(**********************************************************) 
(**      Injection from [Z] to [R]                        *)
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

Lemma plus_IZR_NEG_POS : 
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
NewDestruct z; NewDestruct t; Intros; Auto with real.
Simpl; Intros; Rewrite convert_add; Auto with real.
Apply plus_IZR_NEG_POS.
Rewrite Zplus_sym; Rewrite Rplus_sym; Apply plus_IZR_NEG_POS.
Simpl; Intros; Rewrite convert_add; Rewrite plus_INR; Auto with real.
Save.

(**********)
Lemma mult_IZR:(z,t:Z)(IZR `z*t`)==``(IZR z)*(IZR t)``.
Intros z t; Case z; Case t; Simpl; Auto with real.
Intros t1 z1; Rewrite times_convert; Auto with real.
Intros t1 z1; Rewrite times_convert; Auto with real.
Rewrite Rmult_sym.
Rewrite Ropp_mul1; Auto with real.
Apply eq_Ropp; Rewrite mult_sym; Auto with real.
Intros t1 z1; Rewrite times_convert; Auto with real.
Rewrite Ropp_mul1; Auto with real.
Intros t1 z1; Rewrite times_convert; Auto with real.
Rewrite Ropp_mul2; Auto with real.
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
NewDestruct z; Simpl; Intros; Auto with zarith.
Case (Rlt_not_eq ``0`` (INR (convert p))); Auto with real.
Case (Rlt_not_eq ``-(INR (convert p))`` ``0`` ); Auto with real.
Save.

(**********)
Lemma eq_IZR:(z1,z2:Z)(IZR z1)==(IZR z2)->z1=z2.
Intros;Generalize (eq_Rminus (IZR z1) (IZR z2) H);
 Rewrite (Z_R_minus z1 z2);Intro;Generalize (eq_IZR_R0 `z1-z2` H0);
 Intro;Omega.
Save.

(**********)
Lemma not_O_IZR:(z:Z)`z<>0`->``(IZR z)<>0``.
Intros z H; Red; Intros H0; Case H.
Apply eq_IZR; Auto.
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

Lemma IZR_le: (m,n:Z) `m<= n` -> ``(IZR m)<=(IZR n)``.
Intros;Apply Rgt_not_le;Red;Intro.
Unfold Rgt in H0;Generalize (lt_IZR n m H0); Intro; Omega.
Save.

Lemma IZR_lt: (m,n:Z) `m< n` -> ``(IZR m)<(IZR n)``.
Intros;Cut `m<=n`.
Intro H0;Elim (IZR_le m n H0);Intro;Auto.
Generalize (eq_IZR m n H1);Intro;ElimType False;Omega.
Omega.
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
Lemma single_z_r_R1: 
   (r:R)(z,x:Z)``r<(IZR z)``->``(IZR z)<=r+1``->``r<(IZR x)``->
        ``(IZR x)<=r+1``->z=x.
Intros; Apply one_IZR_r_R1 with r; Auto.
Save.

(**********)
Lemma tech_single_z_r_R1
	:(r:R)(z:Z)``r<(IZR z)``->``(IZR z)<=r+1``
         -> (Ex [s:Z] (~s=z/\``r<(IZR s)``/\``(IZR s)<=r+1``))->False.
Intros r z H1 H2 (s, (H3,(H4,H5))).
Apply H3; Apply single_z_r_R1 with r; Trivial.
Save.

(*****************************************************************)
(** Definitions of new types                                     *)
(*****************************************************************)

Record nonnegreal : Type := mknonnegreal {
nonneg :> R;
cond_nonneg : ``0<=nonneg`` }.

Record posreal : Type := mkposreal {
pos :> R;
cond_pos : ``0<pos`` }.

Record nonposreal : Type := mknonposreal {
nonpos :> R;
cond_nonpos : ``nonpos<=0`` }.

Record negreal : Type := mknegreal {
neg :> R;
cond_neg : ``neg<0`` }.

Record nonzeroreal : Type := mknonzeroreal {
nonzero :> R;
cond_nonzero : ~``nonzero==0`` }.

(**********)
Lemma prod_neq_R0 : (x,y:R) ~``x==0``->~``y==0``->~``x*y==0``.
Intros; Red; Intro; Generalize (without_div_Od x y H1); Intro; Elim H2; Intro; [Rewrite H3 in H; Elim H | Rewrite H3 in H0; Elim H0]; Reflexivity.
Save.

(*********)
Lemma Rmult_le_pos : (x,y:R) ``0<=x`` -> ``0<=y`` -> ``0<=x*y``.
Intros; Rewrite <- (Rmult_Ol x); Rewrite <- (Rmult_sym x); Apply (Rle_monotony x R0 y H H0).
Save.

(**********************************************************)
(** Other rules about < and <=                            *)
(**********************************************************)

Lemma gt0_plus_gt0_is_gt0 : (x,y:R) ``0<x`` -> ``0<y`` -> ``0<x+y``.
Intros; Apply Rlt_trans with x; [Assumption | Pattern 1 x; Rewrite <- (Rplus_Or x); Apply Rlt_compatibility; Assumption].
Save.

Lemma ge0_plus_gt0_is_gt0 : (x,y:R) ``0<=x`` -> ``0<y`` -> ``0<x+y``.
Intros; Apply Rle_lt_trans with x; [Assumption | Pattern 1 x; Rewrite <- (Rplus_Or x); Apply Rlt_compatibility; Assumption].
Save.

Lemma  gt0_plus_ge0_is_gt0 : (x,y:R) ``0<x`` -> ``0<=y`` -> ``0<x+y``.
Intros; Rewrite <- Rplus_sym; Apply ge0_plus_gt0_is_gt0; Assumption.
Save.

Lemma ge0_plus_ge0_is_ge0 : (x,y:R) ``0<=x`` -> ``0<=y`` -> ``0<=x+y``.
Intros; Apply Rle_trans with x; [Assumption | Pattern 1 x; Rewrite <- (Rplus_Or x); Apply Rle_compatibility; Assumption].
Save.

Lemma plus_le_is_le : (x,y,z:R) ``0<=y`` -> ``x+y<=z`` -> ``x<=z``.
Intros; Apply Rle_trans with ``x+y``; [Pattern 1 x; Rewrite <- (Rplus_Or x); Apply Rle_compatibility; Assumption | Assumption].
Save.

Lemma plus_lt_is_lt : (x,y,z:R) ``0<=y`` -> ``x+y<z`` -> ``x<z``.
Intros; Apply Rle_lt_trans with ``x+y``; [Pattern 1 x; Rewrite <- (Rplus_Or x); Apply Rle_compatibility; Assumption | Assumption].
Save.

Lemma Rmult_lt2 : (r1,r2,r3,r4:R) ``0<=r1`` -> ``0<=r3`` -> ``r1<r2`` -> ``r3<r4`` -> ``r1*r3<r2*r4``.
Intros; Apply Rle_lt_trans with ``r2*r3``; [Apply Rle_monotony_r; [Assumption | Left; Assumption] | Apply Rlt_monotony; [Apply Rle_lt_trans with r1; Assumption | Assumption]].
Save.

Lemma le_epsilon : (x,y:R) ((eps : R) ``0<eps``->``x<=y+eps``) -> ``x<=y``.
Intros; Elim (total_order x y); Intro.
Left; Assumption.
Elim H0; Intro.
Right; Assumption.
Clear H0; Generalize (Rgt_minus x y H1); Intro H2; Change ``0<x-y`` in H2.
Cut ``0<2``.
Intro.
Generalize (Rmult_lt_pos ``x-y`` ``/2`` H2 (Rlt_Rinv ``2`` H0)); Intro H3; Generalize (H ``(x-y)*/2`` H3); Replace ``y+(x-y)*/2`` with ``(y+x)*/2``.
Intro H4; Generalize (Rle_monotony ``2`` x ``(y+x)*/2`` (Rlt_le ``0`` ``2`` H0) H4); Rewrite <- (Rmult_sym ``((y+x)*/2)``); Rewrite Rmult_assoc; Rewrite <- Rinv_l_sym.
Rewrite Rmult_1r; Replace ``2*x`` with ``x+x``.
Rewrite (Rplus_sym y); Intro H5; Apply Rle_anti_compatibility with x; Assumption.
Ring. 
Replace ``2`` with (INR (S (S O))); [Apply not_O_INR; Discriminate | Ring].
Field; Replace ``2`` with (INR (S (S O))); [Apply not_O_INR; Discriminate | Ring].
Cut ~(O=(2)); [Intro H0; Generalize (lt_INR_0 (2) (neq_O_lt (2) H0)); Unfold INR; Intro; Assumption | Discriminate].
Save.

(*****************************************************)
(** Complementary results about [INR]                *)
(*****************************************************)

Fixpoint INR2 [n:nat] : R := Cases n of
O => ``0``
| (S n0) => Cases n0 of
O => ``1``
| (S _) => ``1+(INR2 n0)``
end
end.

Theorem INR_eq_INR2 : (n:nat) (INR n)==(INR2 n).
Induction n; [Unfold INR INR2; Reflexivity | Intros; Unfold INR INR2; Fold INR INR2; Rewrite H; Case n0; [Reflexivity | Intros; Ring]].
Save.

Lemma add_auto : (p,q:nat) ``(INR2 (S p))+(INR2 q)==(INR2 p)+(INR2 (S q))``.
Intros; Repeat Rewrite <- INR_eq_INR2; Repeat Rewrite S_INR; Ring.
Save.