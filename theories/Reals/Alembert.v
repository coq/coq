(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)
 
(*i $Id$ i*)


Require Max.
Require Raxioms.
Require DiscrR.
Require Rbase.
Require Rseries.
Require Rtrigo_fun.

Axiom fct_eq : (A:Type)(f1,f2:A->R) ((x:A)(f1 x)==(f2 x)) -> f1 == f2.

Definition SigT := Specif.sigT.

Lemma not_sym : (r1,r2:R) ``r1<>r2`` -> ``r2<>r1``.
Intros; Red; Intro H0; Rewrite H0 in H; Elim H; Reflexivity.
Qed.

Lemma Rgt_2_0 : ``0<2``.
Cut ~(O=(2)); [Intro H0; Generalize (lt_INR_0 (2) (neq_O_lt (2) H0)); Unfold INR; Intro H; Assumption | Discriminate].
Qed.

Lemma Rgt_3_0 : ``0<3``.
Cut ~(O=(3)); [Intro H0; Generalize (lt_INR_0 (3) (neq_O_lt (3) H0)); Rewrite INR_eq_INR2; Unfold INR2; Intro H; Assumption | Discriminate].
Qed.

(*********************)
(* Lemmes techniques *)
(*********************)

Lemma tech1 : (An:nat->R;N:nat) ((n:nat)``(le n N)``->``0<(An n)``) -> ``0 < (sum_f_R0 An N)``.
Intros; Induction N.
Simpl; Apply H.
Apply le_n.
Replace (sum_f_R0 An (S N)) with ``(sum_f_R0 An N)+(An (S N))``.
Apply gt0_plus_gt0_is_gt0.
Apply HrecN; Intros; Apply H.
Apply le_S; Assumption.
Apply H.
Apply le_n.
Reflexivity.
Qed.

(* Relation de Chasles *)
Lemma tech2 : (An:nat->R;m,n:nat) (lt m n) -> (sum_f_R0 An n) == (Rplus (sum_f_R0 An m) (sum_f_R0 [i:nat]``(An (plus (S m) i))`` (minus n (S m)))). 
Intros.
Induction n.
Elim (lt_n_O ? H).
Cut (lt m n)\/m=n.
Intro; Elim H0; Intro.
Replace (sum_f_R0 An (S n)) with ``(sum_f_R0 An n)+(An (S n))``; [Idtac | Reflexivity].
Replace (minus (S n) (S m)) with (S (minus n (S m))).
Replace (sum_f_R0 [i:nat](An (plus (S m) i)) (S (minus n (S m)))) with (Rplus (sum_f_R0 [i:nat](An (plus (S m) i)) (minus n (S m))) (An (plus (S m) (S (minus n (S m)))))); [Idtac | Reflexivity].
Replace (plus (S m) (S (minus n (S m)))) with (S n).
Rewrite (Hrecn H1).
Ring.
Apply INR_eq.
Rewrite S_INR.
Rewrite plus_INR.
Do 2 Rewrite S_INR.
Rewrite minus_INR.
Rewrite S_INR.
Ring.
Apply lt_le_S; Assumption.
Apply INR_eq.
Rewrite S_INR.
Repeat Rewrite minus_INR.
Repeat Rewrite S_INR.
Ring.
Apply le_n_S.
Apply lt_le_weak; Assumption.
Apply lt_le_S; Assumption.
Rewrite H1.
Replace (minus (S n) (S n)) with O.
Simpl.
Replace (plus n O) with n; [Idtac | Ring].
Reflexivity.
Apply minus_n_n.
Inversion H.
Right; Reflexivity.
Left.
Apply lt_le_trans with (S m).
Apply lt_n_Sn.
Assumption.
Qed.

(* Somme d'une suite géométrique *)
Lemma tech3 : (k:R;N:nat) ``k<>1`` -> (sum_f_R0 [i:nat](pow k i) N)==``(1-(pow k (S N)))/(1-k)``.
Intros.
Induction N.
Simpl.
Field.
Replace ``1+ -k`` with ``1-k``; [Idtac | Ring].
Apply Rminus_eq_contra.
Apply not_sym.
Assumption.
Replace (sum_f_R0 ([i:nat](pow k i)) (S N)) with (Rplus (sum_f_R0 [i:nat](pow k i) N) (pow k (S N))); [Idtac | Reflexivity].
Rewrite HrecN.
Replace ``(1-(pow k (S N)))/(1-k)+(pow k (S N))`` with ``((1-(pow k (S N)))+(1-k)*(pow k (S N)))/(1-k)``; [Idtac | Field; Replace ``1+ -k`` with ``1-k``; [Idtac | Ring]; Apply Rminus_eq_contra; Apply not_sym; Assumption].
Replace ``(1-(pow k (S N))+(1-k)*(pow k (S N)))`` with ``1-k*(pow k (S N))``; [Idtac | Ring].
Replace (S (S N)) with (plus (1) (S N)).
Rewrite pow_add.
Simpl.
Rewrite Rmult_1r.
Reflexivity.
Ring.
Qed.

Lemma tech4 : (An:nat->R;k:R;N:nat) ``0<=k`` -> ((i:nat)``(An (S i))<k*(An i)``) -> ``(An N)<=(An O)*(pow k N)``.
Intros.
Induction N.
Simpl.
Right; Ring.
Apply Rle_trans with ``k*(An N)``.
Left; Apply (H0 N).
Replace (S N) with (plus N (1)); [Idtac | Ring].
Rewrite pow_add.
Simpl.
Rewrite Rmult_1r.
Replace ``(An O)*((pow k N)*k)`` with ``k*((An O)*(pow k N))``; [Idtac | Ring].
Apply Rle_monotony.
Assumption.
Apply HrecN.
Qed.

Lemma tech5 : (An:nat->R;N:nat) (sum_f_R0 An (S N))==``(sum_f_R0 An N)+(An (S N))``.
Intros; Reflexivity.
Qed.

Lemma tech6 : (An:nat->R;k:R;N:nat) ``0<=k`` -> ((i:nat)``(An (S i))<k*(An i)``) -> (Rle (sum_f_R0 An N) (Rmult (An O) (sum_f_R0 [i:nat](pow k i) N))).
Intros.
Induction N.
Simpl.
Right; Ring.
Apply Rle_trans with (Rplus (Rmult (An O) (sum_f_R0 [i:nat](pow k i) N)) (An (S N))).
Replace ``(sum_f_R0 An (S N))`` with ``(sum_f_R0 An N)+(An (S N))``.
Do 2 Rewrite <- (Rplus_sym (An (S N))).
Apply Rle_compatibility.
Apply HrecN.
Symmetry; Apply tech5.
Rewrite tech5.
Rewrite Rmult_Rplus_distr.
Apply Rle_compatibility.
Apply tech4; Assumption.
Qed.

Lemma tech7 : (r1,r2:R) ``r1<>0`` -> ``r2<>0`` -> ``r1<>r2`` -> ``/r1<>/r2``.
Intros.
Red.
Intro.
Assert H3 := (Rmult_mult_r r1 ? ? H2).
Rewrite <- Rinv_r_sym in H3; [Idtac | Assumption].
Assert H4 := (Rmult_mult_r r2 ? ? H3).
Rewrite Rmult_1r in H4.
Rewrite <- Rmult_assoc in H4.
Rewrite Rinv_r_simpl_m in H4; [Idtac | Assumption].
Elim H1; Symmetry; Assumption.
Qed.

Lemma tech8 : (n,i:nat) (le n (plus (S n) i)).
Intros.
Induction i.
Replace (plus (S n) O) with (S n).
Apply le_n_Sn.
Ring.
Replace (plus (S n) (S i)) with (S (plus (S n) i)).
Apply le_S; Assumption.
Cut (m:nat)(S m)=(plus m (1)); [Intro | Intro; Ring].
Rewrite H.
Rewrite (H n).
Rewrite (H i).
Ring.
Qed.

Lemma tech9 : (Un:nat->R) (Un_growing Un) -> ((m,n:nat)(le m n)->``(Un m)<=(Un n)``).
Intros.
Unfold Un_growing in H.
Induction n.
Induction m.
Right; Reflexivity.
Elim (le_Sn_O ? H0).
Cut (le m n)\/m=(S n).
Intro; Elim H1; Intro.
Apply Rle_trans with (Un n).
Apply Hrecn; Assumption.
Apply H.
Rewrite H2; Right; Reflexivity.
Inversion H0.
Right; Reflexivity.
Left; Assumption.
Qed.

Lemma tech10 : (Un:nat->R;x:R) (Un_growing Un) -> (is_lub (EUn Un) x) -> (Un_cv Un x).
Intros.
Cut (bound (EUn Un)).
Intro.
Assert H2 := (Un_cv_crit ? H H1).
Elim H2; Intros.
Case (total_order_T x x0); Intro.
Elim s; Intro.
Cut (n:nat)``(Un n)<=x``.
Intro.
Unfold Un_cv in H3.
Cut ``0<x0-x``.
Intro.
Elim (H3 ``x0-x`` H5); Intros.
Cut (ge x1 x1).
Intro.
Assert H8 := (H6 x1 H7).
Unfold R_dist in H8.
Rewrite Rabsolu_left1 in H8.
Rewrite Ropp_distr2 in H8.
Unfold Rminus in H8.
Assert H9 := (Rlt_anti_compatibility ``x0`` ? ? H8).
Assert H10 := (Ropp_Rlt ? ? H9).
Assert H11 := (H4 x1).
Elim (Rlt_antirefl ? (Rlt_le_trans ? ? ? H10 H11)).
Apply Rle_minus.
Apply Rle_trans with x.
Apply H4.
Left; Assumption.
Unfold ge; Apply le_n.
Apply Rgt_minus.
Assumption.
Intro.
Unfold is_lub in H0.
Unfold is_upper_bound in H0.
Elim H0; Intros.
Apply H4.
Unfold EUn.
Exists n.
Reflexivity.
Rewrite b; Assumption.
Cut ((n:nat)``(Un n)<=x0``).
Intro.
Unfold is_lub in H0.
Unfold is_upper_bound in H0.
Elim H0; Intros.
Cut (y:R)(EUn Un y)->``y<=x0``.
Intro.
Assert H8 := (H6 ? H7). 
Elim (Rlt_antirefl ? (Rle_lt_trans ? ? ? H8 r)).
Unfold EUn.
Intros.
Elim H7; Intros.
Rewrite H8; Apply H4.
Intro.
Case (total_order_Rle (Un n) x0); Intro.
Assumption.
Cut (n0:nat)(le n n0) -> ``x0<(Un n0)``. 
Intro.
Unfold Un_cv in H3.
Cut ``0<(Un n)-x0``.
Intro.
Elim (H3 ``(Un n)-x0`` H5); Intros.
Cut (ge (max n x1) x1).
Intro.
Assert H8 := (H6 (max n x1) H7).
Unfold R_dist in H8.
Rewrite Rabsolu_right in H8.
Unfold Rminus in H8; Do 2 Rewrite <- (Rplus_sym ``-x0``) in H8.
Assert H9 := (Rlt_anti_compatibility ? ? ? H8).
Cut ``(Un n)<=(Un (max n x1))``.
Intro.
Elim (Rlt_antirefl ? (Rle_lt_trans ? ? ? H10 H9)).
Apply tech9.
Assumption.
Apply le_max_l.
Apply Rge_trans with ``(Un n)-x0``.
Unfold Rminus; Apply Rle_sym1.
Do 2 Rewrite <- (Rplus_sym ``-x0``).
Apply Rle_compatibility.
Apply tech9.
Assumption.
Apply le_max_l.
Left; Assumption.
Unfold ge; Apply le_max_r.
Apply Rlt_anti_compatibility with x0.
Rewrite Rplus_Or.
Unfold Rminus; Rewrite (Rplus_sym x0).
Rewrite Rplus_assoc; Rewrite Rplus_Ropp_l; Rewrite Rplus_Or.
Apply H4.
Apply le_n.
Intros.
Apply Rlt_le_trans with (Un n).
Case (total_order_Rlt_Rle x0 (Un n)); Intro.
Assumption.
Elim n0; Assumption.
Apply tech9; Assumption.
Unfold bound.
Exists x.
Unfold is_lub in H0.
Elim H0; Intros; Assumption.
Qed.

Lemma tech11 : (An,Bn,Cn:nat->R;N:nat) ((i:nat) (An i)==``(Bn i)-(Cn i)``) -> (sum_f_R0 An N)==``(sum_f_R0 Bn N)-(sum_f_R0 Cn N)``.
Intros.
Induction N.
Simpl.
Apply H.
Replace (sum_f_R0 An (S N)) with ``(sum_f_R0 An N)+(An (S N))``; [Idtac | Reflexivity].
Replace (sum_f_R0 Bn (S N)) with ``(sum_f_R0 Bn N)+(Bn (S N))``; [Idtac | Reflexivity].
Replace (sum_f_R0 Cn (S N)) with ``(sum_f_R0 Cn N)+(Cn (S N))``; [Idtac | Reflexivity].
Rewrite HrecN.
Unfold Rminus.
Repeat Rewrite Rplus_assoc.
Apply Rplus_plus_r.
Rewrite Ropp_distr1.
Rewrite <- Rplus_assoc.
Rewrite <- (Rplus_sym ``-(sum_f_R0 Cn N)``).
Rewrite Rplus_assoc.
Apply Rplus_plus_r.
Unfold Rminus in H.
Apply H.
Qed.

Lemma tech12 : (An:nat->R;x:R;l:R) (Un_cv [N:nat](sum_f_R0 [i:nat]``(An i)*(pow x i)`` N) l) -> (Pser An x l).
Intros.
Unfold Pser.
Unfold infinit_sum.
Unfold Un_cv in H.
Assumption.
Qed. 

Lemma tech13 : (An:nat->R;k:R) ``0<=k<1`` -> (Un_cv [n:nat](Rabsolu ``(An (S n))/(An n)``) k) -> (EXT k0 : R | ``k<k0<1`` /\ (EX N:nat | (n:nat) (le N n)->``(Rabsolu ((An (S n))/(An n)))<k0``)).
Intros.
Exists ``k+(1-k)/2``.
Split.
Split.
Pattern 1 k; Rewrite <- Rplus_Or.
Apply Rlt_compatibility.
Unfold Rdiv; Apply Rmult_lt_pos.
Apply Rlt_anti_compatibility with k; Rewrite Rplus_Or.
Replace ``k+(1-k)`` with R1; [Elim H; Intros; Assumption | Ring].
Apply Rlt_Rinv; Apply Rgt_2_0.
Apply Rlt_monotony_contra with ``2``.
Apply Rgt_2_0.
Unfold Rdiv.
Rewrite Rmult_1r.
Rewrite Rmult_Rplus_distr.
Pattern 1 ``2``; Rewrite Rmult_sym.
Rewrite Rmult_assoc.
Rewrite <- Rinv_l_sym; [Idtac | DiscrR].
Rewrite Rmult_1r.
Replace ``2*k+(1-k)`` with ``1+k``; [Idtac | Ring].
Elim H; Intros.
Apply Rlt_compatibility; Assumption.
Unfold Un_cv in H0.
Cut ``0<(1-k)/2``.
Intro.
Elim (H0 ``(1-k)/2`` H1); Intros.
Exists x.
Intros.
Assert H4 := (H2 n H3).
Unfold R_dist in H4.
Rewrite <- Rabsolu_Rabsolu.
Replace ``(Rabsolu ((An (S n))/(An n)))`` with ``((Rabsolu ((An (S n))/(An n)))-k)+k``; [Idtac | Ring].
Apply Rle_lt_trans with ``(Rabsolu ((Rabsolu ((An (S n))/(An n)))-k))+(Rabsolu k)``.
Apply Rabsolu_triang.
Rewrite (Rabsolu_right k).
Apply Rlt_anti_compatibility with ``-k``.
Rewrite <- (Rplus_sym k).
Repeat Rewrite <- Rplus_assoc.
Rewrite Rplus_Ropp_l.
Repeat Rewrite Rplus_Ol.
Apply H4.
Apply Rle_sym1.
Elim H; Intros; Assumption.
Unfold Rdiv; Apply Rmult_lt_pos.
Apply Rlt_anti_compatibility with k.
Rewrite Rplus_Or.
Elim H; Intros.
Replace ``k+(1-k)`` with R1; [Assumption | Ring].
Apply Rlt_Rinv; Apply Rgt_2_0.
Qed.


(*************************************************)
(* Différentes versions du critère de D'Alembert *)
(*************************************************)

Lemma Alembert_positive :  (An:nat->R) ((n:nat)``0<(An n)``) -> (Un_cv [n:nat](Rabsolu ``(An (S n))/(An n)``) R0) -> (SigT R [l:R](Un_cv [N:nat](sum_f_R0 An N) l)).
Intros An H H0.
Cut (sigTT R [l:R](is_lub (EUn [N:nat](sum_f_R0 An N)) l)) -> (SigT R [l:R](Un_cv [N:nat](sum_f_R0 An N) l)).
Intro.
Apply X.
Apply complet.
2:Exists (sum_f_R0 An O).
2:Unfold EUn.
2:Exists O.
2:Reflexivity.
Unfold Un_cv in H0.
Unfold bound.
Cut ``0</2``; [Intro | Apply Rlt_Rinv; Apply Rgt_2_0].
Elim (H0 ``/2`` H1); Intros.
Exists ``(sum_f_R0 An x)+2*(An (S x))``.
Unfold is_upper_bound.
Intros.
Unfold EUn in H3.
Elim H3; Intros.
Rewrite H4.
Assert H5 := (lt_eq_lt_dec x1 x).
Elim H5; Intros.
Elim a; Intro.
Replace (sum_f_R0 An x) with (Rplus (sum_f_R0 An x1) (sum_f_R0 [i:nat](An (plus (S x1) i)) (minus x (S x1)))).
Pattern 1 (sum_f_R0 An x1); Rewrite <- Rplus_Or.
Rewrite Rplus_assoc.
Apply Rle_compatibility.
Left; Apply gt0_plus_gt0_is_gt0.
Apply tech1.
Intros.
Apply H.
Apply Rmult_lt_pos.
Apply Rgt_2_0.
Apply H.
Symmetry; Apply tech2; Assumption.
Rewrite b.
Pattern 1 (sum_f_R0 An x); Rewrite <- Rplus_Or.
Apply Rle_compatibility.
Left; Apply Rmult_lt_pos.
Apply Rgt_2_0.
Apply H.
Replace (sum_f_R0 An x1) with (Rplus (sum_f_R0 An x) (sum_f_R0 [i:nat](An (plus (S x) i)) (minus x1 (S x)))).
Apply Rle_compatibility.
2:Symmetry.
2:Apply tech2.
2:Assumption.
Cut (Rle (sum_f_R0 [i:nat](An (plus (S x) i)) (minus x1 (S x))) (Rmult (An (S x)) (sum_f_R0 [i:nat](pow ``/2`` i) (minus x1 (S x))))).
Intro.
Apply Rle_trans with (Rmult (An (S x)) (sum_f_R0 [i:nat](pow ``/2`` i) (minus x1 (S x)))).
Assumption.
Rewrite <- (Rmult_sym (An (S x))).
Apply Rle_monotony.
Left; Apply H.
Rewrite tech3.
Replace ``1-/2`` with ``/2``.
Unfold Rdiv.
Rewrite Rinv_Rinv.
Pattern 3 ``2``; Rewrite <- Rmult_1r.
Rewrite <- (Rmult_sym ``2``).
Apply Rle_monotony.
Left; Apply Rgt_2_0.
Left; Apply Rlt_anti_compatibility with ``(pow (/2) (S (minus x1 (S x))))``.
Replace ``(pow (/2) (S (minus x1 (S x))))+(1-
   (pow (/2) (S (minus x1 (S x)))))`` with R1; [Idtac | Ring].
Rewrite <- (Rplus_sym ``1``).
Pattern 1 R1; Rewrite <- Rplus_Or.
Apply Rlt_compatibility.
Apply pow_lt.
Apply Rlt_Rinv; Apply Rgt_2_0.
DiscrR.
Field.
DiscrR.
Pattern 3 R1; Replace R1 with ``/1``.
2:Apply Rinv_R1.
Apply tech7; DiscrR.
Replace (An (S x)) with (An (plus (S x) O)).
Apply (tech6 [i:nat](An (plus (S x) i)) ``/2``).
Left; Apply Rlt_Rinv; Apply Rgt_2_0.
2:Replace (plus (S x) O) with (S x); [Reflexivity | Ring].
Intro.
Cut (n:nat)(ge n x)->``(An (S n))</2*(An n)``.
Intro.
Replace (plus (S x) (S i)) with (S (plus (S x) i)).
Apply H6.
Unfold ge.
Apply tech8.
Cut (m:nat)(S m)=(plus m (1)); [Intro | Intro; Ring].
Rewrite H7.
Rewrite (H7 x).
Rewrite (H7 i).
Ring.
Intros.
Unfold R_dist in H2.
Apply Rlt_monotony_contra with ``/(An n)``.
Apply Rlt_Rinv; Apply H.
Do 2 Rewrite (Rmult_sym ``/(An n)``).
Rewrite Rmult_assoc.
Rewrite <- Rinv_r_sym.
Rewrite Rmult_1r.
Replace ``(An (S n))*/(An n)`` with ``(Rabsolu ((Rabsolu ((An (S n))/(An n)))-0))``.
Apply H2; Assumption.
Unfold Rminus; Rewrite Ropp_O; Rewrite Rplus_Or.
Rewrite Rabsolu_Rabsolu.
Rewrite Rabsolu_right.
Unfold Rdiv; Reflexivity.
Left; Unfold Rdiv; Change ``0<(An (S n))*/(An n)``; Apply Rmult_lt_pos.
Apply H.
Apply Rlt_Rinv; Apply H.
Red; Intro.
Assert H8 := (H n).
Rewrite H7 in H8; Elim (Rlt_antirefl ? H8).
Intro.
Elim X; Intros.
Apply Specif.existT with x.
Apply tech10.
2:Assumption.
Unfold Un_growing.
Intro.
Rewrite tech5.
Pattern 1 (sum_f_R0 An n); Rewrite <- Rplus_Or.
Apply Rle_compatibility.
Left; Apply H.
Qed.

Lemma Alembert_general:(An:nat->R) ((n:nat)``(An n)<>0``) -> (Un_cv [n:nat](Rabsolu ``(An (S n))/(An n)``) R0) -> (SigT R  [l:R](Un_cv [N:nat](sum_f_R0 An N) l)).
Intros.
Pose Vn := [i:nat]``(2*(Rabsolu (An i))+(An i))/2``.
Pose Wn := [i:nat]``(2*(Rabsolu (An i))-(An i))/2``.
Cut (n:nat)``0<(Vn n)``.
Intro.
Cut (n:nat)``0<(Wn n)``.
Intro.
Cut (Un_cv [n:nat](Rabsolu ``(Vn (S n))/(Vn n)``) ``0``).
Intro.
Cut (Un_cv [n:nat](Rabsolu ``(Wn (S n))/(Wn n)``) ``0``).
Intro.
Assert H5 := (Alembert_positive Vn H1 H3).
Assert H6 := (Alembert_positive Wn H2 H4).
Elim H5; Intros.
Elim H6; Intros.
Apply Specif.existT with ``x-x0``.
Unfold Un_cv.
Unfold Un_cv in p.
Unfold Un_cv in p0.
Intros.
Cut ``0<eps/2``.
Intro.
Elim (p ``eps/2`` H8); Clear p; Intros.
Elim (p0 ``eps/2`` H8); Clear p0; Intros.
Pose N := (max x1 x2).
Exists N.
Intros.
Replace (sum_f_R0 An n) with (Rminus (sum_f_R0 Vn n) (sum_f_R0 Wn n)).
Unfold R_dist.
Replace (Rminus (Rminus (sum_f_R0 Vn n) (sum_f_R0 Wn n)) (Rminus x x0)) with (Rplus (Rminus (sum_f_R0 Vn n) x) (Ropp (Rminus (sum_f_R0 Wn n) x0))); [Idtac | Ring].
Apply Rle_lt_trans with (Rplus (Rabsolu (Rminus (sum_f_R0 Vn n) x)) (Rabsolu (Ropp (Rminus (sum_f_R0 Wn n) x0)))).
Apply Rabsolu_triang.
Rewrite Rabsolu_Ropp.
Apply Rlt_le_trans with ``eps/2+eps/2``.
Apply Rplus_lt.
Unfold R_dist in H9.
Apply H9.
Unfold ge; Apply le_trans with N.
Unfold N; Apply le_max_l.
Assumption.
Unfold R_dist in H10.
Apply H10.
Unfold ge; Apply le_trans with N.
Unfold N; Apply le_max_r.
Assumption.
Right; Symmetry; Apply double_var.
Symmetry; Apply tech11.
Intro.
Unfold Vn Wn.
Field.
DiscrR.
Unfold Rdiv; Apply Rmult_lt_pos; [Assumption | Apply Rlt_Rinv; Apply Rgt_2_0].
Cut (n:nat)``/2*(Rabsolu (An n))<=(Wn n)<=(3*/2)*(Rabsolu (An n))``.
Intro.
Cut (n:nat)``/(Wn n)<=2*/(Rabsolu (An n))``.
Intro.
Cut (n:nat)``(Wn (S n))/(Wn n)<=3*(Rabsolu (An (S n))/(An n))``.
Intro.
Unfold Un_cv.
Intros.
Unfold Un_cv in H0.
Cut ``0<eps/3``.
Intro.
Elim (H0 ``eps/3`` H8); Intros.
Exists x.
Intros.
Assert H11 := (H9 n H10).
Unfold R_dist.
Unfold Rminus; Rewrite Ropp_O; Rewrite Rplus_Or; Rewrite Rabsolu_Rabsolu.
Unfold R_dist in H11; Unfold Rminus in H11; Rewrite Ropp_O in H11; Rewrite Rplus_Or in H11; Rewrite Rabsolu_Rabsolu in H11.
Rewrite Rabsolu_right.
Apply Rle_lt_trans with ``3*(Rabsolu ((An (S n))/(An n)))``.
Apply H6.
Apply Rlt_monotony_contra with ``/3``.
Apply Rlt_Rinv; Apply Rgt_3_0.
Rewrite <- Rmult_assoc.
Rewrite <- Rinv_l_sym; [Idtac | DiscrR].
Rewrite Rmult_1l.
Rewrite <- (Rmult_sym eps).
Unfold Rdiv in H11; Exact H11.
Left; Change ``0<(Wn (S n))/(Wn n)``; Unfold Rdiv; Apply Rmult_lt_pos.
Apply H2.
Apply Rlt_Rinv; Apply H2.
Unfold Rdiv; Apply Rmult_lt_pos; [Assumption | Apply Rlt_Rinv; Apply Rgt_3_0].
Intro.
Unfold Rdiv.
Rewrite Rabsolu_mult.
Rewrite <- Rmult_assoc.
Replace ``3`` with ``2*(3*/2)``; [Idtac | Field; DiscrR].
Apply Rle_trans with ``(Wn (S n))*2*/(Rabsolu (An n))``.
Rewrite Rmult_assoc.
Apply Rle_monotony.
Left; Apply H2.
Apply H5.
Rewrite Rabsolu_Rinv.
Replace ``(Wn (S n))*2*/(Rabsolu (An n))`` with ``(2*/(Rabsolu (An n)))*(Wn (S n))``; [Idtac | Ring].
Replace ``2*(3*/2)*(Rabsolu (An (S n)))*/(Rabsolu (An n))`` with ``(2*/(Rabsolu (An n)))*((3*/2)*(Rabsolu (An (S n))))``; [Idtac | Ring].
Apply Rle_monotony.
Left; Apply Rmult_lt_pos.
Apply Rgt_2_0.
Apply Rlt_Rinv; Apply Rabsolu_pos_lt; Apply H.
Elim (H4 (S n)); Intros; Assumption.
Apply H.
Intro.
Apply Rle_monotony_contra with (Wn n).
Apply H2.
Rewrite <- Rinv_r_sym.
Apply Rle_monotony_contra with (Rabsolu (An n)).
Apply Rabsolu_pos_lt; Apply H.
Rewrite Rmult_1r.
Replace ``(Rabsolu (An n))*((Wn n)*(2*/(Rabsolu (An n))))`` with ``2*(Wn n)*((Rabsolu (An n))*/(Rabsolu (An n)))``; [Idtac | Ring].
Rewrite <- Rinv_r_sym.
Rewrite Rmult_1r.
Apply Rle_monotony_contra with ``/2``.
Apply Rlt_Rinv; Apply Rgt_2_0.
Rewrite <- Rmult_assoc.
Rewrite <- Rinv_l_sym.
Rewrite Rmult_1l; Elim (H4 n); Intros; Assumption.
DiscrR.
Apply Rabsolu_no_R0; Apply H.
Red; Intro; Assert H6 := (H2 n); Rewrite H5 in H6; Elim (Rlt_antirefl ? H6).
Intro.
Split.
Unfold Wn.
Unfold Rdiv.
Rewrite <- (Rmult_sym ``/2``).
Apply Rle_monotony.
Left; Apply Rlt_Rinv; Apply Rgt_2_0.
Pattern 1 (Rabsolu (An n)); Rewrite <- Rplus_Or.
Rewrite double.
Unfold Rminus.
Rewrite Rplus_assoc.
Apply Rle_compatibility.
Apply Rle_anti_compatibility with (An n).
Rewrite Rplus_Or.
Rewrite (Rplus_sym (An n)).
Rewrite Rplus_assoc; Rewrite Rplus_Ropp_l; Rewrite Rplus_Or.
Apply Rle_Rabsolu.
Unfold Wn.
Unfold Rdiv.
Repeat Rewrite <- (Rmult_sym ``/2``).
Repeat Rewrite Rmult_assoc.
Apply Rle_monotony.
Left; Apply Rlt_Rinv; Apply Rgt_2_0.
Unfold Rminus.
Rewrite double.
Replace ``3*(Rabsolu (An n))`` with ``(Rabsolu (An n))+(Rabsolu (An n))+(Rabsolu (An n))``; [Idtac | Ring].
Repeat Rewrite Rplus_assoc.
Repeat Apply Rle_compatibility.
Rewrite <- Rabsolu_Ropp.
Apply Rle_Rabsolu.
Cut (n:nat)``/2*(Rabsolu (An n))<=(Vn n)<=(3*/2)*(Rabsolu (An n))``.
Intro.
Cut (n:nat)``/(Vn n)<=2*/(Rabsolu (An n))``.
Intro.
Cut (n:nat)``(Vn (S n))/(Vn n)<=3*(Rabsolu (An (S n))/(An n))``.
Intro.
Unfold Un_cv.
Intros.
Unfold Un_cv in H1.
Cut ``0<eps/3``.
Intro.
Elim (H0 ``eps/3`` H7); Intros.
Exists x.
Intros.
Assert H10 := (H8 n H9).
Unfold R_dist.
Unfold Rminus; Rewrite Ropp_O; Rewrite Rplus_Or; Rewrite Rabsolu_Rabsolu.
Unfold R_dist in H10; Unfold Rminus in H10; Rewrite Ropp_O in H10; Rewrite Rplus_Or in H10; Rewrite Rabsolu_Rabsolu in H10.
Rewrite Rabsolu_right.
Apply Rle_lt_trans with ``3*(Rabsolu ((An (S n))/(An n)))``.
Apply H5.
Apply Rlt_monotony_contra with ``/3``.
Apply Rlt_Rinv; Apply Rgt_3_0.
Rewrite <- Rmult_assoc.
Rewrite <- Rinv_l_sym; [Idtac | DiscrR].
Rewrite Rmult_1l.
Rewrite <- (Rmult_sym eps).
Unfold Rdiv in H10; Exact H10.
Left; Change ``0<(Vn (S n))/(Vn n)``; Unfold Rdiv; Apply Rmult_lt_pos.
Apply H1.
Apply Rlt_Rinv; Apply H1.
Unfold Rdiv; Apply Rmult_lt_pos; [Assumption | Apply Rlt_Rinv; Apply Rgt_3_0].
Intro.
Unfold Rdiv.
Rewrite Rabsolu_mult.
Rewrite <- Rmult_assoc.
Replace ``3`` with ``2*(3*/2)``; [Idtac | Field; DiscrR].
Apply Rle_trans with ``(Vn (S n))*2*/(Rabsolu (An n))``.
Rewrite Rmult_assoc.
Apply Rle_monotony.
Left; Apply H1.
Apply H4.
Rewrite Rabsolu_Rinv.
Replace ``(Vn (S n))*2*/(Rabsolu (An n))`` with ``(2*/(Rabsolu (An n)))*(Vn (S n))``; [Idtac | Ring].
Replace ``2*(3*/2)*(Rabsolu (An (S n)))*/(Rabsolu (An n))`` with ``(2*/(Rabsolu (An n)))*((3*/2)*(Rabsolu (An (S n))))``; [Idtac | Ring].
Apply Rle_monotony.
Left; Apply Rmult_lt_pos.
Apply Rgt_2_0.
Apply Rlt_Rinv; Apply Rabsolu_pos_lt; Apply H.
Elim (H3 (S n)); Intros; Assumption.
Apply H.
Intro.
Apply Rle_monotony_contra with (Vn n).
Apply H1.
Rewrite <- Rinv_r_sym.
Apply Rle_monotony_contra with (Rabsolu (An n)).
Apply Rabsolu_pos_lt; Apply H.
Rewrite Rmult_1r.
Replace ``(Rabsolu (An n))*((Vn n)*(2*/(Rabsolu (An n))))`` with ``2*(Vn n)*((Rabsolu (An n))*/(Rabsolu (An n)))``; [Idtac | Ring].
Rewrite <- Rinv_r_sym.
Rewrite Rmult_1r.
Apply Rle_monotony_contra with ``/2``.
Apply Rlt_Rinv; Apply Rgt_2_0.
Rewrite <- Rmult_assoc.
Rewrite <- Rinv_l_sym.
Rewrite Rmult_1l; Elim (H3 n); Intros; Assumption.
DiscrR.
Apply Rabsolu_no_R0; Apply H.
Red; Intro; Assert H5 := (H1 n); Rewrite H4 in H5; Elim (Rlt_antirefl ? H5).
Intro.
Split.
Unfold Vn.
Unfold Rdiv.
Rewrite <- (Rmult_sym ``/2``).
Apply Rle_monotony.
Left; Apply Rlt_Rinv; Apply Rgt_2_0.
Pattern 1 (Rabsolu (An n)); Rewrite <- Rplus_Or.
Rewrite double.
Rewrite Rplus_assoc.
Apply Rle_compatibility.
Apply Rle_anti_compatibility with ``-(An n)``.
Rewrite Rplus_Or.
Rewrite <- (Rplus_sym (An n)).
Rewrite <- Rplus_assoc; Rewrite Rplus_Ropp_l; Rewrite Rplus_Ol.
Rewrite <- Rabsolu_Ropp.
Apply Rle_Rabsolu.
Unfold Vn.
Unfold Rdiv.
Repeat Rewrite <- (Rmult_sym ``/2``).
Repeat Rewrite Rmult_assoc.
Apply Rle_monotony.
Left; Apply Rlt_Rinv; Apply Rgt_2_0.
Unfold Rminus.
Rewrite double.
Replace ``3*(Rabsolu (An n))`` with ``(Rabsolu (An n))+(Rabsolu (An n))+(Rabsolu (An n))``; [Idtac | Ring].
Repeat Rewrite Rplus_assoc.
Repeat Apply Rle_compatibility.
Apply Rle_Rabsolu.
Intro.
Unfold Wn.
Unfold Rdiv.
Rewrite <- (Rmult_Or ``/2``).
Rewrite <- (Rmult_sym ``/2``).
Apply Rlt_monotony.
Apply Rlt_Rinv; Apply Rgt_2_0.
Apply Rlt_anti_compatibility with (An n).
Rewrite Rplus_Or.
Unfold Rminus.
Rewrite (Rplus_sym (An n)).
Rewrite Rplus_assoc.
Rewrite Rplus_Ropp_l; Rewrite Rplus_Or.
Apply Rle_lt_trans with (Rabsolu (An n)).
Apply Rle_Rabsolu.
Rewrite double.
Pattern 1 (Rabsolu (An n)); Rewrite <- Rplus_Or.
Apply Rlt_compatibility.
Apply Rabsolu_pos_lt; Apply H.
Intro.
Unfold Vn.
Unfold Rdiv.
Rewrite <- (Rmult_Or ``/2``).
Rewrite <- (Rmult_sym ``/2``).
Apply Rlt_monotony.
Apply Rlt_Rinv; Apply Rgt_2_0.
Apply Rlt_anti_compatibility with ``-(An n)``.
Rewrite Rplus_Or.
Unfold Rminus.
Rewrite (Rplus_sym ``-(An n)``).
Rewrite Rplus_assoc.
Rewrite Rplus_Ropp_r; Rewrite Rplus_Or.
Apply Rle_lt_trans with (Rabsolu (An n)).
Rewrite <- Rabsolu_Ropp.
Apply Rle_Rabsolu.
Rewrite double.
Pattern 1 (Rabsolu (An n)); Rewrite <- Rplus_Or.
Apply Rlt_compatibility.
Apply Rabsolu_pos_lt; Apply H.
Qed.

Lemma Alembert_step1 : (An:nat->R;x:R) ``x<>0`` -> ((n:nat)``(An n)<>0``) -> (Un_cv [n:nat](Rabsolu ``(An (S n))/(An n)``) ``0``) -> (SigT R [l:R](Pser An x l)).
Intros.
Pose Bn := [i:nat]``(An i)*(pow x i)``.
Cut (n:nat)``(Bn n)<>0``.
Intro.
Cut (Un_cv [n:nat](Rabsolu ``(Bn (S n))/(Bn n)``) ``0``).
Intro.
Assert H4 := (Alembert_general Bn H2 H3).
Elim H4; Intros.
Apply Specif.existT with x0.
Unfold Bn in p.
Apply tech12. 
Assumption.
Unfold Un_cv.
Intros.
Unfold Un_cv in H1.
Cut ``0<eps/(Rabsolu x)``.
Intro.
Elim (H1 ``eps/(Rabsolu x)`` H4); Intros.
Exists x0.
Intros.
Unfold R_dist.
Unfold Rminus; Rewrite Ropp_O; Rewrite Rplus_Or; Rewrite Rabsolu_Rabsolu.
Unfold Bn.
Replace ``((An (S n))*(pow x (S n)))/((An n)*(pow x n))`` with ``(An (S n))/(An n)*x``.
Rewrite Rabsolu_mult.
Apply Rlt_monotony_contra with ``/(Rabsolu x)``.
Apply Rlt_Rinv; Apply Rabsolu_pos_lt; Assumption.
Rewrite <- (Rmult_sym (Rabsolu x)).
Rewrite <- Rmult_assoc.
Rewrite <- Rinv_l_sym.
Rewrite Rmult_1l.
Rewrite <- (Rmult_sym eps).
Unfold Rdiv in H5.
Replace ``(Rabsolu ((An (S n))/(An n)))`` with ``(R_dist (Rabsolu ((An (S n))*/(An n))) 0)``.
Apply H5; Assumption.
Unfold R_dist.
Unfold Rminus; Rewrite Ropp_O; Rewrite Rplus_Or; Rewrite Rabsolu_Rabsolu.
Unfold Rdiv; Reflexivity.
Apply Rabsolu_no_R0; Assumption.
Replace (S n) with (plus n (1)); [Idtac | Ring].
Rewrite pow_add.
Unfold Rdiv.
Rewrite Rinv_Rmult.
Replace ``(An (plus n (S O)))*((pow x n)*(pow x (S O)))*(/(An n)*/(pow x n))`` with ``(An (plus n (S O)))*(pow x (S O))*/(An n)*((pow x n)*/(pow x n))``; [Idtac | Ring].
Rewrite <- Rinv_r_sym.
Simpl.
Ring.
Apply pow_nonzero; Assumption.
Apply H0.
Apply pow_nonzero; Assumption.
Unfold Rdiv; Apply Rmult_lt_pos.
Assumption.
Apply Rlt_Rinv; Apply Rabsolu_pos_lt; Assumption.
Intro.
Unfold Bn.
Apply prod_neq_R0.
Apply H0.
Apply pow_nonzero; Assumption.
Qed.

Lemma Alembert_step2 : (An:nat->R;x:R) ``x==0`` -> (SigT R [l:R](Pser An x l)).
Intros.
Apply Specif.existT with (An O).
Unfold Pser.
Unfold infinit_sum.
Intros.
Exists O.
Intros.
Replace (sum_f_R0 [n0:nat]``(An n0)*(pow x n0)`` n) with (An O).
Unfold R_dist; Unfold Rminus; Rewrite Rplus_Ropp_r; Rewrite Rabsolu_R0; Assumption.
Induction n.
Simpl.
Ring.
Rewrite tech5.
Rewrite Hrecn.
Rewrite H.
Simpl.
Ring.
Unfold ge; Apply le_O_n.
Qed.

(* Un critère utile de convergence des séries entières *)
Theorem Alembert : (An:nat->R;x:R) ((n:nat)``(An n)<>0``) -> (Un_cv [n:nat](Rabsolu ``(An (S n))/(An n)``) ``0``) -> (SigT R [l:R](Pser An x l)).
Intros.
Case (total_order_T x R0); Intro.
Elim s; Intro.
Cut ``x<>0``.
Intro.
Apply Alembert_step1; Assumption.
Red; Intro; Rewrite H1 in a; Elim (Rlt_antirefl ? a).
Apply Alembert_step2; Assumption.
Cut ``x<>0``.
Intro.
Apply Alembert_step1; Assumption.
Red; Intro; Rewrite H1 in r; Elim (Rlt_antirefl ? r).
Qed.

(* Le "vrai" critère de D'Alembert pour les séries à TG positif *)
Lemma Alembert_strong_positive : (An:nat->R;k:R) ``0<=k<1`` -> ((n:nat)``0<(An n)``) -> (Un_cv [n:nat](Rabsolu ``(An (S n))/(An n)``) k) -> (SigT R [l:R](Un_cv [N:nat](sum_f_R0 An N) l)).
Intros An k Hyp H H0.
Cut (sigTT R [l:R](is_lub (EUn [N:nat](sum_f_R0 An N)) l)) -> (SigT R [l:R](Un_cv [N:nat](sum_f_R0 An N) l)).
Intro.
Apply X.
Apply complet.
2:Exists (sum_f_R0 An O).
2:Unfold EUn.
2:Exists O.
2:Reflexivity.
Assert H1 := (tech13 ? ? Hyp H0).
Elim H1; Intros.
Elim H2; Intros.
Elim H4; Intros.
Unfold bound.
Exists ``(sum_f_R0 An x0)+/(1-x)*(An (S x0))``.
Unfold is_upper_bound.
Intros.
Unfold EUn in H6.
Elim H6; Intros.
Rewrite H7.
Assert H8 := (lt_eq_lt_dec x2 x0).
Elim H8; Intros.
Elim a; Intro.
Replace (sum_f_R0 An x0) with (Rplus (sum_f_R0 An x2) (sum_f_R0 [i:nat](An (plus (S x2) i)) (minus x0 (S x2)))).
Pattern 1 (sum_f_R0 An x2); Rewrite <- Rplus_Or.
Rewrite Rplus_assoc.
Apply Rle_compatibility.
Left; Apply gt0_plus_gt0_is_gt0.
Apply tech1.
Intros.
Apply H.
Apply Rmult_lt_pos.
Apply Rlt_Rinv.
Apply Rlt_anti_compatibility with x.
Rewrite Rplus_Or.
Replace ``x+(1-x)`` with R1; [Elim H3; Intros; Assumption | Ring].
Apply H.
Symmetry; Apply tech2; Assumption.
Rewrite b.
Pattern 1 (sum_f_R0 An x0); Rewrite <- Rplus_Or.
Apply Rle_compatibility.
Left; Apply Rmult_lt_pos.
Apply Rlt_Rinv.
Apply Rlt_anti_compatibility with x.
Rewrite Rplus_Or.
Replace ``x+(1-x)`` with R1; [Elim H3; Intros; Assumption | Ring].
Apply H.
Replace (sum_f_R0 An x2) with (Rplus (sum_f_R0 An x0) (sum_f_R0 [i:nat](An (plus (S x0) i)) (minus x2 (S x0)))).
Apply Rle_compatibility.
2:Symmetry.
2:Apply tech2.
2:Assumption.
Cut (Rle (sum_f_R0 [i:nat](An (plus (S x0) i)) (minus x2 (S x0))) (Rmult (An (S x0)) (sum_f_R0 [i:nat](pow x i) (minus x2 (S x0))))).
Intro.
Apply Rle_trans with (Rmult (An (S x0)) (sum_f_R0 [i:nat](pow x i) (minus x2 (S x0)))).
Assumption.
Rewrite <- (Rmult_sym (An (S x0))).
Apply Rle_monotony.
Left; Apply H.
Rewrite tech3.
Unfold Rdiv.
Apply Rle_monotony_contra with ``1-x``.
Apply Rlt_anti_compatibility with x; Rewrite Rplus_Or.
Replace ``x+(1-x)`` with R1; [Elim H3; Intros; Assumption | Ring].
Do 2 Rewrite (Rmult_sym ``1-x``).
Rewrite Rmult_assoc.
Rewrite <- Rinv_l_sym.
Rewrite Rmult_1r.
Apply Rle_anti_compatibility with ``(pow x (S (minus x2 (S x0))))``.
Replace ``(pow x (S (minus x2 (S x0))))+(1-(pow x (S (minus x2 (S x0)))))`` with R1; [Idtac | Ring].
Rewrite <- (Rplus_sym R1).
Pattern 1 R1; Rewrite <- Rplus_Or.
Apply Rle_compatibility.
Left; Apply pow_lt.
Apply Rle_lt_trans with k.
Elim Hyp; Intros; Assumption.
Elim H3; Intros; Assumption.
Apply Rminus_eq_contra.
Red; Intro.
Elim H3; Intros.
Rewrite H10 in H12; Elim (Rlt_antirefl ? H12).
Red; Intro.
Elim H3; Intros.
Rewrite H10 in H12; Elim (Rlt_antirefl ? H12).
Replace (An (S x0)) with (An (plus (S x0) O)).
Apply (tech6 [i:nat](An (plus (S x0) i)) x).
Left; Apply Rle_lt_trans with k.
Elim Hyp; Intros; Assumption.
Elim H3; Intros; Assumption.
2:Replace (plus (S x0) O) with (S x0); [Reflexivity | Ring].
Intro.
Cut (n:nat)(ge n x0)->``(An (S n))<x*(An n)``.
Intro.
Replace (plus (S x0) (S i)) with (S (plus (S x0) i)).
Apply H9.
Unfold ge.
Apply tech8.
Cut (m:nat)(S m)=(plus m (1)); [Intro | Intro; Ring].
Rewrite H10.
Rewrite (H10 x0).
Rewrite (H10 i).
Ring.
Intros.
Apply Rlt_monotony_contra with ``/(An n)``.
Apply Rlt_Rinv; Apply H.
Do 2 Rewrite (Rmult_sym ``/(An n)``).
Rewrite Rmult_assoc.
Rewrite <- Rinv_r_sym.
Rewrite Rmult_1r.
Replace ``(An (S n))*/(An n)`` with ``(Rabsolu ((An (S n))/(An n)))``.
Apply H5; Assumption.
Rewrite Rabsolu_right.
Unfold Rdiv; Reflexivity.
Left; Unfold Rdiv; Change ``0<(An (S n))*/(An n)``; Apply Rmult_lt_pos.
Apply H.
Apply Rlt_Rinv; Apply H.
Red; Intro.
Assert H11 := (H n).
Rewrite H10 in H11; Elim (Rlt_antirefl ? H11).
Intro.
Elim X; Intros.
Apply Specif.existT with x.
Apply tech10.
2:Assumption.
Unfold Un_growing.
Intro.
Rewrite tech5.
Pattern 1 (sum_f_R0 An n); Rewrite <- Rplus_Or.
Apply Rle_compatibility.
Left; Apply H.
Qed.
