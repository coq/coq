(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
 
(*i $Id$ i*)

Require Rbase.
Require Rfunctions.
Require Rseries.
Require Rcomplete.
Require Max.
V7only [ Import nat_scope. Import Z_scope. Import R_scope. ].
Open Local Scope R_scope.

Lemma tech1 : (An:nat->R;N:nat) ((n:nat)``(le n N)``->``0<(An n)``) -> ``0 < (sum_f_R0 An N)``.
Intros; Induction N.
Simpl; Apply H; Apply le_n.
Simpl; Apply gt0_plus_gt0_is_gt0.
Apply HrecN; Intros; Apply H; Apply le_S; Assumption.
Apply H; Apply le_n.
Qed.

(* Chasles' relation *)
Lemma tech2 : (An:nat->R;m,n:nat) (lt m n) -> (sum_f_R0 An n) == (Rplus (sum_f_R0 An m) (sum_f_R0 [i:nat]``(An (plus (S m) i))`` (minus n (S m)))). 
Intros; Induction n.
Elim (lt_n_O ? H).
Cut (lt m n)\/m=n.
Intro; Elim H0; Intro.
Replace (sum_f_R0 An (S n)) with ``(sum_f_R0 An n)+(An (S n))``; [Idtac | Reflexivity].
Replace (minus (S n) (S m)) with (S (minus n (S m))).
Replace (sum_f_R0 [i:nat](An (plus (S m) i)) (S (minus n (S m)))) with (Rplus (sum_f_R0 [i:nat](An (plus (S m) i)) (minus n (S m))) (An (plus (S m) (S (minus n (S m)))))); [Idtac | Reflexivity].
Replace (plus (S m) (S (minus n (S m)))) with (S n).
Rewrite (Hrecn H1).
Ring.
Apply INR_eq; Rewrite S_INR; Rewrite plus_INR; Do 2 Rewrite S_INR; Rewrite minus_INR.
Rewrite S_INR; Ring.
Apply lt_le_S; Assumption.
Apply INR_eq; Rewrite S_INR; Repeat Rewrite minus_INR.
Repeat Rewrite S_INR; Ring.
Apply le_n_S; Apply lt_le_weak; Assumption.
Apply lt_le_S; Assumption.
Rewrite H1; Rewrite <- minus_n_n; Simpl.
Replace (plus n O) with n; [Reflexivity | Ring].
Inversion H.
Right; Reflexivity.
Left; Apply lt_le_trans with (S m); [Apply lt_n_Sn | Assumption].
Qed.

(* Sum of geometric sequences *)
Lemma tech3 : (k:R;N:nat) ``k<>1`` -> (sum_f_R0 [i:nat](pow k i) N)==``(1-(pow k (S N)))/(1-k)``.
Intros; Cut ``1-k<>0``.
Intro; Induction N.
Simpl; Rewrite Rmult_1r; Unfold Rdiv; Rewrite <- Rinv_r_sym.
Reflexivity.
Apply H0.
Replace (sum_f_R0 ([i:nat](pow k i)) (S N)) with (Rplus (sum_f_R0 [i:nat](pow k i) N) (pow k (S N))); [Idtac | Reflexivity]; Rewrite HrecN; Replace ``(1-(pow k (S N)))/(1-k)+(pow k (S N))`` with ``((1-(pow k (S N)))+(1-k)*(pow k (S N)))/(1-k)``.
Apply r_Rmult_mult with ``1-k``.
Unfold Rdiv; Do 2 Rewrite <- (Rmult_sym ``/(1-k)``); Repeat Rewrite <- Rmult_assoc; Rewrite <- Rinv_r_sym; [ Do 2 Rewrite Rmult_1l; Simpl; Ring | Apply H0].
Apply H0.
Unfold Rdiv; Rewrite Rmult_Rplus_distrl; Rewrite (Rmult_sym ``1-k``); Repeat Rewrite Rmult_assoc; Rewrite <- Rinv_r_sym.
Rewrite Rmult_1r; Reflexivity.
Apply H0.
Apply Rminus_eq_contra; Red; Intro; Elim H; Symmetry; Assumption.
Qed.

Lemma tech4 : (An:nat->R;k:R;N:nat) ``0<=k`` -> ((i:nat)``(An (S i))<k*(An i)``) -> ``(An N)<=(An O)*(pow k N)``.
Intros; Induction N.
Simpl; Right; Ring.
Apply Rle_trans with ``k*(An N)``.
Left; Apply (H0 N).
Replace (S N) with (plus N (1)); [Idtac | Ring].
Rewrite pow_add; Simpl; Rewrite Rmult_1r; Replace ``(An O)*((pow k N)*k)`` with ``k*((An O)*(pow k N))``; [Idtac | Ring]; Apply Rle_monotony.
Assumption.
Apply HrecN.
Qed.

Lemma tech5 : (An:nat->R;N:nat) (sum_f_R0 An (S N))==``(sum_f_R0 An N)+(An (S N))``.
Intros; Reflexivity.
Qed.

Lemma tech6 : (An:nat->R;k:R;N:nat) ``0<=k`` -> ((i:nat)``(An (S i))<k*(An i)``) -> (Rle (sum_f_R0 An N) (Rmult (An O) (sum_f_R0 [i:nat](pow k i) N))).
Intros; Induction N.
Simpl; Right; Ring.
Apply Rle_trans with (Rplus (Rmult (An O) (sum_f_R0 [i:nat](pow k i) N)) (An (S N))).
Rewrite tech5; Do 2 Rewrite <- (Rplus_sym (An (S N))); Apply Rle_compatibility.
Apply HrecN.
Rewrite tech5 ; Rewrite Rmult_Rplus_distr; Apply Rle_compatibility.
Apply tech4; Assumption.
Qed.

Lemma tech7 : (r1,r2:R) ``r1<>0`` -> ``r2<>0`` -> ``r1<>r2`` -> ``/r1<>/r2``.
Intros; Red; Intro.
Assert H3 := (Rmult_mult_r r1 ? ? H2).
Rewrite <- Rinv_r_sym in H3; [Idtac | Assumption].
Assert H4 := (Rmult_mult_r r2 ? ? H3).
Rewrite Rmult_1r in H4; Rewrite <- Rmult_assoc in H4.
Rewrite Rinv_r_simpl_m in H4; [Idtac | Assumption].
Elim H1; Symmetry; Assumption.
Qed.

Lemma tech11 : (An,Bn,Cn:nat->R;N:nat) ((i:nat) (An i)==``(Bn i)-(Cn i)``) -> (sum_f_R0 An N)==``(sum_f_R0 Bn N)-(sum_f_R0 Cn N)``.
Intros; Induction N.
Simpl; Apply H.
Do 3 Rewrite tech5; Rewrite HrecN; Rewrite (H (S N)); Ring.
Qed.

Lemma tech12 : (An:nat->R;x:R;l:R) (Un_cv [N:nat](sum_f_R0 [i:nat]``(An i)*(pow x i)`` N) l) -> (Pser An x l).
Intros; Unfold Pser; Unfold infinit_sum; Unfold Un_cv in H; Assumption.
Qed. 

Lemma scal_sum : (An:nat->R;N:nat;x:R) (Rmult x (sum_f_R0 An N))==(sum_f_R0 [i:nat]``(An i)*x`` N).
Intros; Induction N.
Simpl; Ring.
Do 2 Rewrite tech5.
Rewrite Rmult_Rplus_distr; Rewrite <- HrecN; Ring.
Qed.

Lemma decomp_sum : (An:nat->R;N:nat) (lt O N) -> (sum_f_R0 An N)==(Rplus (An O) (sum_f_R0 [i:nat](An (S i)) (pred N))).
Intros; Induction N.
Elim (lt_n_n ? H).
Cut (lt O N)\/N=O.
Intro; Elim H0; Intro.
Cut (S (pred N))=(pred (S N)).
Intro; Rewrite <- H2.
Do 2 Rewrite tech5.
Replace (S (S (pred N))) with (S N).
Rewrite (HrecN H1); Ring.
Rewrite H2; Simpl; Reflexivity.
Assert H2 := (O_or_S N).
Elim H2; Intros.
Elim a; Intros.
Rewrite <- p.
Simpl; Reflexivity.
Rewrite <- b in H1; Elim (lt_n_n ? H1).
Rewrite H1; Simpl; Reflexivity.
Inversion H.
Right; Reflexivity.
Left; Apply lt_le_trans with (1); [Apply lt_O_Sn | Assumption].
Qed.

Lemma plus_sum : (An,Bn:nat->R;N:nat) (sum_f_R0 [i:nat]``(An i)+(Bn i)`` N)==``(sum_f_R0 An N)+(sum_f_R0 Bn N)``.
Intros; Induction N.
Simpl; Ring.
Do 3 Rewrite tech5; Rewrite HrecN; Ring.
Qed.

Lemma sum_eq : (An,Bn:nat->R;N:nat) ((i:nat)(le i N)->(An i)==(Bn i)) -> (sum_f_R0 An N)==(sum_f_R0 Bn N).
Intros; Induction N.
Simpl; Apply H; Apply le_n.
Do 2 Rewrite tech5; Rewrite HrecN.
Rewrite (H (S N)); [Reflexivity | Apply le_n].
Intros; Apply H; Apply le_trans with N; [Assumption | Apply le_n_Sn].
Qed.

(* Unicity of the limit defined by convergent series *)
Lemma unicity_sum : (An:nat->R;l1,l2:R) (infinit_sum An l1) -> (infinit_sum An l2) -> l1 == l2.
Unfold infinit_sum; Intros.
Case (Req_EM l1 l2); Intro.
Assumption.
Cut ``0<(Rabsolu ((l1-l2)/2))``; [Intro | Apply Rabsolu_pos_lt].
Elim (H ``(Rabsolu ((l1-l2)/2))`` H2); Intros.
Elim (H0 ``(Rabsolu ((l1-l2)/2))`` H2); Intros.
Pose N := (max x0 x); Cut (ge N x0).
Cut (ge N x).
Intros; Assert H7 := (H3 N H5); Assert H8 := (H4 N H6).
Cut ``(Rabsolu (l1-l2)) <= (R_dist (sum_f_R0 An N) l1) + (R_dist (sum_f_R0 An N) l2)``.
Intro; Assert H10 := (Rplus_lt ? ? ? ? H7 H8); Assert H11 := (Rle_lt_trans ? ? ? H9 H10); Unfold Rdiv in H11; Rewrite Rabsolu_mult in H11.
Cut ``(Rabsolu (/2))==/2``.
Intro; Rewrite H12 in H11; Assert H13 := double_var; Unfold Rdiv in H13; Rewrite <- H13 in H11.
Elim (Rlt_antirefl ? H11).
Apply Rabsolu_right; Left; Change ``0</2``; Apply Rlt_Rinv; Cut ~(O=(2)); [Intro H20; Generalize (lt_INR_0 (2) (neq_O_lt (2) H20)); Unfold INR; Intro; Assumption | Discriminate].
Unfold R_dist; Rewrite <- (Rabsolu_Ropp ``(sum_f_R0 An N)-l1``); Rewrite Ropp_distr3.
Replace ``l1-l2`` with ``((l1-(sum_f_R0 An N)))+((sum_f_R0 An N)-l2)``; [Idtac | Ring].
Apply Rabsolu_triang.
Unfold ge; Unfold N; Apply le_max_r.
Unfold ge; Unfold N; Apply le_max_l.
Unfold Rdiv; Apply prod_neq_R0.
Apply Rminus_eq_contra; Assumption.
Apply Rinv_neq_R0; DiscrR.
Qed.

Lemma minus_sum : (An,Bn:nat->R;N:nat) (sum_f_R0 [i:nat]``(An i)-(Bn i)`` N)==``(sum_f_R0 An N)-(sum_f_R0 Bn N)``. 
Intros; Induction N. 
Simpl; Ring. 
Do 3 Rewrite tech5; Rewrite HrecN; Ring. 
Qed. 

Lemma sum_decomposition : (An:nat->R;N:nat) (Rplus (sum_f_R0 [l:nat](An (mult (2) l)) (S N)) (sum_f_R0 [l:nat](An (S (mult (2) l))) N))==(sum_f_R0 An (mult (2) (S N))).
Intros.
Induction N.
Simpl; Ring.
Rewrite tech5.
Rewrite (tech5 [l:nat](An (S (mult (2) l))) N).
Replace (mult (2) (S (S N))) with (S (S (mult (2) (S N)))).
Rewrite (tech5 An (S (mult (2) (S N)))).
Rewrite (tech5 An (mult (2) (S N))).
Rewrite <- HrecN.
Ring.
Apply INR_eq; Do 2 Rewrite S_INR; Do 2 Rewrite mult_INR;Repeat Rewrite S_INR.
Ring.
Qed.

Lemma sum_Rle : (An,Bn:nat->R;N:nat) ((n:nat)(le n N)->``(An n)<=(Bn n)``) -> ``(sum_f_R0 An N)<=(sum_f_R0 Bn N)``.
Intros.
Induction N.
Simpl; Apply H.
Apply le_n.
Do 2 Rewrite tech5.
Apply Rle_trans with ``(sum_f_R0 An N)+(Bn (S N))``.
Apply Rle_compatibility.
Apply H.
Apply le_n.
Do 2 Rewrite <- (Rplus_sym ``(Bn (S N))``).
Apply Rle_compatibility.
Apply HrecN.
Intros; Apply H.
Apply le_trans with N; [Assumption | Apply le_n_Sn].
Qed.

Lemma sum_Rabsolu : (An:nat->R;N:nat) (Rle (Rabsolu (sum_f_R0 An N)) (sum_f_R0 [l:nat](Rabsolu (An l)) N)).
Intros.
Induction N.
Simpl.
Right; Reflexivity.
Do 2 Rewrite tech5.
Apply Rle_trans with ``(Rabsolu (sum_f_R0 An N))+(Rabsolu (An (S N)))``.
Apply Rabsolu_triang.
Do 2 Rewrite <- (Rplus_sym (Rabsolu (An (S N)))).
Apply Rle_compatibility.
Apply HrecN.
Qed.

Lemma sum_cte : (x:R;N:nat) (sum_f_R0 [_:nat]x N) == ``x*(INR (S N))``.
Intros.
Induction N.
Simpl; Ring.
Rewrite tech5.
Rewrite HrecN; Repeat Rewrite S_INR; Ring.
Qed.

(**********)
Lemma sum_growing : (An,Bn:nat->R;N:nat) ((n:nat)``(An n)<=(Bn n)``)->``(sum_f_R0 An N)<=(sum_f_R0 Bn N)``.
Intros.
Induction N.
Simpl; Apply H.
Do 2 Rewrite tech5.
Apply Rle_trans with ``(sum_f_R0 An N)+(Bn (S N))``.
Apply Rle_compatibility; Apply H.
Do 2 Rewrite <- (Rplus_sym (Bn (S N))).
Apply Rle_compatibility; Apply HrecN.
Qed.

(**********)
Lemma Rabsolu_triang_gen : (An:nat->R;N:nat) (Rle (Rabsolu (sum_f_R0 An N)) (sum_f_R0 [i:nat](Rabsolu (An i)) N)). 
Intros.
Induction N.
Simpl.
Right; Reflexivity.
Do 2 Rewrite tech5.
Apply Rle_trans with ``(Rabsolu ((sum_f_R0 An N)))+(Rabsolu (An (S N)))``.
Apply Rabsolu_triang.
Do 2 Rewrite <- (Rplus_sym (Rabsolu (An (S N)))).
Apply Rle_compatibility; Apply HrecN.
Qed.

(**********)
Lemma cond_pos_sum : (An:nat->R;N:nat) ((n:nat)``0<=(An n)``) -> ``0<=(sum_f_R0 An N)``.
Intros.
Induction N.
Simpl; Apply H.
Rewrite tech5.
Apply ge0_plus_ge0_is_ge0.
Apply HrecN.
Apply H.
Qed.

(* Cauchy's criterion for series *)
Definition Cauchy_crit_series [An:nat->R] : Prop := (Cauchy_crit [N:nat](sum_f_R0 An N)).

(* If (|An|) satisfies the Cauchy's criterion for series, then (An) too *)
Lemma cauchy_abs : (An:nat->R) (Cauchy_crit_series [i:nat](Rabsolu (An i))) -> (Cauchy_crit_series An).
Unfold Cauchy_crit_series; Unfold Cauchy_crit.
Intros.
Elim (H eps H0); Intros.
Exists x.
Intros.
Cut (Rle (R_dist (sum_f_R0 An n) (sum_f_R0 An m)) (R_dist (sum_f_R0 [i:nat](Rabsolu (An i)) n) (sum_f_R0 [i:nat](Rabsolu (An i)) m))).
Intro.
Apply Rle_lt_trans with (R_dist (sum_f_R0 [i:nat](Rabsolu (An i)) n) (sum_f_R0 [i:nat](Rabsolu (An i)) m)).
Assumption.
Apply H1; Assumption.
Assert H4 := (lt_eq_lt_dec n m).
Elim H4; Intro.
Elim a; Intro.
Rewrite (tech2 An n m); [Idtac | Assumption].
Rewrite (tech2 [i:nat](Rabsolu (An i)) n m); [Idtac | Assumption].
Unfold R_dist.
Unfold Rminus.
Do 2 Rewrite Ropp_distr1.
Do 2 Rewrite <- Rplus_assoc.
Do 2 Rewrite Rplus_Ropp_r.
Do 2 Rewrite Rplus_Ol.
Do 2 Rewrite Rabsolu_Ropp.
Rewrite (Rabsolu_right (sum_f_R0 [i:nat](Rabsolu (An (plus (S n) i))) (minus m (S n)))).
Pose Bn:=[i:nat](An (plus (S n) i)).
Replace [i:nat](Rabsolu (An (plus (S n) i))) with [i:nat](Rabsolu (Bn i)).
Apply Rabsolu_triang_gen.
Unfold Bn; Reflexivity.
Apply Rle_sym1.
Apply cond_pos_sum.
Intro; Apply Rabsolu_pos.
Rewrite b.
Unfold R_dist.
Unfold Rminus; Do 2 Rewrite Rplus_Ropp_r.
Rewrite Rabsolu_R0; Right; Reflexivity.
Rewrite (tech2 An m n); [Idtac | Assumption].
Rewrite (tech2 [i:nat](Rabsolu (An i)) m n); [Idtac | Assumption].
Unfold R_dist.
Unfold Rminus.
Do 2 Rewrite Rplus_assoc.
Rewrite (Rplus_sym (sum_f_R0 An m)).
Rewrite (Rplus_sym (sum_f_R0 [i:nat](Rabsolu (An i)) m)).
Do 2 Rewrite Rplus_assoc.
Do 2 Rewrite Rplus_Ropp_l.
Do 2 Rewrite Rplus_Or.
Rewrite (Rabsolu_right (sum_f_R0 [i:nat](Rabsolu (An (plus (S m) i))) (minus n (S m)))).
Pose Bn:=[i:nat](An (plus (S m) i)).
Replace [i:nat](Rabsolu (An (plus (S m) i))) with [i:nat](Rabsolu (Bn i)).
Apply Rabsolu_triang_gen.
Unfold Bn; Reflexivity.
Apply Rle_sym1.
Apply cond_pos_sum.
Intro; Apply Rabsolu_pos.
Qed.

(**********)
Lemma cv_cauchy_1 : (An:nat->R) (sigTT R [l:R](Un_cv [N:nat](sum_f_R0 An N) l)) -> (Cauchy_crit_series An).
Intros.
Elim X; Intros.
Unfold Un_cv in p.
Unfold Cauchy_crit_series; Unfold Cauchy_crit.
Intros.
Cut ``0<eps/2``.
Intro.
Elim (p ``eps/2`` H0); Intros.
Exists x0.
Intros.
Apply Rle_lt_trans with ``(R_dist (sum_f_R0 An n) x)+(R_dist (sum_f_R0 An m) x)``.
Unfold R_dist.
Replace ``(sum_f_R0 An n)-(sum_f_R0 An m)`` with ``((sum_f_R0 An n)-x)+ -((sum_f_R0 An m)-x)``; [Idtac | Ring].
Rewrite <- (Rabsolu_Ropp ``(sum_f_R0 An m)-x``).
Apply Rabsolu_triang.
Apply Rlt_le_trans with ``eps/2+eps/2``.
Apply Rplus_lt.
Apply H1; Assumption.
Apply H1; Assumption.
Right; Symmetry; Apply double_var.
Unfold Rdiv; Apply Rmult_lt_pos; [Assumption | Apply Rlt_Rinv; Sup0].
Qed.

Lemma cv_cauchy_2 : (An:nat->R) (Cauchy_crit_series An) -> (sigTT R [l:R](Un_cv [N:nat](sum_f_R0 An N) l)).
Intros.
Apply R_complete.
Unfold Cauchy_crit_series in H.
Exact H.
Qed.

(**********)
Lemma sum_eq_R0 : (An:nat->R;N:nat) ((n:nat)(le n N)->``(An n)==0``) -> (sum_f_R0 An N)==R0.
Intros; Induction N.
Simpl; Apply H; Apply le_n.
Rewrite tech5; Rewrite HrecN; [Rewrite Rplus_Ol; Apply H; Apply le_n | Intros; Apply H; Apply le_trans with N; [Assumption | Apply le_n_Sn]].
Qed.

Definition SP [fn:nat->R->R;N:nat] : R->R := [x:R](sum_f_R0 [k:nat]``(fn k x)`` N).

(**********)
Lemma sum_incr : (An:nat->R;N:nat;l:R) (Un_cv [n:nat](sum_f_R0 An n) l) -> ((n:nat)``0<=(An n)``) -> ``(sum_f_R0 An N)<=l``.
Intros; Case (total_order_T (sum_f_R0 An N) l); Intro.
Elim s; Intro.
Left; Apply a.
Right; Apply b.
Cut (Un_growing [n:nat](sum_f_R0 An n)).
Intro; LetTac l1 := (sum_f_R0 An N) in r.
Unfold Un_cv in H; Cut ``0<l1-l``.
Intro; Elim (H ? H2); Intros.
Pose N0 := (max x N); Cut (ge N0 x).
Intro; Assert H5 := (H3 N0 H4).
Cut ``l1<=(sum_f_R0 An N0)``.
Intro; Unfold R_dist in H5; Rewrite Rabsolu_right in H5.
Cut ``(sum_f_R0 An N0)<l1``.
Intro; Elim (Rlt_antirefl ? (Rlt_le_trans ? ? ? H7 H6)).
Apply Rlt_anti_compatibility with ``-l``.
Do 2 Rewrite (Rplus_sym ``-l``).
Apply H5.
Apply Rle_sym1; Apply Rle_anti_compatibility with l.
Rewrite Rplus_Or; Replace ``l+((sum_f_R0 An N0)-l)`` with (sum_f_R0 An N0); [Idtac | Ring]; Apply Rle_trans with l1.
Left; Apply r.
Apply H6.
Unfold l1; Apply Rle_sym2; Apply (growing_prop [k:nat](sum_f_R0 An k)).
Apply H1.
Unfold ge N0; Apply le_max_r.
Unfold ge N0; Apply le_max_l.
Apply Rlt_anti_compatibility with l; Rewrite Rplus_Or; Replace ``l+(l1-l)`` with l1; [Apply r | Ring].
Unfold Un_growing; Intro; Simpl; Pattern 1 (sum_f_R0 An n); Rewrite <- Rplus_Or; Apply Rle_compatibility; Apply H0.
Qed.

(**********)
Lemma sum_cv_maj : (An:nat->R;fn:nat->R->R;x,l1,l2:R) (Un_cv [n:nat](SP fn n x) l1) -> (Un_cv [n:nat](sum_f_R0 An n) l2) -> ((n:nat)``(Rabsolu (fn n x))<=(An n)``) -> ``(Rabsolu l1)<=l2``.
Intros; Case (total_order_T (Rabsolu l1) l2); Intro.
Elim s; Intro.
Left; Apply a.
Right; Apply b.
Cut (n0:nat)``(Rabsolu (SP fn n0 x))<=(sum_f_R0 An n0)``.
Intro; Cut ``0<((Rabsolu l1)-l2)/2``.
Intro; Unfold Un_cv in H H0.
Elim (H ? H3); Intros Na H4.
Elim (H0 ? H3); Intros Nb H5.
Pose N := (max Na Nb).
Unfold R_dist in H4 H5.
Cut ``(Rabsolu ((sum_f_R0 An N)-l2))<((Rabsolu l1)-l2)/2``.
Intro; Cut ``(Rabsolu ((Rabsolu l1)-(Rabsolu (SP fn N x))))<((Rabsolu l1)-l2)/2``.
Intro; Cut ``(sum_f_R0 An N)<((Rabsolu l1)+l2)/2``.
Intro; Cut ``((Rabsolu l1)+l2)/2<(Rabsolu (SP fn N x))``.
Intro; Cut ``(sum_f_R0 An N)<(Rabsolu (SP fn N x))``.
Intro; Assert H11 := (H2 N).
Elim (Rlt_antirefl ? (Rle_lt_trans ? ? ? H11 H10)).
Apply Rlt_trans with ``((Rabsolu l1)+l2)/2``; Assumption.
Case (case_Rabsolu ``(Rabsolu l1)-(Rabsolu (SP fn N x))``); Intro.
Apply Rlt_trans with (Rabsolu l1).
Apply Rlt_monotony_contra with ``2``.
Sup0.
Unfold Rdiv; Rewrite (Rmult_sym ``2``); Rewrite Rmult_assoc; Rewrite <- Rinv_l_sym.
Rewrite Rmult_1r; Rewrite double; Apply Rlt_compatibility; Apply r.
DiscrR.
Apply (Rminus_lt ? ? r0).
Rewrite (Rabsolu_right ? r0) in H7.
Apply Rlt_anti_compatibility with ``((Rabsolu l1)-l2)/2-(Rabsolu (SP fn N x))``.
Replace ``((Rabsolu l1)-l2)/2-(Rabsolu (SP fn N x))+((Rabsolu l1)+l2)/2`` with ``(Rabsolu l1)-(Rabsolu (SP fn N x))``.
Unfold Rminus; Rewrite Rplus_assoc; Rewrite Rplus_Ropp_l; Rewrite Rplus_Or; Apply H7.
Unfold Rdiv; Rewrite Rmult_Rplus_distrl; Rewrite <- (Rmult_sym ``/2``); Rewrite Rminus_distr; Repeat Rewrite (Rmult_sym ``/2``); Pattern 1 (Rabsolu l1); Rewrite double_var; Unfold Rdiv; Ring.
Case (case_Rabsolu ``(sum_f_R0 An N)-l2``); Intro.
Apply Rlt_trans with l2.
Apply (Rminus_lt ? ? r0).
Apply Rlt_monotony_contra with ``2``.
Sup0.
Rewrite (double l2); Unfold Rdiv; Rewrite (Rmult_sym ``2``); Rewrite Rmult_assoc; Rewrite <- Rinv_l_sym.
Rewrite Rmult_1r; Rewrite (Rplus_sym (Rabsolu l1)); Apply Rlt_compatibility; Apply r.
DiscrR.
Rewrite (Rabsolu_right ? r0) in H6; Apply Rlt_anti_compatibility with ``-l2``.
Replace ``-l2+((Rabsolu l1)+l2)/2`` with ``((Rabsolu l1)-l2)/2``.
Rewrite Rplus_sym; Apply H6.
Unfold Rdiv; Rewrite <- (Rmult_sym ``/2``); Rewrite Rminus_distr; Rewrite Rmult_Rplus_distrl; Pattern 2 l2; Rewrite double_var; Repeat Rewrite (Rmult_sym ``/2``); Rewrite Ropp_distr1; Unfold Rdiv; Ring.
Apply Rle_lt_trans with ``(Rabsolu ((SP fn N x)-l1))``.
Rewrite <- Rabsolu_Ropp; Rewrite Ropp_distr3; Apply Rabsolu_triang_inv2.
Apply H4; Unfold ge N; Apply le_max_l.
Apply H5; Unfold ge N; Apply le_max_r.
Unfold Rdiv; Apply Rmult_lt_pos.
Apply Rlt_anti_compatibility with l2.
Rewrite Rplus_Or; Replace ``l2+((Rabsolu l1)-l2)`` with (Rabsolu l1); [Apply r | Ring].
Apply Rlt_Rinv; Sup0.
Intros; Induction n0.
Unfold SP; Simpl; Apply H1.
Unfold SP; Simpl.
Apply Rle_trans with (Rplus (Rabsolu (sum_f_R0 [k:nat](fn k x) n0)) (Rabsolu (fn (S n0) x))).
Apply Rabsolu_triang.
Apply Rle_trans with ``(sum_f_R0 An n0)+(Rabsolu (fn (S n0) x))``.
Do 2 Rewrite <- (Rplus_sym (Rabsolu (fn (S n0) x))).
Apply Rle_compatibility; Apply Hrecn0.
Apply Rle_compatibility; Apply H1.
Qed.
