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
Require SeqSeries.
Require Rtrigo_def.
V7only [ Import nat_scope. Import Z_scope. Import R_scope. ].
Open Local Scope R_scope.

Definition A1 [x:R] : nat->R := [N:nat](sum_f_R0 [k:nat]``(pow (-1) k)/(INR (fact (mult (S (S O)) k)))*(pow x (mult (S (S O)) k))`` N). 
 
Definition B1 [x:R] : nat->R := [N:nat](sum_f_R0 [k:nat]``(pow (-1) k)/(INR (fact (plus (mult (S (S O)) k) (S O))))*(pow x (plus (mult (S (S O)) k) (S O)))`` N). 
 
Definition C1 [x,y:R] : nat -> R := [N:nat](sum_f_R0 [k:nat]``(pow (-1) k)/(INR (fact (mult (S (S O)) k)))*(pow (x+y) (mult (S (S O)) k))`` N). 
 
Definition Reste1 [x,y:R] : nat -> R := [N:nat](sum_f_R0 [k:nat](sum_f_R0 [l:nat]``(pow (-1) (S (plus l k)))/(INR (fact (mult (S (S O)) (S (plus l k)))))*(pow x (mult (S (S O)) (S (plus l k))))*(pow (-1) (minus N l))/(INR (fact (mult (S (S O)) (minus N l))))*(pow y (mult (S (S O)) (minus N l)))`` (pred (minus N k))) (pred N)).

Definition Reste2 [x,y:R] : nat -> R := [N:nat](sum_f_R0 [k:nat](sum_f_R0 [l:nat]``(pow (-1) (S (plus l k)))/(INR (fact (plus (mult (S (S O)) (S (plus l k))) (S O))))*(pow x (plus (mult (S (S O)) (S (plus l k))) (S O)))*(pow (-1) (minus N l))/(INR (fact (plus (mult (S (S O)) (minus N l)) (S O))))*(pow y (plus (mult (S (S O)) (minus N l)) (S O)))`` (pred (minus N k))) (pred N)).

Definition Reste [x,y:R] : nat -> R := [N:nat]``(Reste2 x y N)-(Reste1 x y (S N))``.

(* Here is the main result that will be used to prove that (cos (x+y))=(cos x)(cos y)-(sin x)(sin y) *)
Theorem cos_plus_form : (x,y:R;n:nat) (lt O n) -> ``(A1 x (S n))*(A1 y (S n))-(B1 x n)*(B1 y n)+(Reste x y n)``==(C1 x y (S n)). 
Intros.
Unfold A1 B1.
Rewrite (cauchy_finite [k:nat]
        ``(pow ( -1) k)/(INR (fact (mult (S (S O)) k)))*
        (pow x (mult (S (S O)) k))`` [k:nat]
      ``(pow ( -1) k)/(INR (fact (mult (S (S O)) k)))*
      (pow y (mult (S (S O)) k))`` (S n)).
Rewrite (cauchy_finite [k:nat]
      ``(pow ( -1) k)/(INR (fact (plus (mult (S (S O)) k) (S O))))*
      (pow x (plus (mult (S (S O)) k) (S O)))`` [k:nat]
      ``(pow ( -1) k)/(INR (fact (plus (mult (S (S O)) k) (S O))))*
      (pow y (plus (mult (S (S O)) k) (S O)))`` n H).
Unfold Reste.
Replace (sum_f_R0
   [k:nat]
      (sum_f_R0
        [l:nat]
         ``(pow ( -1) (S (plus l k)))/
         (INR (fact (mult (S (S O)) (S (plus l k)))))*
         (pow x (mult (S (S O)) (S (plus l k))))*
         ((pow ( -1) (minus (S n) l))/
         (INR (fact (mult (S (S O)) (minus (S n) l))))*
         (pow y (mult (S (S O)) (minus (S n) l))))``
        (pred (minus (S n) k))) (pred (S n))) with (Reste1 x y (S n)).
Replace (sum_f_R0
   [k:nat]
      (sum_f_R0
        [l:nat]
         ``(pow ( -1) (S (plus l k)))/
         (INR (fact (plus (mult (S (S O)) (S (plus l k))) (S O))))*
         (pow x (plus (mult (S (S O)) (S (plus l k))) (S O)))*
         ((pow ( -1) (minus n l))/
         (INR (fact (plus (mult (S (S O)) (minus n l)) (S O))))*
         (pow y (plus (mult (S (S O)) (minus n l)) (S O))))``
        (pred (minus n k))) (pred n)) with (Reste2 x y n).
Ring.
Replace (sum_f_R0
   [k:nat]
      (sum_f_R0
        [p:nat]
         ``(pow ( -1) p)/(INR (fact (mult (S (S O)) p)))*
         (pow x (mult (S (S O)) p))*((pow ( -1) (minus k p))/
         (INR (fact (mult (S (S O)) (minus k p))))*
         (pow y (mult (S (S O)) (minus k p))))`` k) (S n)) with (sum_f_R0 [k:nat](Rmult ``(pow (-1) k)/(INR (fact (mult (S (S O)) k)))`` (sum_f_R0 [l:nat]``(C (mult (S (S O)) k) (mult (S (S O)) l))*(pow x (mult (S (S O)) l))*(pow y (mult (S (S O)) (minus k l)))`` k)) (S n)).
Pose sin_nnn := [n:nat]Cases n of O => R0 | (S p) => (Rmult ``(pow (-1) (S p))/(INR (fact (mult (S (S O)) (S p))))`` (sum_f_R0 [l:nat]``(C (mult (S (S O)) (S p)) (S (mult (S (S O)) l)))*(pow x (S (mult (S (S O)) l)))*(pow y (S (mult (S (S O)) (minus p l))))`` p)) end.
Replace (Ropp (sum_f_R0
       [k:nat]
          (sum_f_R0
            [p:nat]
             ``(pow ( -1) p)/
             (INR (fact (plus (mult (S (S O)) p) (S O))))*
             (pow x (plus (mult (S (S O)) p) (S O)))*
             ((pow ( -1) (minus k p))/
             (INR (fact (plus (mult (S (S O)) (minus k p)) (S O))))*
             (pow y (plus (mult (S (S O)) (minus k p)) (S O))))`` k)
       n)) with (sum_f_R0 sin_nnn (S n)).
Rewrite <- sum_plus.
Unfold C1.
Apply sum_eq; Intros.
Induction i.
Simpl.
Rewrite Rplus_Ol.
Replace (C O O) with R1.
Unfold Rdiv; Rewrite Rinv_R1.
Ring.
Unfold C.
Rewrite <- minus_n_n.
Simpl.
Unfold Rdiv; Rewrite Rmult_1r; Rewrite Rinv_R1; Ring.
Unfold sin_nnn.
Rewrite <- Rmult_Rplus_distr.
Apply Rmult_mult_r.
Rewrite binomial.
Pose Wn := [i0:nat]``(C (mult (S (S O)) (S i)) i0)*(pow x i0)*
         (pow y (minus (mult (S (S O)) (S i)) i0))``.
Replace (sum_f_R0
   [l:nat]
      ``(C (mult (S (S O)) (S i)) (mult (S (S O)) l))*
      (pow x (mult (S (S O)) l))*
      (pow y (mult (S (S O)) (minus (S i) l)))`` (S i)) with (sum_f_R0 [l:nat](Wn (mult (2) l)) (S i)).
Replace (sum_f_R0
     [l:nat]
        ``(C (mult (S (S O)) (S i)) (S (mult (S (S O)) l)))*
        (pow x (S (mult (S (S O)) l)))*
        (pow y (S (mult (S (S O)) (minus i l))))`` i) with (sum_f_R0 [l:nat](Wn (S (mult (2) l))) i).
Rewrite Rplus_sym.
Apply sum_decomposition.
Apply sum_eq; Intros.
Unfold Wn.
Apply Rmult_mult_r.
Replace (minus (mult (2) (S i)) (S (mult (2) i0))) with (S (mult (2) (minus i i0))).
Reflexivity.
Apply INR_eq.
Rewrite S_INR; Rewrite mult_INR.
Repeat Rewrite minus_INR.
Rewrite mult_INR; Repeat Rewrite S_INR.
Rewrite mult_INR; Repeat Rewrite S_INR; Ring.
Replace (mult (2) (S i)) with (S (S (mult (2) i))).
Apply le_n_S.
Apply le_trans with (mult (2) i).
Apply mult_le; Assumption.
Apply le_n_Sn.
Apply INR_eq; Do 2 Rewrite S_INR; Do 2 Rewrite mult_INR; Repeat Rewrite S_INR; Ring.
Assumption.
Apply sum_eq; Intros.
Unfold Wn.
Apply Rmult_mult_r.
Replace (minus (mult (2) (S i)) (mult (2) i0)) with (mult (2) (minus (S i) i0)).
Reflexivity.
Apply INR_eq.
Rewrite mult_INR.
Repeat Rewrite minus_INR.
Rewrite mult_INR; Repeat Rewrite S_INR.
Rewrite mult_INR; Repeat Rewrite S_INR; Ring.
Apply mult_le; Assumption.
Assumption.
Rewrite <- (Ropp_Ropp (sum_f_R0 sin_nnn (S n))).
Apply eq_Ropp.
Replace ``-(sum_f_R0 sin_nnn (S n))`` with ``-1*(sum_f_R0 sin_nnn (S n))``; [Idtac | Ring].
Rewrite scal_sum.
Rewrite decomp_sum.
Replace (sin_nnn O) with R0.
Rewrite Rmult_Ol; Rewrite Rplus_Ol.
Replace (pred (S n)) with n; [Idtac | Reflexivity].
Apply sum_eq; Intros.
Rewrite Rmult_sym.
Unfold sin_nnn.
Rewrite scal_sum.
Rewrite scal_sum.
Apply sum_eq; Intros.
Unfold Rdiv.
Repeat Rewrite Rmult_assoc.
Rewrite (Rmult_sym ``/(INR (fact (mult (S (S O)) (S i))))``).
Repeat Rewrite <- Rmult_assoc.
Rewrite <- (Rmult_sym ``/(INR (fact (mult (S (S O)) (S i))))``).
Repeat Rewrite <- Rmult_assoc.
Replace ``/(INR (fact (mult (S (S O)) (S i))))*
   (C (mult (S (S O)) (S i)) (S (mult (S (S O)) i0)))`` with ``/(INR (fact (plus (mult (S (S O)) i0) (S O))))*/(INR (fact (plus (mult (S (S O)) (minus i i0)) (S O))))``.
Replace (S (mult (2) i0)) with (plus (mult (2) i0) (1)); [Idtac | Ring].
Replace (S (mult (2) (minus i i0))) with (plus (mult (2) (minus i i0)) (1)); [Idtac | Ring].
Replace ``(pow (-1) (S i))`` with ``-1*(pow (-1) i0)*(pow (-1) (minus i i0))``.
Ring.
Simpl.
Pattern 2 i; Replace i with (plus i0 (minus i i0)).
Rewrite pow_add.
Ring.
Symmetry; Apply le_plus_minus; Assumption.
Unfold C.
Unfold Rdiv; Repeat Rewrite <- Rmult_assoc.
Rewrite <- Rinv_l_sym.
Rewrite Rmult_1l.
Rewrite Rinv_Rmult.
Replace (S (mult (S (S O)) i0)) with (plus (mult (2) i0) (1)); [Apply Rmult_mult_r | Ring].
Replace (minus (mult (2) (S i)) (plus (mult (2) i0) (1))) with (plus (mult (2) (minus i i0)) (1)).
Reflexivity.
Apply INR_eq.
Rewrite plus_INR; Rewrite mult_INR; Repeat Rewrite minus_INR.
Rewrite plus_INR; Do 2 Rewrite mult_INR; Repeat Rewrite S_INR; Ring.
Replace (plus (mult (2) i0) (1)) with (S (mult (2) i0)).
Replace (mult (2) (S i)) with (S (S (mult (2) i))).
Apply le_n_S.
Apply le_trans with (mult (2) i).
Apply mult_le; Assumption.
Apply le_n_Sn.
Apply INR_eq; Do 2 Rewrite S_INR; Do 2 Rewrite mult_INR; Repeat Rewrite S_INR; Ring.
Apply INR_eq; Rewrite S_INR; Rewrite plus_INR; Rewrite mult_INR; Repeat Rewrite S_INR; Ring.
Assumption.
Apply INR_fact_neq_0.
Apply INR_fact_neq_0.
Apply INR_fact_neq_0.
Reflexivity.
Apply lt_O_Sn.
Apply sum_eq; Intros.
Rewrite scal_sum.
Apply sum_eq; Intros.
Unfold Rdiv.
Repeat Rewrite <- Rmult_assoc.
Rewrite <- (Rmult_sym ``/(INR (fact (mult (S (S O)) i)))``).
Repeat Rewrite <- Rmult_assoc.
Replace ``/(INR (fact (mult (S (S O)) i)))*
   (C (mult (S (S O)) i) (mult (S (S O)) i0))`` with ``/(INR (fact (mult (S (S O)) i0)))*/(INR (fact (mult (S (S O)) (minus i i0))))``.
Replace ``(pow (-1) i)`` with ``(pow (-1) i0)*(pow (-1) (minus i i0))``.
Ring.
Pattern 2 i; Replace i with (plus i0 (minus i i0)).
Rewrite pow_add.
Ring.
Symmetry; Apply le_plus_minus; Assumption.
Unfold C.
Unfold Rdiv; Repeat Rewrite <- Rmult_assoc.
Rewrite <- Rinv_l_sym.
Rewrite Rmult_1l.
Rewrite Rinv_Rmult.
Replace (minus (mult (2) i) (mult (2) i0)) with (mult (2) (minus i i0)).
Reflexivity.
Apply INR_eq.
Rewrite mult_INR; Repeat Rewrite minus_INR.
Do 2 Rewrite mult_INR; Repeat Rewrite S_INR; Ring.
Apply mult_le; Assumption.
Assumption.
Apply INR_fact_neq_0.
Apply INR_fact_neq_0.
Apply INR_fact_neq_0.
Unfold Reste2; Apply sum_eq; Intros.
Apply sum_eq; Intros.
Unfold Rdiv; Ring. 
Unfold Reste1; Apply sum_eq; Intros.
Apply sum_eq; Intros.
Unfold Rdiv; Ring.
Apply lt_O_Sn.
Qed.

Lemma pow_sqr : (x:R;i:nat) (pow x (mult (2) i))==(pow ``x*x`` i). 
Intros. 
Assert H := (pow_Rsqr x i).
Unfold Rsqr in H; Exact H.
Qed. 
 
Lemma A1_cvg : (x:R) (Un_cv (A1 x) (cos x)). 
Intro. 
Assert H := (exist_cos ``x*x``). 
Elim H; Intros. 
Assert p_i := p. 
Unfold cos_in in p. 
Unfold cos_n infinit_sum in p. 
Unfold R_dist in p. 
Cut ``(cos x)==x0``. 
Intro. 
Rewrite H0. 
Unfold Un_cv; Unfold R_dist; Intros. 
Elim (p eps H1); Intros. 
Exists x1; Intros. 
Unfold A1. 
Replace (sum_f_R0 ([k:nat]``(pow ( -1) k)/(INR (fact (mult (S (S O)) k)))*(pow x (mult (S (S O)) k))``) n) with (sum_f_R0 ([i:nat]``(pow ( -1) i)/(INR (fact (mult (S (S O)) i)))*(pow (x*x) i)``) n). 
Apply H2; Assumption. 
Apply sum_eq. 
Intros. 
Replace ``(pow (x*x) i)`` with ``(pow x (mult (S (S O)) i))``. 
Reflexivity. 
Apply pow_sqr. 
Unfold cos. 
Case (exist_cos (Rsqr x)). 
Unfold Rsqr; Intros. 
Unfold cos_in in p_i. 
Unfold cos_in in c. 
Apply unicity_sum with [i:nat]``(cos_n i)*(pow (x*x) i)``; Assumption. 
Qed. 
 
Lemma C1_cvg : (x,y:R) (Un_cv (C1 x y) (cos (Rplus x y))). 
Intros. 
Assert H := (exist_cos ``(x+y)*(x+y)``). 
Elim H; Intros. 
Assert p_i := p. 
Unfold cos_in in p. 
Unfold cos_n infinit_sum in p. 
Unfold R_dist in p. 
Cut ``(cos (x+y))==x0``. 
Intro. 
Rewrite H0. 
Unfold Un_cv; Unfold R_dist; Intros. 
Elim (p eps H1); Intros. 
Exists x1; Intros. 
Unfold C1. 
Replace (sum_f_R0 ([k:nat]``(pow ( -1) k)/(INR (fact (mult (S (S O)) k)))*(pow (x+y) (mult (S (S O)) k))``) n) with (sum_f_R0 ([i:nat]``(pow ( -1) i)/(INR (fact (mult (S (S O)) i)))*(pow ((x+y)*(x+y)) i)``) n). 
Apply H2; Assumption. 
Apply sum_eq. 
Intros. 
Replace ``(pow ((x+y)*(x+y)) i)`` with ``(pow (x+y) (mult (S (S O)) i))``. 
Reflexivity. 
Apply pow_sqr. 
Unfold cos. 
Case (exist_cos (Rsqr ``x+y``)). 
Unfold Rsqr; Intros. 
Unfold cos_in in p_i. 
Unfold cos_in in c. 
Apply unicity_sum with [i:nat]``(cos_n i)*(pow ((x+y)*(x+y)) i)``; Assumption. 
Qed. 
 
Lemma B1_cvg : (x:R) (Un_cv (B1 x) (sin x)). 
Intro. 
Case (Req_EM x R0); Intro. 
Rewrite H. 
Rewrite sin_0. 
Unfold B1. 
Unfold Un_cv; Unfold R_dist; Intros; Exists O; Intros. 
Replace (sum_f_R0 ([k:nat]``(pow ( -1) k)/(INR (fact (plus (mult (S (S O)) k) (S O))))*(pow 0 (plus (mult (S (S O)) k) (S O)))``) n) with R0. 
Unfold Rminus; Rewrite Rplus_Ropp_r; Rewrite Rabsolu_R0; Assumption. 
Induction n. 
Simpl; Ring. 
Rewrite tech5; Rewrite <- Hrecn. 
Simpl; Ring. 
Unfold ge; Apply le_O_n. 
Assert H0 := (exist_sin ``x*x``). 
Elim H0; Intros. 
Assert p_i := p. 
Unfold sin_in in p. 
Unfold sin_n infinit_sum in p. 
Unfold R_dist in p. 
Cut ``(sin x)==x*x0``. 
Intro. 
Rewrite H1. 
Unfold Un_cv; Unfold R_dist; Intros. 
Cut ``0<eps/(Rabsolu x)``; [Intro | Unfold Rdiv; Apply Rmult_lt_pos; [Assumption | Apply Rlt_Rinv; Apply Rabsolu_pos_lt; Assumption]]. 
Elim (p ``eps/(Rabsolu x)`` H3); Intros. 
Exists x1; Intros. 
Unfold B1. 
Replace (sum_f_R0 ([k:nat]``(pow ( -1) k)/(INR (fact (plus (mult (S (S O)) k) (S O))))*(pow x (plus (mult (S (S O)) k) (S O)))``) n) with (Rmult x (sum_f_R0 ([i:nat]``(pow ( -1) i)/(INR (fact (plus (mult (S (S O)) i) (S O))))*(pow (x*x) i)``) n)). 
Replace (Rminus (Rmult x (sum_f_R0 ([i:nat]``(pow ( -1) i)/(INR (fact (plus (mult (S (S O)) i) (S O))))*(pow (x*x) i)``) n)) (Rmult x x0)) with (Rmult x (Rminus (sum_f_R0 ([i:nat]``(pow ( -1) i)/(INR (fact (plus (mult (S (S O)) i) (S O))))*(pow (x*x) i)``) n) x0)); [Idtac | Ring]. 
Rewrite Rabsolu_mult. 
Apply Rlt_monotony_contra with ``/(Rabsolu x)``. 
Apply Rlt_Rinv; Apply Rabsolu_pos_lt; Assumption. 
Rewrite <- Rmult_assoc. 
Rewrite <- Rinv_l_sym. 
Rewrite Rmult_1l; Rewrite <- (Rmult_sym eps); Unfold Rdiv in H4; Apply H4; Assumption. 
Apply Rabsolu_no_R0; Assumption. 
Rewrite scal_sum. 
Apply sum_eq. 
Intros. 
Rewrite pow_add. 
Rewrite pow_sqr. 
Simpl. 
Ring. 
Unfold sin. 
Case (exist_sin (Rsqr x)). 
Unfold Rsqr; Intros. 
Unfold sin_in in p_i. 
Unfold sin_in in s. 
Assert H1 := (unicity_sum [i:nat]``(sin_n i)*(pow (x*x) i)`` x0 x1 p_i s). 
Rewrite H1; Reflexivity. 
Qed. 
