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
Require Classical.
Require Compare.
V7only [ Import nat_scope. Import Z_scope. Import R_scope. ].
Open Local Scope R_scope.

Implicit Variable Type r:R.

(* classical is needed for [Un_cv_crit] *)
(*********************************************************)
(*           Definition of sequence and properties       *)
(*                                                       *)
(*********************************************************)

Section sequence.

(*********)
Variable Un:nat->R.

(*********)
Fixpoint Rmax_N [N:nat]:R:=
   Cases N of
     O     => (Un O)
    |(S n) => (Rmax (Un (S n)) (Rmax_N n))
   end.

(*********)
Definition EUn:R->Prop:=[r:R](Ex [i:nat] (r==(Un i))).

(*********)
Definition Un_cv:R->Prop:=[l:R]
  (eps:R)(Rgt eps R0)->(Ex[N:nat](n:nat)(ge n N)->
             (Rlt (R_dist (Un n) l) eps)).

(*********)
Definition Cauchy_crit:Prop:=(eps:R)(Rgt eps R0)->
       (Ex[N:nat] (n,m:nat)(ge n N)->(ge m N)->
                  (Rlt (R_dist (Un n) (Un m)) eps)).

(*********)
Definition Un_growing:Prop:=(n:nat)(Rle (Un n) (Un (S n))).

(*********)
Lemma EUn_noempty:(ExT [r:R] (EUn r)).
Unfold EUn;Split with (Un O);Split with O;Trivial.
Qed.

(*********)
Lemma Un_in_EUn:(n:nat)(EUn (Un n)).
Intro;Unfold EUn;Split with n;Trivial.
Qed.

(*********)
Lemma Un_bound_imp:(x:R)((n:nat)(Rle (Un n) x))->(is_upper_bound EUn x).
Intros;Unfold is_upper_bound;Intros;Unfold EUn in H0;Elim H0;Clear H0;
 Intros;Generalize (H x1);Intro;Rewrite <- H0 in H1;Trivial.
Qed.

(*********)
Lemma growing_prop:(n,m:nat)Un_growing->(ge n m)->(Rge (Un n) (Un m)).
Double Induction n m;Intros.
Unfold Rge;Right;Trivial.
ElimType False;Unfold ge in H1;Generalize (le_Sn_O n0);Intro;Auto.
Cut (ge n0 (0)).
Generalize H0;Intros;Unfold Un_growing in H0;
 Apply (Rge_trans (Un (S n0)) (Un n0) (Un (0)) 
                  (Rle_sym1 (Un n0) (Un (S n0)) (H0 n0)) (H O H2 H3)).
Elim n0;Auto.
Elim (lt_eq_lt_dec n1 n0);Intro y.
Elim y;Clear y;Intro y.
Unfold ge in H2;Generalize (le_not_lt n0 n1 (le_S_n n0 n1 H2));Intro;
 ElimType False;Auto.
Rewrite y;Unfold Rge;Right;Trivial.
Unfold ge in H0;Generalize (H0 (S n0) H1 (lt_le_S n0 n1 y));Intro;
 Unfold Un_growing in H1;
 Apply (Rge_trans (Un (S n1)) (Un n1) (Un (S n0)) 
                  (Rle_sym1 (Un n1) (Un (S n1)) (H1 n1)) H3).
Qed.


(* classical is needed: [not_all_not_ex] *)
(*********)
Lemma Un_cv_crit:Un_growing->(bound EUn)->(ExT [l:R] (Un_cv l)).
Unfold Un_growing Un_cv;Intros;
 Generalize (complet_weak EUn H0 EUn_noempty);Intro;
 Elim H1;Clear H1;Intros;Split with x;Intros;
 Unfold is_lub in H1;Unfold bound in H0;Unfold is_upper_bound in H0 H1;
 Elim H0;Clear H0;Intros;Elim H1;Clear H1;Intros;
 Generalize (H3 x0 H0);Intro;Cut (n:nat)(Rle (Un n) x);Intro.
Cut (Ex [N:nat] (Rlt (Rminus x eps) (Un N))).
Intro;Elim H6;Clear H6;Intros;Split with x1.
Intros;Unfold R_dist;Apply (Rabsolu_def1 (Rminus (Un n) x) eps).
Unfold Rgt in H2;
 Apply (Rle_lt_trans (Rminus (Un n) x) R0 eps 
                     (Rle_minus (Un n) x (H5 n)) H2).
Fold Un_growing in H;Generalize (growing_prop n x1 H H7);Intro;
 Generalize (Rlt_le_trans (Rminus x eps) (Un x1) (Un n) H6
                          (Rle_sym2 (Un x1) (Un n) H8));Intro;
 Generalize (Rlt_compatibility (Ropp x) (Rminus x eps) (Un n) H9);
 Unfold Rminus;Rewrite <-(Rplus_assoc (Ropp x) x (Ropp eps));
 Rewrite (Rplus_sym (Ropp x) (Un n));Fold (Rminus (Un n) x);
 Rewrite Rplus_Ropp_l;Rewrite (let (H1,H2)=(Rplus_ne (Ropp eps)) in H2);
 Trivial.
Cut ~((N:nat)(Rge (Rminus x eps) (Un N))).
Intro;Apply (not_all_not_ex nat ([N:nat](Rlt (Rminus x eps) (Un N))));
 Red;Intro;Red in H6;Elim H6;Clear H6;Intro;
 Apply (Rlt_not_ge (Rminus x eps) (Un N) (H7 N)).
Red;Intro;Cut (N:nat)(Rle (Un N) (Rminus x eps)).
Intro;Generalize (Un_bound_imp (Rminus x eps) H7);Intro;
 Unfold is_upper_bound in H8;Generalize (H3 (Rminus x eps) H8);Intro;
 Generalize (Rle_minus x (Rminus x eps) H9);Unfold Rminus;
 Rewrite Ropp_distr1;Rewrite <- Rplus_assoc;Rewrite Rplus_Ropp_r;
 Rewrite (let (H1,H2)=(Rplus_ne (Ropp (Ropp eps))) in H2);
 Rewrite Ropp_Ropp;Intro;Unfold Rgt in H2;
 Generalize (Rle_not eps R0 H2);Intro;Auto.
Intro;Elim (H6 N);Intro;Unfold Rle.
Left;Unfold Rgt in H7;Assumption.
Right;Auto.
Apply (H1 (Un n) (Un_in_EUn n)).
Qed.

(*********)
Lemma finite_greater:(N:nat)(ExT [M:R] (n:nat)(le n N)->(Rle (Un n) M)).
Intro;Induction N.
Split with (Un O);Intros;Rewrite (le_n_O_eq n H); 
 Apply (eq_Rle (Un (n)) (Un (n)) (refl_eqT R (Un (n)))).
Elim HrecN;Clear HrecN;Intros;Split with (Rmax (Un (S N)) x);Intros;
 Elim (Rmax_Rle (Un (S N)) x (Un n));Intros;Clear H1;Inversion H0.
Rewrite <-H1;Rewrite <-H1 in H2;
 Apply (H2 (or_introl (Rle (Un n) (Un n)) (Rle (Un n) x) 
    (eq_Rle (Un n) (Un n) (refl_eqT R (Un n))))).
Apply (H2 (or_intror (Rle (Un n) (Un (S N))) (Rle (Un n) x) 
    (H n H3))).
Qed.

(*********)
Lemma cauchy_bound:Cauchy_crit->(bound EUn).
Unfold Cauchy_crit bound;Intros;Unfold is_upper_bound;
 Unfold Rgt in H;Elim (H R1 Rlt_R0_R1);Clear H;Intros;
 Generalize (H x);Intro;Generalize (le_dec x);Intro;
 Elim (finite_greater x);Intros;Split with (Rmax x0 (Rplus (Un x) R1));
 Clear H;Intros;Unfold EUn in H;Elim H;Clear H;Intros;Elim (H1 x2);
 Clear H1;Intro y.
Unfold ge in H0;Generalize (H0 x2 (le_n x) y);Clear H0;Intro;
 Rewrite <- H in H0;Unfold R_dist in H0;
 Elim (Rabsolu_def2 (Rminus (Un x) x1) R1 H0);Clear H0;Intros;
 Elim (Rmax_Rle x0 (Rplus (Un x) R1) x1);Intros;Apply H4;Clear H3 H4;
 Right;Clear H H0 y;Apply (Rlt_le x1 (Rplus (Un x) R1));
 Generalize (Rlt_minus (Ropp R1) (Rminus (Un x) x1) H1);Clear H1;
 Intro;Apply (Rminus_lt x1 (Rplus (Un x) R1));
 Cut (Rminus (Ropp R1) (Rminus (Un x) x1))==
  (Rminus x1 (Rplus (Un x) R1));[Intro;Rewrite H0 in H;Assumption|Ring].
Generalize (H2 x2 y);Clear H2 H0;Intro;Rewrite<-H in H0;
 Elim (Rmax_Rle x0 (Rplus (Un x) R1) x1);Intros;Clear H1;Apply H2;
 Left;Assumption.
Qed.

End sequence.

(*****************************************************************)
(*           Definition of Power Series and properties           *)
(*                                                               *)
(*****************************************************************)

Section Isequence.

(*********)
Variable An:nat->R.

(*********)
Definition Pser:R->R->Prop:=[x,l:R]
   (infinit_sum [n:nat](Rmult (An n) (pow x n)) l).

End Isequence.

Lemma GP_infinite:
 (x:R) (Rlt (Rabsolu x) R1) 
       -> (Pser ([n:nat] R1) x (Rinv(Rminus R1 x))).
Intros;Unfold Pser; Unfold infinit_sum;Intros;Elim (Req_EM x R0).
Intros;Exists O; Intros;Rewrite H1;Rewrite minus_R0;Rewrite Rinv_R1;
  Cut (sum_f_R0 [n0:nat](Rmult R1 (pow R0 n0)) n)==R1.
Intros; Rewrite H3;Rewrite R_dist_eq;Auto.
Elim n; Simpl.
Ring.
Intros;Rewrite H3;Ring.
Intro;Cut (Rlt R0
      (Rmult eps (Rmult (Rabsolu (Rminus R1 x)) 
                        (Rabsolu (Rinv x))))).
Intro;Elim (pow_lt_1_zero x H
                    (Rmult eps (Rmult (Rabsolu (Rminus R1 x))
                                 (Rabsolu (Rinv x))))
                    H2);Intro N; Intros;Exists N; Intros;
  Cut (sum_f_R0 [n0:nat](Rmult R1 (pow x n0)) n)==
    (sum_f_R0 [n0:nat](pow x n0) n).
Intros; Rewrite H5;Apply (Rlt_monotony_rev
         (Rabsolu (Rminus R1 x))
         (R_dist (sum_f_R0 [n0:nat](pow x n0) n) 
                 (Rinv (Rminus R1 x))) 
         eps).
Apply Rabsolu_pos_lt.
Apply Rminus_eq_contra.
Apply imp_not_Req.
Right; Unfold Rgt.
Apply (Rle_lt_trans x (Rabsolu x) R1).
Apply Rle_Rabsolu.
Assumption.
Unfold R_dist; Rewrite <- Rabsolu_mult.
Rewrite Rminus_distr.
Cut (Rmult (Rminus R1 x) (sum_f_R0 [n0:nat](pow x n0) n))==
    (Ropp (Rmult(sum_f_R0 [n0:nat](pow x n0) n) 
          (Rminus x R1))).
Intro; Rewrite H6.
Rewrite GP_finite.
Rewrite Rinv_r.
Cut (Rminus (Ropp (Rminus (pow x (plus n (1))) R1)) R1)==
    (Ropp (pow x (plus n (1)))).
Intro; Rewrite H7.
Rewrite Rabsolu_Ropp;Cut (plus n (S O))=(S n);Auto.
Intro H8;Rewrite H8;Simpl;Rewrite Rabsolu_mult;
  Apply (Rlt_le_trans (Rmult (Rabsolu x) (Rabsolu (pow x n)))
                    (Rmult (Rabsolu x)
                           (Rmult eps
                              (Rmult (Rabsolu (Rminus R1 x)) 
                                      (Rabsolu (Rinv x)))))
                 (Rmult (Rabsolu (Rminus R1 x)) eps)).
Apply Rlt_monotony.
Apply Rabsolu_pos_lt.
Assumption.
Auto.
Cut (Rmult (Rabsolu x)
           (Rmult eps (Rmult (Rabsolu (Rminus R1 x)) 
                             (Rabsolu (Rinv x)))))==
    (Rmult (Rmult (Rabsolu x) (Rabsolu (Rinv x))) 
           (Rmult eps (Rabsolu (Rminus R1 x)))).
Clear H8;Intros; Rewrite H8;Rewrite <- Rabsolu_mult;Rewrite Rinv_r.  
Rewrite Rabsolu_R1;Cut (Rmult R1 (Rmult eps (Rabsolu (Rminus R1 x))))==
    (Rmult (Rabsolu (Rminus R1 x)) eps).
Intros; Rewrite H9;Unfold Rle; Right; Reflexivity.
Ring.
Assumption.
Ring.
Ring.
Ring.
Apply Rminus_eq_contra.
Apply imp_not_Req.
Right; Unfold Rgt.
Apply (Rle_lt_trans x (Rabsolu x) R1).
Apply Rle_Rabsolu.
Assumption.
Ring; Ring.
Elim n; Simpl.
Ring.
Intros; Rewrite H5.
Ring.
Apply Rmult_lt_pos.
Auto.
Apply Rmult_lt_pos.
Apply Rabsolu_pos_lt.
Apply Rminus_eq_contra.
Apply imp_not_Req.
Right; Unfold Rgt.
Apply (Rle_lt_trans x (Rabsolu x) R1).
Apply Rle_Rabsolu.
Assumption.
Apply Rabsolu_pos_lt.
Apply Rinv_neq_R0.
Assumption.
Qed.
