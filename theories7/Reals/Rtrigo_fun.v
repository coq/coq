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
V7only [ Import nat_scope. Import Z_scope. Import R_scope. ].
Open Local Scope R_scope.

(*****************************************************************)
(*           To define transcendental functions                  *)
(*                                                               *)
(*****************************************************************)
(*****************************************************************)
(*           For exponential function                            *)
(*                                                               *)
(*****************************************************************)

(*********)
Lemma Alembert_exp:(Un_cv
   [n:nat](Rabsolu (Rmult (Rinv (INR (fact (S n)))) 
         (Rinv (Rinv (INR (fact n)))))) R0).
Unfold Un_cv;Intros;Elim (total_order_Rgt eps R1);Intro.
Split with O;Intros;Rewrite (simpl_fact n);Unfold R_dist;
 Rewrite (minus_R0 (Rabsolu (Rinv (INR (S n)))));
 Rewrite (Rabsolu_Rabsolu (Rinv (INR (S n))));
 Cut (Rgt (Rinv (INR (S n))) R0).
Intro; Rewrite (Rabsolu_pos_eq (Rinv (INR (S n)))).
Cut (Rlt (Rminus (Rinv eps) R1) R0).
Intro;Generalize (Rlt_le_trans (Rminus (Rinv eps) R1) R0 (INR n) H2 
   (pos_INR n));Clear H2;Intro;
 Unfold Rminus in H2;Generalize (Rlt_compatibility R1 
       (Rplus (Rinv eps) (Ropp R1)) (INR n) H2);
 Replace (Rplus R1 (Rplus (Rinv eps) (Ropp R1))) with (Rinv eps);
 [Clear H2;Intro|Ring].
Rewrite (Rplus_sym R1 (INR n)) in H2;Rewrite <-(S_INR n) in H2;
 Generalize (Rmult_gt (Rinv (INR (S n))) eps H1 H);Intro;
 Unfold Rgt in H3;
 Generalize (Rlt_monotony (Rmult (Rinv (INR (S n))) eps) (Rinv eps)
     (INR (S n)) H3 H2);Intro;
 Rewrite (Rmult_assoc (Rinv (INR (S n))) eps (Rinv eps)) in H4;
 Rewrite (Rinv_r eps (imp_not_Req eps R0 
      (or_intror (Rlt eps R0) (Rgt eps R0) H))) 
  in H4;Rewrite (let (H1,H2)=(Rmult_ne (Rinv (INR (S n)))) in H1) 
  in H4;Rewrite (Rmult_sym (Rinv (INR (S n)))) in H4;
 Rewrite (Rmult_assoc eps (Rinv (INR (S n))) (INR (S n))) in H4;
 Rewrite (Rinv_l (INR (S n)) (not_O_INR (S n) 
      (sym_not_equal nat O (S n) (O_S n)))) in H4;
 Rewrite (let (H1,H2)=(Rmult_ne eps) in H1) in H4;Assumption.
Apply Rlt_minus;Unfold Rgt in a;Rewrite <- Rinv_R1;
 Apply (Rinv_lt R1 eps);Auto;
 Rewrite (let (H1,H2)=(Rmult_ne eps) in H2);Unfold Rgt in H;Assumption.
Unfold Rgt in H1;Apply Rlt_le;Assumption.
Unfold Rgt;Apply Rlt_Rinv; Apply lt_INR_0;Apply lt_O_Sn.
(**)
Cut `0<=(up (Rminus (Rinv eps) R1))`.
Intro;Elim (IZN (up (Rminus (Rinv eps) R1)) H0);Intros;
 Split with x;Intros;Rewrite (simpl_fact n);Unfold R_dist;
 Rewrite (minus_R0 (Rabsolu (Rinv (INR (S n)))));
 Rewrite (Rabsolu_Rabsolu (Rinv (INR (S n))));
 Cut (Rgt (Rinv (INR (S n))) R0).
Intro; Rewrite (Rabsolu_pos_eq (Rinv (INR (S n)))).
Cut (Rlt (Rminus (Rinv eps) R1) (INR x)).
Intro;Generalize (Rlt_le_trans (Rminus (Rinv eps) R1) (INR x) (INR n) 
      H4 (le_INR x n ([n,m:nat; H:(ge m n)]H x n H2)));  
 Clear H4;Intro;Unfold Rminus in H4;Generalize (Rlt_compatibility R1 
       (Rplus (Rinv eps) (Ropp R1)) (INR n) H4);
 Replace (Rplus R1 (Rplus (Rinv eps) (Ropp R1))) with (Rinv eps);
 [Clear H4;Intro|Ring].
Rewrite (Rplus_sym R1 (INR n)) in H4;Rewrite <-(S_INR n) in H4;
 Generalize (Rmult_gt (Rinv (INR (S n))) eps H3 H);Intro;
 Unfold Rgt in H5;
 Generalize (Rlt_monotony (Rmult (Rinv (INR (S n))) eps) (Rinv eps)
     (INR (S n)) H5 H4);Intro;
 Rewrite (Rmult_assoc (Rinv (INR (S n))) eps (Rinv eps)) in H6;
 Rewrite (Rinv_r eps (imp_not_Req eps R0 
      (or_intror (Rlt eps R0) (Rgt eps R0) H))) 
  in H6;Rewrite (let (H1,H2)=(Rmult_ne (Rinv (INR (S n)))) in H1) 
  in H6;Rewrite (Rmult_sym (Rinv (INR (S n)))) in H6;
 Rewrite (Rmult_assoc eps (Rinv (INR (S n))) (INR (S n))) in H6;
 Rewrite (Rinv_l (INR (S n)) (not_O_INR (S n) 
      (sym_not_equal nat O (S n) (O_S n)))) in H6;
 Rewrite (let (H1,H2)=(Rmult_ne eps) in H1) in H6;Assumption.
Cut (IZR (up (Rminus (Rinv eps) R1)))==(IZR (INZ x));
 [Intro|Rewrite H1;Trivial].
Elim (archimed (Rminus (Rinv eps) R1));Intros;Clear H6;
 Unfold Rgt in H5;Rewrite H4 in H5;Rewrite INR_IZR_INZ;Assumption.
Unfold Rgt in H1;Apply Rlt_le;Assumption.
Unfold Rgt;Apply Rlt_Rinv; Apply lt_INR_0;Apply lt_O_Sn.
Apply (le_O_IZR (up (Rminus (Rinv eps) R1))); 
 Apply (Rle_trans R0 (Rminus (Rinv eps) R1) 
  (IZR (up (Rminus (Rinv eps) R1)))).
Generalize (Rgt_not_le eps R1 b);Clear b;Unfold Rle;Intro;Elim H0;
 Clear H0;Intro.
Left;Unfold Rgt in H;
 Generalize (Rlt_monotony (Rinv eps) eps R1 (Rlt_Rinv eps H) H0);
 Rewrite (Rinv_l eps (sym_not_eqT R R0 eps
    (imp_not_Req R0 eps (or_introl (Rlt R0 eps) (Rgt R0 eps) H))));
 Rewrite (let (H1,H2)=(Rmult_ne (Rinv eps)) in H1);Intro;
 Fold (Rgt (Rminus (Rinv eps) R1) R0);Apply Rgt_minus;Unfold Rgt;
 Assumption.
Right;Rewrite H0;Rewrite Rinv_R1;Apply sym_eqT;Apply eq_Rminus;Auto.
Elim (archimed (Rminus (Rinv eps) R1));Intros;Clear H1;
 Unfold Rgt in H0;Apply Rlt_le;Assumption.
Qed.






