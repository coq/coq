(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(*********************************************************)
(*      Definition of the derivative,continuity          *)
(*                                                       *)
(*********************************************************)
Require Export Rfunctions.
Require Classical_Pred_Type.
Require Omega.

(*********)
Definition D_x:(R->Prop)->R->R->Prop:=[D:R->Prop][y:R][x:R]
       (D x)/\(~y==x).

(*********)
Definition continue_in:(R->R)->(R->Prop)->R->Prop:=
       [f:R->R; D:R->Prop; x0:R](limit1_in f (D_x D x0) (f x0) x0).

(*********)
Definition D_in:(R->R)->(R->R)->(R->Prop)->R->Prop:=
  [f:R->R; d:R->R; D:R->Prop; x0:R](limit1_in 
    [x:R] (Rmult (Rminus (f x) (f x0)) (Rinv (Rminus x x0))) 
    (D_x D x0) (d x0) x0).

(*********)
Lemma cont_deriv:(f,d:R->R;D:R->Prop;x0:R)
         (D_in f d D x0)->(continue_in f D x0).
Unfold continue_in;Unfold D_in;Unfold limit1_in;Unfold limit_in;Simpl;
 Intros;Cut (Rgt (Rminus eps (Rabsolu (d x0))) R0)\/
            ~(Rgt (Rminus eps (Rabsolu (d x0))) R0).
Intro;Elim H1;Clear H1;Intro.
Elim (H (Rminus eps (Rabsolu (d x0))) H1);Clear H;Intros;Elim H;Clear H;
 Intros;Split with (Rmin R1 x);Split.
Generalize Rlt_R0_R1;Intro Hyp;Fold (Rgt R1 R0) in Hyp;
 Elim (Rmin_Rgt R1 x R0);Intros a b;
 Apply (b (conj (Rgt R1 R0) (Rgt x R0) (Hyp) H)).
Intros; Elim H3;Clear H3;Intros;
 Generalize (let (H1,H2)=(Rmin_Rgt R1 x (R_dist x1 x0)) in H1);
 Unfold Rgt;Intro;Elim (H5 H4);Clear H5;Intros;
 Generalize (H2 x1 (conj (D_x D x0 x1) (Rlt (R_dist x1 x0) x) H3 H6));
 Clear H2;Intro;Unfold D_x in H3;Elim H3;Intros;
 Generalize (sym_not_eqT R x0 x1 H8);Clear H8;Intro H8;
 Generalize (Rminus_eq_contra x1 x0 H8);Clear H7 H8;
 Intro;Generalize H2;Pattern 1 (d x0); 
 Rewrite <-(let (H1,H2)=(Rmult_ne (d x0)) in H2);
 Rewrite <-(Rinv_l (Rminus x1 x0) H7); Unfold R_dist;Unfold 1 Rminus;
 Rewrite (Rmult_sym (Rminus (f x1) (f x0)) (Rinv (Rminus x1 x0)));
 Rewrite (Rmult_sym (Rmult (Rinv (Rminus x1 x0)) (Rminus x1 x0)) (d x0));
 Rewrite <-(Ropp_mul1 (d x0) (Rmult (Rinv (Rminus x1 x0)) (Rminus x1 x0)));
 Rewrite (Rmult_sym (Ropp (d x0))
                    (Rmult (Rinv (Rminus x1 x0)) (Rminus x1 x0)));
 Rewrite (Rmult_assoc (Rinv (Rminus x1 x0)) (Rminus x1 x0) (Ropp (d x0)));
 Rewrite <-(Rmult_Rplus_distr (Rinv (Rminus x1 x0)) (Rminus (f x1) (f x0))
                   (Rmult (Rminus x1 x0) (Ropp (d x0))));
 Rewrite (Rabsolu_mult (Rinv (Rminus x1 x0))
                       (Rplus (Rminus (f x1) (f x0))
                              (Rmult (Rminus x1 x0) (Ropp (d x0)))));
 Clear H2;Intro;Generalize (Rlt_monotony (Rabsolu (Rminus x1 x0)) 
        (Rmult (Rabsolu (Rinv (Rminus x1 x0)))
           (Rabsolu
             (Rplus (Rminus (f x1) (f x0))
               (Rmult (Rminus x1 x0) (Ropp (d x0))))))
         (Rminus eps (Rabsolu (d x0)))
        (Rabsolu_pos_lt (Rminus x1 x0) H7) H2); 
 Rewrite <-(Rmult_assoc (Rabsolu (Rminus x1 x0)) 
                 (Rabsolu (Rinv (Rminus x1 x0)))
               (Rabsolu
           (Rplus (Rminus (f x1) (f x0))
             (Rmult (Rminus x1 x0) (Ropp (d x0)))))); 
 Rewrite (Rabsolu_Rinv (Rminus x1 x0) H7);
 Rewrite (Rinv_r (Rabsolu (Rminus x1 x0)) 
                 (Rabsolu_no_R0 (Rminus x1 x0) H7));
 Rewrite (let (H1,H2)=(Rmult_ne (Rabsolu
         (Rplus (Rminus (f x1) (f x0))
           (Rmult (Rminus x1 x0) (Ropp (d x0)))))) in H2);
 Unfold 4 Rminus;
 Rewrite (Rmult_Rplus_distr (Rabsolu (Rminus x1 x0)) eps 
                (Ropp (Rabsolu (d x0))));
 Rewrite (Rmult_sym (Rabsolu (Rminus x1 x0)) (Ropp (Rabsolu (d x0))));
 Rewrite (Ropp_mul1 (Rabsolu (d x0)) (Rabsolu (Rminus x1 x0)));
 Rewrite <-(Rabsolu_mult (d x0) (Rminus x1 x0)); 
 Generalize (Rabsolu_triang_inv (Rminus (f x1) (f x0))
         (Rmult (Rminus x1 x0) (d x0)));Intro;
 Rewrite (Rmult_sym (Rminus x1 x0) (Ropp (d x0)));
 Rewrite (Ropp_mul1 (d x0) (Rminus x1 x0));
 Fold (Rminus (Rminus (f x1) (f x0)) (Rmult (d x0) (Rminus x1 x0)));
 Rewrite (Rmult_sym (Rminus x1 x0) (d x0)) in H8;
 Clear H2;Intro;Generalize (Rle_lt_trans 
           (Rminus (Rabsolu (Rminus (f x1) (f x0)))
           (Rabsolu (Rmult (d x0) (Rminus x1 x0))))
          (Rabsolu
           (Rminus (Rminus (f x1) (f x0)) (Rmult (d x0) (Rminus x1 x0))))
          (Rplus (Rmult (Rabsolu (Rminus x1 x0)) eps)
           (Ropp (Rabsolu (Rmult (d x0) (Rminus x1 x0))))) H8 H2);
 Unfold 1 Rminus;
 Rewrite (Rplus_sym (Rabsolu (Rminus (f x1) (f x0))) 
                    (Ropp (Rabsolu (Rmult (d x0) (Rminus x1 x0)))));
 Rewrite (Rplus_sym (Rmult (Rabsolu (Rminus x1 x0)) eps)
                    (Ropp (Rabsolu (Rmult (d x0) (Rminus x1 x0)))));
 Clear H8 H2;Intro;Generalize (Rlt_anti_compatibility  
            (Ropp (Rabsolu (Rmult (d x0) (Rminus x1 x0)))) 
            (Rabsolu (Rminus (f x1) (f x0)))
            (Rmult (Rabsolu (Rminus x1 x0)) eps) H2);
 Clear H2;Intro;Unfold Rgt in H0;Unfold R_dist in H5;
 Generalize (Rlt_monotony eps (Rabsolu (Rminus x1 x0)) R1 H0 H5);
 Rewrite (let (H1,H2)=(Rmult_ne eps) in H1); 
 Rewrite (Rmult_sym eps (Rabsolu (Rminus x1 x0)));
 Intro;Apply (Rlt_trans (Rabsolu (Rminus (f x1) (f x0)))
                        (Rmult (Rabsolu (Rminus x1 x0)) eps)
                        eps H2 H8).
(**)
Elim (H eps H0);Clear H;Intros;Elim H;Clear H;Intros;
 Split with (Rmin (Rmin (Rinv (Rplus R1 R1)) x) 
              (Rmult eps (Rinv (Rabsolu (Rmult (Rplus R1 R1) (d x0))))));
 Split.
Cut (Rgt (Rmin (Rinv (Rplus R1 R1)) x) R0).
Cut (Rgt (Rmult eps (Rinv (Rabsolu (Rmult (Rplus R1 R1) (d x0))))) R0).
Intros;Elim (Rmin_Rgt (Rmin (Rinv (Rplus R1 R1)) x) 
            (Rmult eps (Rinv (Rabsolu (Rmult (Rplus R1 R1) (d x0))))) R0);
 Intros a b;
 Apply (b (conj (Rgt (Rmin (Rinv (Rplus R1 R1)) x) R0)
       (Rgt (Rmult eps (Rinv (Rabsolu (Rmult (Rplus R1 R1) (d x0))))) R0)
        H4 H3)).
Generalize (Rgt_not_le (Rminus eps (Rabsolu (d x0))) R0 H1);Intro;
 Generalize (Rminus_le eps (Rabsolu (d x0)) H3);Intro;Generalize H0;
 Intro;Unfold Rgt in H5;Generalize (Rlt_le_trans R0 eps (Rabsolu (d x0))
                                          H5 H4);Intro;
 Fold (Rgt (Rabsolu (d x0)) R0) in H6;Cut ~(Rplus R1 R1)==R0.
Intro;Generalize (Rabsolu_pos_lt (Rplus R1 R1) H7);Intro; 
 Fold (Rgt (Rabsolu (Rplus R1 R1)) R0) in H8;
 Generalize (Rmult_gt (Rabsolu (Rplus R1 R1)) (Rabsolu (d x0)) H8 H6);
 Intro;Unfold Rgt in H9; 
  Rewrite <-(Rabsolu_mult (Rplus R1 R1) (d x0)) in H9;
 Generalize (Rlt_Rinv (Rabsolu (Rmult (Rplus R1 R1) (d x0))) H9);Intro;
 Fold (Rgt (Rinv (Rabsolu (Rmult (Rplus R1 R1) (d x0)))) R0) in H10; 
 Apply (Rmult_gt eps (Rinv (Rabsolu (Rmult (Rplus R1 R1) (d x0)))) H0 H10).
Apply (imp_not_Req (Rplus R1 R1) R0).      
Right;Unfold Rgt;Generalize Rlt_R0_R1;Intro;
 Generalize (Rlt_compatibility R1 R0 R1 H7);Intro;
 Rewrite (let (H1,H2)=(Rplus_ne R1) in H1) in H8;
 Apply (Rlt_trans R0 R1 (Rplus R1 R1) H7 H8).
Elim (Rmin_Rgt (Rinv (Rplus R1 R1)) x R0);Intros a b;
 Cut (Rlt R0 (Rplus R1 R1)).
Intro;Generalize (Rlt_Rinv (Rplus R1 R1) H3);Intro;
 Fold (Rgt (Rinv (Rplus R1 R1)) R0) in H4;
 Apply (b (conj (Rgt (Rinv (Rplus R1 R1)) R0) (Rgt x R0) H4 H)).
Generalize Rlt_R0_R1;Intro;
 Generalize (Rlt_compatibility R1 R0 R1 H3);Intro;
 Rewrite (let (H1,H2)=(Rplus_ne R1) in H1) in H4;
 Apply (Rlt_trans R0 R1 (Rplus R1 R1) H3 H4).
Intros;Elim H3;Clear H3;Intros;
 Generalize (let (H1,H2)=(Rmin_Rgt (Rmin (Rinv (Rplus R1 R1)) x)
       (Rmult eps (Rinv (Rabsolu (Rmult (Rplus R1 R1) (d x0)))))
       (R_dist x1 x0)) in H1);Unfold Rgt;Intro;Elim (H5 H4);Clear H5;
 Intros;
 Generalize (let (H1,H2)=(Rmin_Rgt (Rinv (Rplus R1 R1)) x
          (R_dist x1 x0)) in H1);Unfold Rgt;Intro;Elim (H7 H5);Clear H7;
 Intros;Clear H4 H5;
 Generalize (H2 x1 (conj (D_x D x0 x1) (Rlt (R_dist x1 x0) x) H3 H8));
 Clear H2;Intro;Unfold D_x in H3;Elim H3;Intros;
 Generalize (sym_not_eqT R x0 x1 H5);Clear H5;Intro H5;
 Generalize (Rminus_eq_contra x1 x0 H5);
 Intro;Generalize H2;Pattern 1 (d x0); 
 Rewrite <-(let (H1,H2)=(Rmult_ne (d x0)) in H2);
 Rewrite <-(Rinv_l (Rminus x1 x0) H9); Unfold R_dist;Unfold 1 Rminus;
 Rewrite (Rmult_sym (Rminus (f x1) (f x0)) (Rinv (Rminus x1 x0)));
 Rewrite (Rmult_sym (Rmult (Rinv (Rminus x1 x0)) (Rminus x1 x0)) (d x0));
 Rewrite <-(Ropp_mul1 (d x0) (Rmult (Rinv (Rminus x1 x0)) (Rminus x1 x0)));
 Rewrite (Rmult_sym (Ropp (d x0))
                    (Rmult (Rinv (Rminus x1 x0)) (Rminus x1 x0)));
 Rewrite (Rmult_assoc (Rinv (Rminus x1 x0)) (Rminus x1 x0) (Ropp (d x0)));
 Rewrite <-(Rmult_Rplus_distr (Rinv (Rminus x1 x0)) (Rminus (f x1) (f x0))
                   (Rmult (Rminus x1 x0) (Ropp (d x0))));
 Rewrite (Rabsolu_mult (Rinv (Rminus x1 x0))
                       (Rplus (Rminus (f x1) (f x0))
                              (Rmult (Rminus x1 x0) (Ropp (d x0)))));
 Clear H2;Intro;Generalize (Rlt_monotony (Rabsolu (Rminus x1 x0)) 
        (Rmult (Rabsolu (Rinv (Rminus x1 x0)))
           (Rabsolu
             (Rplus (Rminus (f x1) (f x0))
               (Rmult (Rminus x1 x0) (Ropp (d x0)))))) eps 
        (Rabsolu_pos_lt (Rminus x1 x0) H9) H2); 
 Rewrite <-(Rmult_assoc (Rabsolu (Rminus x1 x0)) 
                 (Rabsolu (Rinv (Rminus x1 x0)))
               (Rabsolu
           (Rplus (Rminus (f x1) (f x0))
             (Rmult (Rminus x1 x0) (Ropp (d x0)))))); 
 Rewrite (Rabsolu_Rinv (Rminus x1 x0) H9);
 Rewrite (Rinv_r (Rabsolu (Rminus x1 x0)) 
                 (Rabsolu_no_R0 (Rminus x1 x0) H9));
 Rewrite (let (H1,H2)=(Rmult_ne (Rabsolu
         (Rplus (Rminus (f x1) (f x0))
           (Rmult (Rminus x1 x0) (Ropp (d x0)))))) in H2);
 Generalize (Rabsolu_triang_inv (Rminus (f x1) (f x0))
         (Rmult (Rminus x1 x0) (d x0)));Intro;
 Rewrite (Rmult_sym (Rminus x1 x0) (Ropp (d x0)));
 Rewrite (Ropp_mul1 (d x0) (Rminus x1 x0));
 Fold (Rminus (Rminus (f x1) (f x0)) (Rmult (d x0) (Rminus x1 x0)));
 Rewrite (Rmult_sym (Rminus x1 x0) (d x0)) in H10;
 Clear H2;Intro;Generalize (Rle_lt_trans 
           (Rminus (Rabsolu (Rminus (f x1) (f x0)))
           (Rabsolu (Rmult (d x0) (Rminus x1 x0))))
          (Rabsolu
           (Rminus (Rminus (f x1) (f x0)) (Rmult (d x0) (Rminus x1 x0))))
          (Rmult (Rabsolu (Rminus x1 x0)) eps) H10 H2);
 Clear H2;Intro;
 Generalize (Rlt_compatibility (Rabsolu (Rmult (d x0) (Rminus x1 x0)))
   (Rminus (Rabsolu (Rminus (f x1) (f x0)))
           (Rabsolu (Rmult (d x0) (Rminus x1 x0))))
   (Rmult (Rabsolu (Rminus x1 x0)) eps) H2);
 Unfold 2 Rminus;Rewrite (Rplus_sym (Rabsolu (Rminus (f x1) (f x0)))
    (Ropp (Rabsolu (Rmult (d x0) (Rminus x1 x0)))));
 Rewrite <-(Rplus_assoc (Rabsolu (Rmult (d x0) (Rminus x1 x0)))
  (Ropp (Rabsolu (Rmult (d x0) (Rminus x1 x0)))) 
  (Rabsolu (Rminus (f x1) (f x0))));
 Rewrite (Rplus_Ropp_r (Rabsolu (Rmult (d x0) (Rminus x1 x0))));
 Rewrite (let (H1,H2)=(Rplus_ne (Rabsolu (Rminus (f x1) (f x0)))) in H2);
 Clear H2;Intro;Cut (Rlt (Rplus (Rabsolu (Rmult (d x0) (Rminus x1 x0)))
           (Rmult (Rabsolu (Rminus x1 x0)) eps)) eps).
Intro;Apply (Rlt_trans (Rabsolu (Rminus (f x1) (f x0))) 
    (Rplus (Rabsolu (Rmult (d x0) (Rminus x1 x0)))
            (Rmult (Rabsolu (Rminus x1 x0)) eps)) eps H2 H11). 
Clear H2 H5 H3 H10;Cut (Rlt R0 (Rabsolu (d x0))).
Intro;Unfold Rgt in H0;Generalize (Rlt_monotony eps (R_dist x1 x0)
       (Rinv (Rplus R1 R1)) H0 H7);Clear H7;Intro;
 Generalize (Rlt_monotony (Rabsolu (d x0)) (R_dist x1 x0) 
    (Rmult eps (Rinv (Rabsolu (Rmult (Rplus R1 R1) (d x0))))) H2 H6);
 Clear H6;Intro;Rewrite (Rmult_sym eps (R_dist x1 x0)) in H3; 
 Unfold R_dist in H3 H5;
 Rewrite <-(Rabsolu_mult (d x0) (Rminus x1 x0)) in H5;
 Rewrite (Rabsolu_mult (Rplus R1 R1) (d x0)) in H5;
 Cut ~(Rabsolu (Rplus R1 R1))==R0.
Intro;Fold (Rgt (Rabsolu (d x0)) R0) in H2;
 Rewrite (Rinv_Rmult (Rabsolu (Rplus R1 R1)) (Rabsolu (d x0))
 H6 (imp_not_Req (Rabsolu (d x0)) R0 
  (or_intror (Rlt (Rabsolu (d x0)) R0) (Rgt (Rabsolu (d x0)) R0) H2))) 
  in H5;
 Rewrite (Rmult_sym (Rabsolu (d x0)) (Rmult eps
             (Rmult (Rinv (Rabsolu (Rplus R1 R1)))
               (Rinv (Rabsolu (d x0)))))) in H5;
 Rewrite <-(Rmult_assoc eps (Rinv (Rabsolu (Rplus R1 R1))) 
   (Rinv (Rabsolu (d x0)))) in H5;
 Rewrite (Rmult_assoc (Rmult eps (Rinv (Rabsolu (Rplus R1 R1))))
    (Rinv (Rabsolu (d x0))) (Rabsolu (d x0))) in H5;
 Rewrite (Rinv_l (Rabsolu (d x0)) (imp_not_Req (Rabsolu (d x0)) R0 
  (or_intror (Rlt (Rabsolu (d x0)) R0) (Rgt (Rabsolu (d x0)) R0) H2))) 
  in H5;
 Rewrite (let (H1,H2)=(Rmult_ne (Rmult eps (Rinv (Rabsolu (Rplus R1 R1)))))
   in H1) in H5;Cut (Rabsolu (Rplus R1 R1))==(Rplus R1 R1).
Intro;Rewrite H7 in H5;
 Generalize (Rplus_lt (Rabsolu (Rmult (d x0) (Rminus x1 x0)))
        (Rmult eps (Rinv (Rplus R1 R1)))
        (Rmult (Rabsolu (Rminus x1 x0)) eps)
        (Rmult eps (Rinv (Rplus R1 R1))) H5 H3);Intro;
 Rewrite eps2 in H10;Assumption.
Unfold Rabsolu;Case (case_Rabsolu (Rplus R1 R1));Auto.
 Intro;Cut (Rlt R0 (Rplus R1 R1)).
Intro;Generalize (Rlt_antisym R0 (Rplus R1 R1) H7);Intro;ElimType False;
 Auto.
Generalize Rlt_R0_R1;Intro;
 Generalize (Rlt_compatibility R1 R0 R1 H7);Intro;
 Rewrite (let (H1,H2)=(Rplus_ne R1) in H1) in H10;
 Apply (Rlt_trans R0 R1 (Rplus R1 R1) H7 H10).
Cut ~(Rplus R1 R1)==R0.
Intro;Red;Intro;Apply (Rabsolu_no_R0 (Rplus R1 R1) H6);Auto.
Apply (imp_not_Req (Rplus R1 R1) R0).      
Right;Unfold Rgt;Generalize Rlt_R0_R1;Intro;
 Generalize (Rlt_compatibility R1 R0 R1 H6);Intro;
 Rewrite (let (H1,H2)=(Rplus_ne R1) in H1) in H7;
 Apply (Rlt_trans R0 R1 (Rplus R1 R1) H6 H7).
Generalize (Rgt_not_le (Rminus eps (Rabsolu (d x0))) R0 H1);Intro;
 Generalize (Rminus_le eps (Rabsolu (d x0)) H2);Intro;
 Unfold Rgt in H0;Apply (Rlt_le_trans R0 eps (Rabsolu (d x0)) H0 H3).
Apply classic.
Save.

(*********)
Lemma Dconst:(D:R->Prop)(y:R)(x0:R)(D_in [x:R]y [x:R]R0 D x0).
Unfold D_in;Intros;Unfold limit1_in;Unfold limit_in;Intros;Simpl;
 Split with eps;Split;Auto.
Intros;Rewrite (eq_Rminus y y (refl_eqT R y));
 Rewrite Rmult_Ol;Unfold R_dist; 
 Rewrite (eq_Rminus R0 R0 (refl_eqT R R0));Unfold Rabsolu;
 Case (case_Rabsolu R0);Intro.
Absurd (Rlt R0 R0);Auto.
Red;Intro;Apply (Rlt_antirefl R0 H1).
Unfold Rgt in H0;Assumption.
Save.

(*********)
Lemma Dx:(D:R->Prop)(x0:R)(D_in [x:R]x [x:R]R1 D x0).
Unfold D_in;Intros;Unfold limit1_in;Unfold limit_in;Intros;Simpl;
  Split with eps;Split;Auto.
Intros;Elim H0;Clear H0;Intros;Unfold D_x in H0;
 Elim H0;Intros;
 Rewrite (Rinv_r (Rminus x x0) (Rminus_eq_contra x x0 
      (sym_not_eqT R x0 x H3)));
 Unfold R_dist; 
 Rewrite (eq_Rminus R1 R1 (refl_eqT R R1));Unfold Rabsolu;
 Case (case_Rabsolu R0);Intro.
Absurd (Rlt R0 R0);Auto.
Red;Intro;Apply (Rlt_antirefl R0 r).
Unfold Rgt in H;Assumption.
Save. 

(*********)
Lemma Dadd:(D:R->Prop)(df,dg:R->R)(f,g:R->R)(x0:R)
  (D_in f df D x0)->(D_in g dg D x0)->
  (D_in [x:R](Rplus (f x) (g x)) [x:R](Rplus (df x) (dg x)) D x0).
Unfold D_in;Intros;Generalize (limit_plus 
   [x:R](Rmult (Rminus (f x) (f x0)) (Rinv (Rminus x x0)))
   [x:R](Rmult  (Rminus (g x) (g x0)) (Rinv (Rminus x x0))) 
   (D_x D x0) (df x0) (dg x0) x0 H H0);Clear H H0;
 Unfold limit1_in;Unfold limit_in;Simpl;Intros;
 Elim (H eps H0);Clear H;Intros;Elim H;Clear H;Intros;
 Split with x;Split;Auto;Intros;Generalize (H1 x1 H2);Clear H1;Intro; 
 Rewrite (Rmult_sym (Rminus (f x1) (f x0)) (Rinv (Rminus x1 x0))) in H1;
 Rewrite (Rmult_sym (Rminus (g x1) (g x0)) (Rinv (Rminus x1 x0))) in H1;
 Rewrite <-(Rmult_Rplus_distr (Rinv (Rminus x1 x0)) 
                    (Rminus (f x1) (f x0)) 
                    (Rminus (g x1) (g x0))) in H1;
 Rewrite (Rmult_sym (Rinv (Rminus x1 x0))
           (Rplus (Rminus (f x1) (f x0)) (Rminus (g x1) (g x0)))) in H1;
 Cut (Rplus (Rminus (f x1) (f x0)) (Rminus (g x1) (g x0)))==
      (Rminus (Rplus (f x1) (g x1)) (Rplus (f x0) (g x0))).
Intro;Rewrite H3 in H1;Assumption.
Ring.
Save.

(*********)
Lemma Dmult:(D:R->Prop)(df,dg:R->R)(f,g:R->R)(x0:R)
  (D_in f df D x0)->(D_in g dg D x0)->
  (D_in [x:R](Rmult (f x) (g x))  
             [x:R](Rplus (Rmult (df x) (g x)) (Rmult (f x) (dg x))) D x0).
Intros;Unfold D_in;Generalize H H0;Intros;Unfold D_in in H H0;
 Generalize (cont_deriv f df D x0 H1);Unfold continue_in;Intro;
 Generalize (limit_mul 
   [x:R](Rmult (Rminus (g x) (g x0)) (Rinv (Rminus x x0)))
   [x:R](f x) (D_x D x0) (dg x0) (f x0) x0 H0 H3);Intro;
 Cut (limit1_in [x:R](g x0) (D_x D x0) (g x0) x0).
Intro;Generalize (limit_mul 
  [x:R](Rmult (Rminus (f x) (f x0)) (Rinv (Rminus x x0)))
  [_:R](g x0) (D_x D x0) (df x0) (g x0) x0 H H5);Clear H H0 H1 H2 H3 H5;
 Intro;Generalize (limit_plus 
  [x:R](Rmult (Rmult (Rminus (f x) (f x0)) (Rinv (Rminus x x0))) (g x0))
  [x:R](Rmult (Rmult (Rminus (g x) (g x0)) (Rinv (Rminus x x0)))
                (f x)) (D_x D x0) (Rmult (df x0) (g x0)) 
                               (Rmult (dg x0) (f x0)) x0 H H4);
 Clear H4 H;Intro;Unfold limit1_in in H;Unfold limit_in in H;
 Simpl in H;Unfold limit1_in;Unfold limit_in;Simpl;Intros;
 Elim (H eps H0);Clear H;Intros;Elim H;Clear H;Intros;
 Split with x;Split;Auto;Intros;Generalize (H1 x1 H2);Clear H1;Intro;
 Rewrite (Rmult_sym (Rminus (f x1) (f x0)) (Rinv (Rminus x1 x0))) in H1;
 Rewrite (Rmult_sym (Rminus (g x1) (g x0)) (Rinv (Rminus x1 x0))) in H1;
 Rewrite (Rmult_assoc (Rinv (Rminus x1 x0)) (Rminus (f x1) (f x0))
       (g x0)) in H1;
 Rewrite (Rmult_assoc (Rinv (Rminus x1 x0)) (Rminus (g x1) (g x0))
       (f x1)) in H1;
 Rewrite <-(Rmult_Rplus_distr (Rinv (Rminus x1 x0))
                (Rmult (Rminus (f x1) (f x0)) (g x0))
                (Rmult (Rminus (g x1) (g x0)) (f x1))) in H1;
 Rewrite (Rmult_sym (Rinv (Rminus x1 x0))
       (Rplus (Rmult (Rminus (f x1) (f x0)) (g x0))
               (Rmult (Rminus (g x1) (g x0)) (f x1)))) in H1;
 Rewrite (Rmult_sym (dg x0) (f x0)) in H1;
 Cut (Rplus (Rmult (Rminus (f x1) (f x0)) (g x0))
               (Rmult (Rminus (g x1) (g x0)) (f x1)))==
      (Rminus (Rmult (f x1) (g x1)) (Rmult (f x0) (g x0))).
Intro;Rewrite H3 in H1;Assumption.
Ring.
Unfold limit1_in;Unfold limit_in;Simpl;Intros;
 Split with eps;Split;Auto;Intros;Elim (R_dist_refl (g x0) (g x0));
 Intros a b;Rewrite (b (refl_eqT R (g x0)));Unfold Rgt in H;Assumption.
Save.

(*********)
Lemma Dmult_const:(D:R->Prop)(f,df:R->R)(x0:R)(a:R)(D_in f df D x0)->
  (D_in [x:R](Rmult a (f x)) ([x:R](Rmult a (df x))) D x0).
Intros;Generalize (Dmult D [_:R]R0 df [_:R]a f x0 (Dconst D a x0) H);
 Unfold D_in;Intros;
 Rewrite (Rmult_Ol (f x0)) in H0;
 Rewrite (let (H1,H2)=(Rplus_ne (Rmult a (df x0))) in H2) in H0;
 Assumption.
Save.

(*********)
Lemma Dopp:(D:R->Prop)(f,df:R->R)(x0:R)(D_in f df D x0)->
  (D_in [x:R](Ropp (f x)) ([x:R](Ropp (df x))) D x0).
Intros;Generalize (Dmult_const D f df x0 (Ropp R1) H); Unfold D_in;
 Unfold limit1_in;Unfold limit_in;Intros;
 Generalize (H0 eps H1);Clear H0;Intro;Elim H0;Clear H0;Intros; 
 Elim H0;Clear H0;Simpl;Intros;Split with x;Split;Auto.
Intros;Generalize (H2 x1 H3);Clear H2;Intro;Rewrite Ropp_mul1 in H2;
 Rewrite Ropp_mul1 in H2;Rewrite Ropp_mul1 in H2;
 Rewrite (let (H1,H2)=(Rmult_ne (f x1)) in H2) in H2; 
 Rewrite (let (H1,H2)=(Rmult_ne (f x0)) in H2) in H2;
 Rewrite (let (H1,H2)=(Rmult_ne (df x0)) in H2) in H2;Assumption.
Save.

(*********)
Lemma Dminus:(D:R->Prop)(df,dg:R->R)(f,g:R->R)(x0:R)
  (D_in f df D x0)->(D_in g dg D x0)->
  (D_in [x:R](Rminus (f x) (g x)) [x:R](Rminus (df x) (dg x)) D x0).
Unfold Rminus;Intros;Generalize (Dopp D g dg x0 H0);Intro;
 Apply (Dadd D df [x:R](Ropp (dg x)) f [x:R](Ropp (g x)) x0);Assumption. 
Save.

(*********)
Lemma Dx_pow_n:(n:nat)(D:R->Prop)(x0:R)
  (D_in [x:R](pow x n)  
        [x:R](Rmult (INR n) (pow x (minus n (1)))) D x0).
Induction n;Intros.
Simpl; Rewrite Rmult_Ol; Apply Dconst.
Intros;Cut n0=(minus (S n0) (1));
  [ Intro a; Rewrite <- a;Clear a | Simpl; Apply minus_n_O ].
Generalize (Dmult D [_:R]R1 
   [x:R](Rmult (INR n0) (pow x (minus n0 (1)))) [x:R]x [x:R](pow x n0) 
   x0 (Dx D x0) (H D x0));Unfold D_in;Unfold limit1_in;Unfold limit_in;
 Simpl;Intros;
 Elim (H0 eps H1);Clear H0;Intros;Elim H0;Clear H0;Intros;
 Split with x;Split;Auto.
Intros;Generalize (H2 x1 H3);Clear H2 H3;Intro;
 Rewrite (let (H1,H2)=(Rmult_ne (pow x0 n0)) in H2) in H2;
 Rewrite (tech_pow_Rmult x1 n0) in H2;
 Rewrite (tech_pow_Rmult x0 n0) in H2;
 Rewrite (Rmult_sym (INR n0) (pow x0 (minus n0 (1)))) in H2;
 Rewrite <-(Rmult_assoc x0 (pow x0 (minus n0 (1))) (INR n0)) in H2;
 Rewrite (tech_pow_Rmult x0 (minus n0 (1))) in H2;
 Elim (classic (n0=O));Intro cond.
Rewrite cond in H2;Rewrite cond;Simpl in H2;Simpl;
 Cut (Rplus R1 (Rmult (Rmult x0 R1) R0))==(Rmult R1 R1);
 [Intro A; Rewrite A in H2; Assumption|Ring].
Cut ~(n0=O)->(S (minus n0 (1)))=n0;[Intro|Omega];
 Rewrite (H3 cond) in H2; Rewrite (Rmult_sym (pow x0 n0) (INR n0)) in H2;
 Rewrite (tech_pow_Rplus x0 n0 n0) in H2; Assumption.
Save.

(*********)
Lemma Dcomp:(Df,Dg:R->Prop)(df,dg:R->R)(f,g:R->R)(x0:R)
  (D_in f df Df x0)->(D_in g dg Dg (f x0))->
  (D_in [x:R](g (f x)) [x:R](Rmult (df x) (dg (f x))) 
                       (Dgf Df Dg f) x0).
Intros Df Dg df dg f g x0 H H0;Generalize H H0;Unfold D_in;Intros;
Generalize (limit_comp f [x:R](Rmult (Rminus (g x) (g (f x0)))
                               (Rinv (Rminus x (f x0)))) (D_x Df x0)
              (D_x Dg (f x0)) 
              (f x0) (dg (f x0)) x0);Intro;
 Generalize (cont_deriv f df Df x0 H);Intro;Unfold continue_in in H4;
 Generalize (H3 H4 H2);Clear H3;Intro;
 Generalize (limit_mul [x:R](Rmult (Rminus (g (f x)) (g (f x0)))
                                   (Rinv (Rminus (f x) (f x0))))
                       [x:R](Rmult (Rminus (f x) (f x0))
                                   (Rinv (Rminus x x0))) 
                       (Dgf (D_x Df x0) (D_x Dg (f x0)) f) 
                       (dg (f x0)) (df x0) x0 H3);Intro;
 Cut (limit1_in
         [x:R](Rmult (Rminus (f x) (f x0)) (Rinv (Rminus x x0)))
         (Dgf (D_x Df x0) (D_x Dg (f x0)) f) (df x0) x0).
Intro;Generalize (H5 H6);Clear H5;Intro;
 Generalize (limit_mul 
        [x:R](Rmult (Rminus (f x) (f x0)) (Rinv (Rminus x x0))) 
        [x:R](dg (f x0))
       (D_x Df x0) (df x0) (dg (f x0)) x0 H1
    (limit_free [x:R](dg (f x0)) (D_x Df x0) x0 x0));
 Intro;
 Unfold limit1_in;Unfold limit_in;Simpl;Unfold limit1_in in H5 H7;
 Unfold limit_in in H5 H7;Simpl in H5 H7;Intros;Elim (H5 eps H8);
 Elim (H7 eps H8);Clear H5 H7;Intros;Elim H5;Elim H7;Clear H5 H7;
 Intros;Split with (Rmin x x1);Split.
Elim (Rmin_Rgt x x1 R0);Intros a b;
 Apply (b (conj (Rgt x R0) (Rgt x1 R0) H9 H5));Clear a b.
Intros;Elim H11;Clear H11;Intros;Elim (Rmin_Rgt x x1 (R_dist x2 x0));
 Intros a b;Clear b;Unfold Rgt in a;Elim (a H12);Clear H5 a;Intros;
 Unfold D_x Dgf in H11 H7 H10;Clear H12;
 Elim (classic (f x2)==(f x0));Intro.
Elim H11;Clear H11;Intros;Elim H11;Clear H11;Intros;
 Generalize (H10 x2 (conj (Df x2)/\~x0==x2 (Rlt (R_dist x2 x0) x)
        (conj (Df x2) ~x0==x2 H11 H14) H5));Intro;
 Rewrite (eq_Rminus (f x2) (f x0) H12) in H16;
 Rewrite (Rmult_Ol (Rinv (Rminus x2 x0))) in H16;
 Rewrite (Rmult_Ol (dg (f x0))) in H16;
 Rewrite H12;
 Rewrite (eq_Rminus (g (f x0)) (g (f x0)) (refl_eqT R (g (f x0))));
 Rewrite (Rmult_Ol (Rinv (Rminus x2 x0)));Assumption.
Clear H10 H5;Elim H11;Clear H11;Intros;Elim H5;Clear H5;Intros;
Cut (((Df x2)/\~x0==x2)/\(Dg (f x2))/\~(f x0)==(f x2))
        /\(Rlt (R_dist x2 x0) x1);Auto;Intro;
 Generalize (H7 x2 H14);Intro;
 Generalize (Rminus_eq_contra (f x2) (f x0) H12);Intro;
 Rewrite (Rmult_assoc (Rminus (g (f x2)) (g (f x0))) 
           (Rinv (Rminus (f x2) (f x0)))
          (Rmult (Rminus (f x2) (f x0)) (Rinv (Rminus x2 x0)))) in H15;
 Rewrite <-(Rmult_assoc (Rinv (Rminus (f x2) (f x0))) 
             (Rminus (f x2) (f x0)) (Rinv (Rminus x2 x0))) in H15;
 Rewrite (Rinv_l (Rminus (f x2) (f x0)) H16) in H15;
 Rewrite (let (H1,H2)=(Rmult_ne (Rinv (Rminus x2 x0))) in H2) in H15;
 Rewrite (Rmult_sym (df x0) (dg (f x0)));Assumption.
Clear H5 H3 H4 H2;Unfold limit1_in;Unfold limit_in;Simpl;
 Unfold limit1_in in H1;Unfold limit_in in H1;Simpl in H1;Intros;
 Elim (H1 eps H2);Clear H1;Intros;Elim H1;Clear H1;Intros;
 Split with x;Split;Auto;Intros;Unfold D_x Dgf in H4 H3;
 Elim H4;Clear H4;Intros;Elim H4;Clear H4;Intros;
 Exact (H3 x1 (conj (Df x1)/\~x0==x1 (Rlt (R_dist x1 x0) x) H4 H5)).
Save.   
