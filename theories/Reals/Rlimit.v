(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(*********************************************************)
(*           Definition of the limit                     *)
(*                                                       *)
(*********************************************************)

Require Export Rbasic_fun.
Require Export Classical_Prop.
Require DiscrR.
Require Fourier.
Require SplitAbsolu.

(*******************************)
(*      Calculus               *)
(*******************************)
(*********)
Lemma eps2_Rgt_R0:(eps:R)(Rgt eps R0)->
      (Rgt (Rmult eps (Rinv (Rplus R1 R1))) R0).
Intros;Fourier.
Save.

(*********)
Lemma eps2:(eps:R)(Rplus (Rmult eps (Rinv (Rplus R1 R1)))
                        (Rmult eps (Rinv (Rplus R1 R1))))==eps.
Intro esp;Field;DiscrR.
Save.

(*********)
Lemma eps4:(eps:R)
  (Rplus (Rmult eps (Rinv (Rplus (Rplus R1 R1) (Rplus R1 R1) )))
        (Rmult eps (Rinv (Rplus (Rplus R1 R1) (Rplus R1 R1) ))))==
                  (Rmult eps (Rinv (Rplus R1 R1))).
Intro eps;Field;DiscrR.
Save.

(*********)
Lemma Rlt_eps2_eps:(eps:R)(Rgt eps R0)->
        (Rlt (Rmult eps (Rinv (Rplus R1 R1))) eps).
Intros;Unfold Rgt in H;Pattern 2 eps;Rewrite <- Rmult_1r;
 Apply (Rlt_monotony eps (Rinv (Rplus R1 R1)) R1 H);
 Apply (Rlt_anti_compatibility (Rinv (Rplus R1 R1)) (Rinv (Rplus R1 R1))
      R1);Pattern 1 2 (Rinv (Rplus R1 R1));Rewrite <-Rmult_1l;
 Rewrite (eps2 R1);
 Pattern 1 R1;Rewrite <-Rplus_Or;
 Rewrite (Rplus_sym (Rinv (Rplus R1 R1)) R1);
 Apply (Rlt_compatibility R1 R0 (Rinv (Rplus R1 R1)) 
   (Rlt_Rinv (Rplus R1 R1) (Rlt_r_plus_R1 R1 (Rlt_le R0 R1 Rlt_R0_R1)))). 
Save.

(*********)
Lemma Rlt_eps4_eps:(eps:R)(Rgt eps R0)->
        (Rlt (Rmult eps (Rinv (Rplus (Rplus R1 R1) (Rplus R1 R1)))) eps).
Intros;Pattern 2 eps;Rewrite <-(let (H1,H2)=(Rmult_ne eps) in H1);
 Unfold Rgt in H;Apply Rlt_monotony;Auto.
 Generalize Rlt_R0_R1;Intro;
 Generalize (Rlt_compatibility R1 R0 R1 H0);Intro;
 Rewrite (let (H1,H2)=(Rplus_ne R1) in H1) in H1;
 Generalize (Rlt_compatibility R1 R1 (Rplus R1 R1) H1);Intro;
 Generalize (Rlt_compatibility (Rplus R1 R1) R1 (Rplus R1 R1) H1);Intro;
 Generalize (Rlt_trans R1 (Rplus R1 R1) (Rplus R1 (Rplus R1 R1))
    H1 H2);Intro;
 Rewrite (Rplus_sym (Rplus R1 R1) R1) in H3;
 Generalize (Rlt_trans R1 (Rplus R1 (Rplus R1 R1)) 
       (Rplus (Rplus R1 R1) (Rplus R1 R1)) H4 H3);Clear H H0 H1 H2 H3 H4;
 Intro;Rewrite <-(let (H1,H2)=(Rmult_ne 
   (Rinv (Rplus (Rplus R1 R1) (Rplus R1 R1)))) in H1);Pattern 6 R1;
 Rewrite <-(Rinv_l (Rplus (Rplus R1 R1) (Rplus R1 R1))).
 Apply (Rlt_monotony (Rinv (Rplus (Rplus R1 R1) (Rplus R1 R1)))
       R1 (Rplus (Rplus R1 R1) (Rplus R1 R1)));Auto.
Apply (Rlt_Rinv (Rplus (Rplus R1 R1) (Rplus R1 R1)));
 Apply (Rlt_trans R0 R1 (Rplus (Rplus R1 R1) (Rplus R1 R1)) Rlt_R0_R1 H).
Apply (imp_not_Req (Rplus (Rplus R1 R1) (Rplus R1 R1)) R0);Right;Unfold Rgt;
 Apply (Rlt_trans R0 R1 (Rplus (Rplus R1 R1) (Rplus R1 R1)) Rlt_R0_R1 H).
Save. 

(*********)
Lemma prop_eps:(r:R)((eps:R)(Rgt eps R0)->(Rlt r eps))->(Rle r R0).
Intros;Elim (total_order r R0); Intro.
Apply Rlt_le; Assumption.
Elim H0; Intro.
Apply eq_Rle; Assumption.
Clear H0;Generalize (H r H1); Intro;Generalize (Rlt_antirefl r);
 Intro;ElimType False; Auto.
Save.

(*********)
Definition mul_factor := [l,l':R](Rinv (Rplus R1 (Rplus (Rabsolu l) 
                                                        (Rabsolu l')))).

(*********)
Lemma mul_factor_wd : (l,l':R)
  ~(Rplus R1 (Rplus (Rabsolu l) (Rabsolu l')))==R0.
Intros;Rewrite (Rplus_sym R1 (Rplus (Rabsolu l) (Rabsolu l')));
 Apply tech_Rplus.
Cut (Rle (Rabsolu (Rplus l l')) (Rplus (Rabsolu l) (Rabsolu l'))).
Cut (Rle R0 (Rabsolu (Rplus l l'))).
Exact (Rle_trans ? ? ?).
Exact (Rabsolu_pos (Rplus l l')).
Exact (Rabsolu_triang ? ?).
Exact Rlt_R0_R1.
Save.

(*********)
Lemma mul_factor_gt:(eps:R)(l,l':R)(Rgt eps R0)->
      (Rgt (Rmult eps (mul_factor l l')) R0).
Intros;Unfold Rgt;Rewrite <- (Rmult_Or eps);Apply Rlt_monotony.
Assumption.
Unfold mul_factor;Apply Rlt_Rinv;
 Cut (Rle R1 (Rplus R1 (Rplus (Rabsolu l) (Rabsolu l')))).
Cut (Rlt R0 R1).
Exact (Rlt_le_trans ? ? ?).
Exact Rlt_R0_R1.
Replace (Rle R1 (Rplus R1 (Rplus (Rabsolu l) (Rabsolu l'))))
 with (Rle (Rplus R1 R0) (Rplus R1 (Rplus (Rabsolu l) (Rabsolu l')))).
Apply Rle_compatibility.
Cut (Rle (Rabsolu (Rplus l l')) (Rplus (Rabsolu l) (Rabsolu l'))).
Cut (Rle R0 (Rabsolu (Rplus l l'))).
Exact (Rle_trans ? ? ?).
Exact (Rabsolu_pos ?).
Exact (Rabsolu_triang ? ?).
Rewrite (proj1 ? ? (Rplus_ne R1));Trivial.
Save.

(*********)
Lemma mul_factor_gt_f:(eps:R)(l,l':R)(Rgt eps R0)->
      (Rgt (Rmin R1 (Rmult eps (mul_factor l l'))) R0).
Intros;Apply Rmin_Rgt_r;Split.
Exact Rlt_R0_R1.
Exact (mul_factor_gt eps l l' H).
Save.


(*******************************)
(*      Metric space           *)
(*******************************)

(*********)
Record Metric_Space:Type:= {
   Base:Type;
   dist:Base->Base->R;
   dist_pos:(x,y:Base)(Rge (dist x y) R0);
   dist_sym:(x,y:Base)(dist x y)==(dist y x);
   dist_refl:(x,y:Base)((dist x y)==R0<->x==y);
   dist_tri:(x,y,z:Base)(Rle (dist x y) 
              (Rplus (dist x z) (dist z y))) }.

(*******************************)
(*     Limit in Metric space   *)
(*******************************)

(*********)
Definition limit_in:=
   [X:Metric_Space; X':Metric_Space; f:(Base X)->(Base X'); 
    D:(Base X)->Prop; x0:(Base X); l:(Base X')]
   (eps:R)(Rgt eps R0)->
   (EXT alp:R | (Rgt alp R0)/\(x:(Base X))(D x)/\
                (Rlt (dist X x x0) alp)->
                (Rlt (dist X' (f x) l) eps)). 

(*******************************)
(*        Distance  in R       *)
(*******************************)

(*********)
Definition R_dist:R->R->R:=[x,y:R](Rabsolu (Rminus x y)).

(*********)
Lemma R_dist_pos:(x,y:R)(Rge (R_dist x y) R0).
Intros;Unfold R_dist;Unfold Rabsolu;Case (case_Rabsolu (Rminus x y));Intro l.
Unfold Rge;Left;Apply (Rlt_RoppO (Rminus x y) l).
Trivial.
Save.

(*********)
Lemma R_dist_sym:(x,y:R)(R_dist x y)==(R_dist y x).
Unfold R_dist;Intros;SplitAbsolu;Ring.
Generalize (Rlt_RoppO (Rminus y x) r); Intro;
 Rewrite (Ropp_distr2 y x) in H;
 Generalize (Rlt_antisym (Rminus x y) R0 r0); Intro;Unfold Rgt in H;
 ElimType False; Auto.
Generalize (minus_Rge y x r); Intro;
 Generalize (minus_Rge x y r0); Intro;
 Generalize (Rge_ge_eq x y H0 H); Intro;Rewrite H1;Ring.
Save.

(*********)
Lemma R_dist_refl:(x,y:R)((R_dist x y)==R0<->x==y).
Unfold R_dist;Intros;SplitAbsolu;Split;Intros.
Rewrite (Ropp_distr2 x y) in H;Apply sym_eqT;
 Apply (Rminus_eq y x H).
Rewrite (Ropp_distr2 x y);Generalize (sym_eqT R x y H);Intro;
 Apply (eq_Rminus y x H0).
Apply (Rminus_eq x y H).
Apply (eq_Rminus x y H). 
Save.

Lemma R_dist_eq:(x:R)(R_dist x x)==R0.
Unfold R_dist;Intros;SplitAbsolu;Intros;Ring.
Save.

(***********)
Lemma R_dist_tri:(x,y,z:R)(Rle (R_dist x y) 
                   (Rplus (R_dist x z) (R_dist z y))).
Intros;Unfold R_dist; Unfold Rabsolu;
 Case (case_Rabsolu (Rminus x y)); Case (case_Rabsolu (Rminus x z));
 Case (case_Rabsolu (Rminus z y));Intros.
Rewrite (Ropp_distr2 x y); Rewrite (Ropp_distr2 x z);
 Rewrite (Ropp_distr2 z y);Unfold Rminus;
 Rewrite (Rplus_sym y (Ropp z));
 Rewrite (Rplus_sym z (Ropp x));
 Rewrite (Rplus_assoc (Ropp x) z (Rplus (Ropp z) y));
 Rewrite <-(Rplus_assoc z (Ropp z) y);Rewrite (Rplus_Ropp_r z);
 Elim (Rplus_ne y);Intros a b;Rewrite b;Clear a b;
 Rewrite (Rplus_sym y (Ropp x));
 Apply (eq_Rle (Rplus (Ropp x) y) (Rplus (Ropp x) y) 
        (refl_eqT R (Rplus (Ropp x) y))).
Rewrite (Ropp_distr2 x y);Rewrite (Ropp_distr2 x z);Unfold Rminus;
 Rewrite (Rplus_sym y (Ropp x));
 Rewrite (Rplus_sym z (Ropp x));
 Rewrite (Rplus_assoc (Ropp x) z (Rplus z (Ropp y)));
 Apply (Rle_compatibility (Ropp x) y 
        (Rplus z (Rplus z (Ropp y))));
 Rewrite (Rplus_sym z (Rplus z (Ropp y)));
 Apply (Rle_anti_compatibility (Ropp y) y
        (Rplus (Rplus z (Ropp y)) z));Rewrite (Rplus_Ropp_l y);
 Rewrite (Rplus_sym (Ropp y) (Rplus (Rplus z (Ropp y)) z));
 Rewrite (Rplus_assoc (Rplus z (Ropp y)) z (Ropp y));
 Fold (Rminus z y);Generalize (Rle_sym2 R0 (Rminus z y) r);Intro;
 Generalize (Rle_compatibility (Rminus z y) R0 (Rminus z y) H);Intro;
 Elim (Rplus_ne (Rminus z y)); Intros a b; Rewrite a in H0; Clear a b;
 Apply (Rle_trans R0 (Rminus z y) (Rplus (Rminus z y) (Rminus z y)) 
        H H0).
Rewrite (Ropp_distr2 x y);Rewrite (Ropp_distr2 z y);Unfold Rminus;
 Rewrite (Rplus_sym y (Ropp z));
 Rewrite <- (Rplus_assoc (Rplus x (Ropp z)) (Ropp z) y);
 Rewrite (Rplus_sym (Rplus (Rplus x (Ropp z)) (Ropp z)) y);
 Apply (Rle_compatibility y (Ropp x)
        (Rplus (Rplus x (Ropp z)) (Ropp z)));
 Apply (Rle_anti_compatibility x (Ropp x)
        (Rplus (Rplus x (Ropp z)) (Ropp z)));Rewrite (Rplus_Ropp_r x);
 Rewrite (Rplus_sym x (Rplus (Rplus x (Ropp z)) (Ropp z)));
 Rewrite (Rplus_assoc (Rplus x (Ropp z)) (Ropp z) x);
 Rewrite (Rplus_sym (Ropp z) x);Fold (Rminus x z);
 Generalize (Rle_sym2 R0 (Rminus x z) r0);Intro;
 Generalize (Rle_compatibility (Rminus x z) R0 (Rminus x z) H);Intro;
 Elim (Rplus_ne (Rminus x z));Intros a b;Rewrite a in H0;Clear a b;
 Apply (Rle_trans R0 (Rminus x z) (Rplus (Rminus x z) (Rminus x z)) 
         H H0).
Unfold 2 3 Rminus;
 Rewrite <-(Rplus_assoc (Rplus x (Ropp z)) z (Ropp y));
 Rewrite (Rplus_assoc x (Ropp z) z);Rewrite (Rplus_Ropp_l z);
 Elim (Rplus_ne x);Intros a b;Rewrite a;Clear a b; Fold (Rminus x y);
 Apply (Rle_anti_compatibility (Rminus x y) (Ropp (Rminus x y))
        (Rminus x y));Rewrite (Rplus_Ropp_r (Rminus x y));
 Generalize (Rle_sym2 R0 (Rminus x z) r0);Intro;
 Generalize (Rle_sym2 R0 (Rminus z y) r);Intro;
 Generalize (Rle_compatibility (Rminus z y) R0 (Rminus x z) H);Intro;
 Elim (Rplus_ne (Rminus z y));Intros a b;Rewrite a in H1;Clear a b;
 Unfold 2 3 Rminus in H1;
 Rewrite (Rplus_assoc z (Ropp y) (Rplus x (Ropp z))) in H1;
 Rewrite (Rplus_sym z (Rplus (Ropp y) (Rplus x (Ropp z)))) 
          in H1;
 Rewrite <-(Rplus_assoc (Ropp y) x (Ropp z)) in H1;
 Rewrite (Rplus_assoc (Rplus (Ropp y) x) (Ropp z) z) in H1;
 Rewrite (Rplus_Ropp_l z) in H1;
 Elim (Rplus_ne (Rplus (Ropp y) x));Intros a b;Rewrite a in H1;
 Clear a b;Rewrite (Rplus_sym (Ropp y) x) in H1;
 Fold (Rminus x y) in H1;
 Generalize (Rle_trans R0 (Rminus z y) (Rminus x y) H0 H1);Intro;
 Generalize (Rle_compatibility (Rminus x y) R0 (Rminus x y) H2);
 Intro;Elim (Rplus_ne (Rminus x y));Intros a b;Rewrite a in H3;
 Clear a b;
 Apply (Rle_trans R0 (Rminus x y) (Rplus (Rminus x y) (Rminus x y)) 
         H2 H3). 
Generalize (Rminus_lt z y r);Intro;Generalize (Rminus_lt x z r0);
 Intro;Generalize (Rlt_trans x z y H0 H);Intro;
 Generalize (Rlt_minus x y H1);Intro;
 Generalize (Rle_not R0 (Rminus x y) H2);Intro;
 Generalize (Rle_sym2 R0 (Rminus x y) r1);Intro;
 ElimType False;Auto.
Rewrite (Ropp_distr2 x z);Unfold Rminus;
 Rewrite (Rplus_sym x (Ropp y));
 Rewrite <-(Rplus_assoc (Rplus z (Ropp x)) z (Ropp y));
 Rewrite (Rplus_sym (Rplus (Rplus z (Ropp x)) z) (Ropp y));
 Apply (Rle_compatibility (Ropp y) x 
        (Rplus (Rplus z (Ropp x)) z));
 Apply (Rle_anti_compatibility (Ropp x) x 
        (Rplus (Rplus z (Ropp x)) z));
 Rewrite (Rplus_Ropp_l x);
 Rewrite (Rplus_sym (Ropp x) (Rplus (Rplus z (Ropp x)) z));
 Rewrite (Rplus_assoc (Rplus z (Ropp x)) z (Ropp x));
 Fold (Rminus z x);Generalize (Rminus_lt x z r0);Intro;
 Generalize (Rlt_RoppO (Rminus x z) r0);Intro;
 Rewrite (Ropp_distr2 x z) in H0;
 Generalize (Rgt_ge (Rminus z x) R0 H0);Intro;
 Generalize (Rle_sym2 R0 (Rminus z x) H1);Intro;
 Generalize (Rle_compatibility (Rminus z x) R0 (Rminus z x) H2); 
 Intro;Elim (Rplus_ne (Rminus z x)); Intros a b; Rewrite a in H3; 
 Clear a b;
 Apply (Rle_trans R0 (Rminus z x) (Rplus (Rminus z x) (Rminus z x)) 
        H2 H3).
Rewrite (Ropp_distr2 z y);Unfold Rminus;
 Rewrite (Rplus_assoc x (Ropp z) (Rplus y (Ropp z)));
 Apply (Rle_compatibility x (Ropp y) 
        (Rplus (Ropp z) (Rplus y (Ropp z))));
 Apply (Rle_anti_compatibility y (Ropp y) 
        (Rplus (Ropp z) (Rplus y (Ropp z))));
 Rewrite (Rplus_Ropp_r y);
 Rewrite <-(Rplus_assoc y  (Ropp z) (Rplus y (Ropp z)));
 Fold (Rminus y z);Generalize (Rlt_Ropp (Rminus z y) R0 r);Intro;
 Rewrite Ropp_O in H;Rewrite (Ropp_distr2 z y) in H;
 Generalize (Rgt_ge (Rminus y z) R0 H);Intro;
 Generalize (Rle_sym2 R0 (Rminus y z) H0);Intro;
 Generalize (Rle_compatibility (Rminus y z) R0 (Rminus y z) H1);
 Intro;Elim (Rplus_ne (Rminus y z)); Intros a b; Rewrite a in H2;
 Clear a b;
 Apply (Rle_trans R0 (Rminus y z) (Rplus (Rminus y z) (Rminus y z)) 
        H1 H2).
Unfold 2 3 Rminus;
 Rewrite (Rplus_assoc  x (Ropp z) (Rplus z (Ropp y)));
 Rewrite <-(Rplus_assoc (Ropp z) z (Ropp y));
 Rewrite (Rplus_Ropp_l z);Elim (Rplus_ne (Ropp y));Intros a b;Rewrite b;
 Clear a b;Fold (Rminus x y);
 Apply (eq_Rle (Rminus x y) (Rminus x y) (refl_eqT R (Rminus x y))).
Save.

(*********)
Lemma R_dist_plus: (a,b,c,d:R)(Rle (R_dist (Rplus a c) (Rplus b d))
                   (Rplus (R_dist a b) (R_dist c d))).
Intros;Unfold R_dist;
 Replace (Rminus (Rplus a c) (Rplus b d))
  with (Rplus (Rminus a b) (Rminus c d)).
Exact (Rabsolu_triang (Rminus a b) (Rminus c d)).
Ring.
Save.

(*******************************)
(*    R is a metric space      *)
(*******************************)

(*********)
Definition R_met:Metric_Space:=(Build_Metric_Space R R_dist 
  R_dist_pos R_dist_sym R_dist_refl R_dist_tri).

(*******************************)
(*         Limit 1 arg         *)
(*******************************)
(*********)
Definition Dgf:=[Df,Dg:R->Prop][f:R->R][x:R](Df x)/\(Dg (f x)).

(*********)
Definition limit1_in:(R->R)->(R->Prop)->R->R->Prop:=
  [f:R->R; D:R->Prop; l:R; x0:R](limit_in R_met R_met f D x0 l).

(*********)
Lemma tech_limit:(f:R->R)(D:R->Prop)(l:R)(x0:R)(D x0)->
   (limit1_in f D l x0)->l==(f x0).
Unfold limit1_in;Unfold limit_in;Simpl;Intros;Apply NNPP;Red;Intro;
 Generalize (R_dist_pos (f x0) l);Intro;Unfold Rge in H2;Elim H2;Intro;
 Clear H2.
Elim (H0 (R_dist (f x0) l) H3);Intros;Elim H2;Clear H2 H0;
 Intros;Generalize (H2 x0);Clear H2;Intro;Elim (R_dist_refl x0 x0);
 Intros a b;Clear a;Rewrite (b (refl_eqT R x0)) in H2;Clear b;
 Unfold Rgt in H0;Generalize (H2 (conj (D x0) (Rlt R0 x) H H0));Intro;
 Clear H2;Generalize (Rlt_antirefl (R_dist (f x0) l));Intro;Auto.
Elim (R_dist_refl (f x0) l);Intros a b;Clear b;Generalize (a H3);Intro;
Generalize (sym_eqT R (f x0) l H2);Intro;Auto.
Save. 

(*********)
Lemma tech_limit_contr:(f:R->R)(D:R->Prop)(l:R)(x0:R)(D x0)->~l==(f x0)
   ->~(limit1_in f D l x0).
Intros;Generalize (tech_limit f D l x0);Tauto.
Save.

(*********)
Lemma lim_x:(D:R->Prop)(x0:R)(limit1_in [x:R]x D x0 x0).
Unfold limit1_in; Unfold limit_in; Simpl; Intros;Split with eps;
 Split; Auto;Intros;Elim H0; Intros; Auto.
Save.

(*********)
Lemma limit_plus:(f,g:R->R)(D:R->Prop)(l,l':R)(x0:R)
   (limit1_in f D l x0)->(limit1_in g D l' x0)->
   (limit1_in [x:R](Rplus (f x) (g x)) D (Rplus l l') x0).
Intros;Unfold limit1_in; Unfold limit_in; Simpl; Intros;
 Elim (H (Rmult eps (Rinv (Rplus R1 R1))) (eps2_Rgt_R0 eps H1));
  Elim (H0 (Rmult eps (Rinv (Rplus R1 R1))) (eps2_Rgt_R0 eps H1));
 Simpl;Clear H H0; Intros; Elim H; Elim H0; Clear H H0; Intros;
  Split with (Rmin x1 x); Split.
Exact (Rmin_Rgt_r x1 x R0 (conj ? ? H H2)).
Intros;Elim H4; Clear H4; Intros;
 Cut (Rlt (Rplus (R_dist (f x2) l) (R_dist (g x2) l')) eps).
 Cut (Rle (R_dist (Rplus (f x2) (g x2)) (Rplus l l'))
      (Rplus (R_dist (f x2) l) (R_dist (g x2) l'))).
Exact (Rle_lt_trans ? ? ?).
Exact (R_dist_plus ? ? ? ?).
Elim (Rmin_Rgt_l x1 x (R_dist x2 x0) H5); Clear H5; Intros.
Generalize (H3 x2 (conj (D x2) (Rlt (R_dist x2 x0) x) H4 H6));
 Generalize (H0 x2 (conj (D x2) (Rlt (R_dist x2 x0) x1) H4 H5));
 Intros;
 Replace eps
 with (Rplus (Rmult eps (Rinv (Rplus R1 R1)))
        (Rmult eps (Rinv (Rplus R1 R1)))).
Exact (Rplus_lt ? ? ? ? H7 H8).
Exact (eps2 eps).
Save.

(*********)
Lemma limit_Ropp:(f:R->R)(D:R->Prop)(l:R)(x0:R)
   (limit1_in f D l x0)->(limit1_in [x:R](Ropp (f x)) D (Ropp l) x0).
Unfold limit1_in;Unfold limit_in;Simpl;Intros;Elim (H eps H0);Clear H;
 Intros;Elim H;Clear H;Intros;Split with x;Split;Auto;Intros;
 Generalize (H1 x1 H2);Clear H1;Intro;Unfold R_dist;Unfold Rminus;
 Rewrite (Ropp_Ropp l);Rewrite (Rplus_sym (Ropp (f x1)) l);
 Fold (Rminus l (f x1));Fold (R_dist l (f x1));Rewrite R_dist_sym;
 Assumption.
Save.

(*********)
Lemma limit_minus:(f,g:R->R)(D:R->Prop)(l,l':R)(x0:R)
   (limit1_in f D l x0)->(limit1_in g D l' x0)->
   (limit1_in [x:R](Rminus (f x) (g x)) D (Rminus l l') x0).
Intros;Unfold Rminus;Generalize (limit_Ropp g D l' x0 H0);Intro;
 Exact (limit_plus f [x:R](Ropp (g x)) D l (Ropp l') x0 H H1).
Save.

(*********)
Lemma limit_free:(f:R->R)(D:R->Prop)(x:R)(x0:R)
   (limit1_in [h:R](f x) D (f x) x0).
Unfold limit1_in;Unfold limit_in;Simpl;Intros;Split with eps;Split;
 Auto;Intros;Elim (R_dist_refl (f x) (f x));Intros a b;
 Rewrite (b (refl_eqT R (f x)));Unfold Rgt in H;Assumption.
Save.

(*********)
Lemma limit_mul:(f,g:R->R)(D:R->Prop)(l,l':R)(x0:R)
   (limit1_in f D l x0)->(limit1_in g D l' x0)->
   (limit1_in [x:R](Rmult (f x) (g x)) D (Rmult l l') x0).
Intros;Unfold limit1_in; Unfold limit_in; Simpl; Intros; 
 Elim (H (Rmin R1 (Rmult eps (mul_factor l l'))) 
                   (mul_factor_gt_f eps l l' H1));
 Elim (H0 (Rmult eps (mul_factor l l')) (mul_factor_gt eps l l' H1));
 Clear H H0; Simpl; Intros; Elim H; Elim H0; Clear H H0; Intros;
 Split with (Rmin x1 x); Split.
Exact (Rmin_Rgt_r x1 x R0 (conj ? ? H H2)).
Intros; Elim H4; Clear H4; Intros;Unfold R_dist;
 Replace (Rminus (Rmult (f x2) (g x2)) (Rmult l l')) with 
     (Rplus (Rmult (f x2) (Rminus (g x2) l')) (Rmult l' (Rminus (f x2) l))).
Cut (Rlt (Rplus (Rabsolu (Rmult (f x2) (Rminus (g x2) l'))) (Rabsolu (Rmult l' 
 (Rminus (f x2) l)))) eps). 
Cut (Rle (Rabsolu (Rplus (Rmult (f x2) (Rminus (g x2) l')) (Rmult l' (Rminus 
  (f x2) l)))) (Rplus (Rabsolu (Rmult (f x2) (Rminus (g x2) l'))) (Rabsolu 
        (Rmult l' (Rminus (f x2) l))))).
Exact (Rle_lt_trans ? ? ?).
Exact (Rabsolu_triang ? ?).
Rewrite (Rabsolu_mult (f x2) (Rminus (g x2) l'));
 Rewrite (Rabsolu_mult l' (Rminus (f x2) l));
 Cut (Rle (Rplus (Rmult (Rplus R1 (Rabsolu l)) (Rmult eps (mul_factor l l'))) 
   (Rmult (Rabsolu l') (Rmult eps (mul_factor l l')))) eps).
Cut (Rlt (Rplus (Rmult (Rabsolu (f x2)) (Rabsolu (Rminus (g x2) l'))) (Rmult 
  (Rabsolu l') (Rabsolu (Rminus (f x2) l)))) (Rplus (Rmult (Rplus R1 (Rabsolu 
     l)) (Rmult eps (mul_factor l l'))) (Rmult (Rabsolu l') (Rmult eps 
      (mul_factor l l'))))).
Exact (Rlt_le_trans ? ? ?).
Elim (Rmin_Rgt_l x1 x (R_dist x2 x0) H5); Clear H5; Intros;
 Generalize (H0 x2 (conj (D x2) (Rlt (R_dist x2 x0) x1) H4 H5));Intro;
 Generalize (Rmin_Rgt_l ? ? ? H7);Intro;Elim H8;Intros;Clear H0 H8;
 Apply Rplus_lt_le_lt.
Apply Rmult_lt_0.
Apply Rle_sym1.
Exact (Rabsolu_pos (Rminus (g x2) l')).
Rewrite (Rplus_sym R1 (Rabsolu l));Unfold Rgt;Apply Rlt_r_plus_R1;
 Exact (Rabsolu_pos l).
Unfold R_dist in H9;
 Apply (Rlt_anti_compatibility (Ropp (Rabsolu l)) (Rabsolu (f x2)) 
     (Rplus R1 (Rabsolu l))).
Rewrite <- (Rplus_assoc (Ropp (Rabsolu l)) R1 (Rabsolu l));
 Rewrite (Rplus_sym (Ropp (Rabsolu l)) R1);
 Rewrite (Rplus_assoc R1 (Ropp (Rabsolu l)) (Rabsolu l));
 Rewrite (Rplus_Ropp_l (Rabsolu l));
 Rewrite (proj1 ? ? (Rplus_ne R1));
 Rewrite (Rplus_sym (Ropp (Rabsolu l)) (Rabsolu (f x2)));
 Generalize H9;
Cut (Rle (Rminus (Rabsolu (f x2)) (Rabsolu l)) (Rabsolu (Rminus (f x2) l))).
Exact (Rle_lt_trans ? ? ?).
Exact (Rabsolu_triang_inv ? ?).
Generalize (H3 x2 (conj (D x2) (Rlt (R_dist x2 x0) x) H4 H6));Trivial.
Apply Rle_monotony.
Exact (Rabsolu_pos l').
Unfold Rle;Left;Assumption.
Rewrite (Rmult_sym (Rplus R1 (Rabsolu l)) (Rmult eps (mul_factor l l')));
 Rewrite (Rmult_sym (Rabsolu l') (Rmult eps (mul_factor l l')));
 Rewrite <- (Rmult_Rplus_distr
           (Rmult eps (mul_factor l l'))
           (Rplus R1 (Rabsolu l))
           (Rabsolu l'));
 Rewrite (Rmult_assoc eps (mul_factor l l') (Rplus (Rplus R1 (Rabsolu l)) 
      (Rabsolu l')));
 Rewrite (Rplus_assoc R1 (Rabsolu l) (Rabsolu l'));Unfold mul_factor;
 Rewrite (Rinv_l (Rplus R1 (Rplus (Rabsolu l) (Rabsolu l'))) 
  (mul_factor_wd l l'));
 Rewrite (proj1 ? ? (Rmult_ne eps));Apply eq_Rle;Trivial.
Ring.
Save.

(*********)
Definition adhDa:(R->Prop)->R->Prop:=[D:R->Prop][a:R]
  (alp:R)(Rgt alp R0)->(EXT x:R | (D x)/\(Rlt (R_dist x a) alp)).

(*********)
Lemma single_limit:(f:R->R)(D:R->Prop)(l:R)(l':R)(x0:R)
  (adhDa D x0)->(limit1_in f D l x0)->(limit1_in f D l' x0)->l==l'.
Unfold limit1_in; Unfold limit_in; Intros.
Cut (eps:R)(Rgt eps R0)->(Rlt (dist R_met l l') 
                              (Rmult (Rplus R1 R1) eps)).
Clear H0 H1;Unfold dist; Unfold R_met; Unfold R_dist; 
 Unfold Rabsolu;Case (case_Rabsolu (Rminus l l')); Intros.
Cut (eps:R)(Rgt eps R0)->(Rlt (Ropp (Rminus l l')) eps).
Intro;Generalize (prop_eps (Ropp (Rminus l l')) H1);Intro;
 Generalize (Rlt_RoppO (Rminus l l') r); Intro;Unfold Rgt in H3;
 Generalize (Rle_not (Ropp (Rminus l l')) R0 H3); Intro;
 ElimType False; Auto.
Intros;Cut (Rgt (Rmult eps (Rinv (Rplus R1 R1))) R0).
Intro;Generalize (H0 (Rmult eps (Rinv (Rplus R1 R1))) H2);
 Rewrite (Rmult_sym eps (Rinv (Rplus R1 R1)));
 Rewrite <- (Rmult_assoc (Rplus R1 R1) (Rinv (Rplus R1 R1)) eps);
 Rewrite (Rinv_r (Rplus R1 R1)).
Elim (Rmult_ne eps);Intros a b;Rewrite b;Clear a b;Trivial.
Apply (imp_not_Req (Rplus R1 R1) R0);Right;Generalize Rlt_R0_R1;Intro;
 Unfold Rgt;Generalize (Rlt_compatibility R1 R0 R1 H3);Intro;
 Elim (Rplus_ne R1);Intros a b;Rewrite a in H4;Clear a b; 
 Apply (Rlt_trans R0 R1 (Rplus R1 R1) H3 H4).
Unfold Rgt;Unfold Rgt in H1;
 Rewrite (Rmult_sym eps(Rinv (Rplus R1 R1)));
 Rewrite <-(Rmult_Or (Rinv (Rplus R1 R1)));
 Apply (Rlt_monotony (Rinv (Rplus R1 R1)) R0 eps);Auto.
Apply (Rlt_Rinv (Rplus R1 R1));Cut (Rlt R1 (Rplus R1 R1)).
Intro;Apply (Rlt_trans R0 R1 (Rplus R1 R1) Rlt_R0_R1 H2).
Generalize (Rlt_compatibility R1 R0 R1 Rlt_R0_R1);Elim (Rplus_ne R1);
 Intros a b;Rewrite a;Clear a b;Trivial.
(**)
Cut (eps:R)(Rgt eps R0)->(Rlt (Rminus l l') eps).
Intro;Generalize (prop_eps (Rminus l l') H1);Intro;
 Elim (Rle_le_eq (Rminus l l') R0);Intros a b;Clear b;
 Apply (Rminus_eq l l');Apply a;Split.
Assumption.
Apply (Rle_sym2 R0 (Rminus l l') r).
Intros;Cut (Rgt (Rmult eps (Rinv (Rplus R1 R1))) R0).
Intro;Generalize (H0 (Rmult eps (Rinv (Rplus R1 R1))) H2);
 Rewrite (Rmult_sym eps (Rinv (Rplus R1 R1)));
 Rewrite <- (Rmult_assoc (Rplus R1 R1) (Rinv (Rplus R1 R1)) eps);
 Rewrite (Rinv_r (Rplus R1 R1)).
Elim (Rmult_ne eps);Intros a b;Rewrite b;Clear a b;Trivial.
Apply (imp_not_Req (Rplus R1 R1) R0);Right;Generalize Rlt_R0_R1;Intro;
 Unfold Rgt;Generalize (Rlt_compatibility R1 R0 R1 H3);Intro;
 Elim (Rplus_ne R1);Intros a b;Rewrite a in H4;Clear a b; 
 Apply (Rlt_trans R0 R1 (Rplus R1 R1) H3 H4).
Unfold Rgt;Unfold Rgt in H1;
 Rewrite (Rmult_sym eps(Rinv (Rplus R1 R1)));
 Rewrite <-(Rmult_Or (Rinv (Rplus R1 R1)));
 Apply (Rlt_monotony (Rinv (Rplus R1 R1)) R0 eps);Auto.
Apply (Rlt_Rinv (Rplus R1 R1));Cut (Rlt R1 (Rplus R1 R1)).
Intro;Apply (Rlt_trans R0 R1 (Rplus R1 R1) Rlt_R0_R1 H2).
Generalize (Rlt_compatibility R1 R0 R1 Rlt_R0_R1);Elim (Rplus_ne R1);
 Intros a b;Rewrite a;Clear a b;Trivial.
(**)
Intros;Unfold adhDa in H;Elim (H0 eps H2);Intros;Elim (H1 eps H2);
 Intros;Clear H0 H1;Elim H3;Elim H4;Clear H3 H4;Intros;
 Simpl;Simpl in H1 H4;Generalize (Rmin_Rgt x x1 R0);Intro;Elim H5;
 Intros;Clear H5;
 Elim (H (Rmin x x1) (H7 (conj (Rgt x R0) (Rgt x1 R0) H3 H0)));
 Intros; Elim H5;Intros;Clear H5 H H6 H7;
 Generalize (Rmin_Rgt x x1 (R_dist x2 x0));Intro;Elim H;
 Intros;Clear H H6;Unfold Rgt in H5;Elim (H5 H9);Intros;Clear H5 H9;
 Generalize (H1 x2 (conj (D x2) (Rlt (R_dist x2 x0) x1) H8 H6));
 Generalize (H4 x2 (conj (D x2) (Rlt (R_dist x2 x0) x) H8 H));
 Clear H8 H H6 H1 H4 H0 H3;Intros;
 Generalize (Rplus_lt (R_dist (f x2) l) eps (R_dist (f x2) l') eps 
  H H0); Unfold R_dist;Intros;
 Rewrite (Rabsolu_minus_sym (f x2) l) in H1;
 Rewrite (Rmult_sym (Rplus R1 R1) eps);Rewrite (Rmult_Rplus_distr eps R1 R1);
 Elim (Rmult_ne eps);Intros a b;Rewrite a;Clear a b;
 Generalize (R_dist_tri l l' (f x2));Unfold R_dist;Intros;
 Apply (Rle_lt_trans (Rabsolu (Rminus l l')) 
  (Rplus (Rabsolu (Rminus l (f x2))) (Rabsolu (Rminus (f x2) l')))
  (Rplus eps eps) H3 H1).
Save.

(*********)
Lemma limit_comp:(f,g:R->R)(Df,Dg:R->Prop)(l,l':R)(x0:R)
   (limit1_in f Df l x0)->(limit1_in g Dg l' l)->
   (limit1_in [x:R](g (f x)) (Dgf Df Dg f) l' x0).
Unfold limit1_in;Unfold limit_in;Simpl;Intros;
 Elim (H0 eps H1);Clear H0;Intros;Elim H0;Clear H0;Intros;
 Elim (H x H0);Clear H;Intros;Elim H;Clear H;Intros;
 Split with x1;Split;Auto;Intros;
 Elim H4;Clear H4;Intros;Unfold Dgf in H4;Elim H4;Clear H4;Intros;
 Generalize (H3 x2 (conj (Df x2) (Rlt (R_dist x2 x0) x1) H4 H5));
 Intro;Exact (H2 (f x2) (conj (Dg (f x2)) (Rlt (R_dist (f x2) l) x)
            H6 H7)).
Save.
