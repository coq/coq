(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(*********************************************************)
(*           Definition of the limit                     *)
(*                                                       *)
(*********************************************************)

Require Rbase.
Require Rfunctions.
Require Classical_Prop.
Require Fourier.
V7only [Import R_scope.]. Open Local Scope R_scope.

(*******************************)
(*      Calculus               *)
(*******************************)
(*********)
Lemma eps2_Rgt_R0:(eps:R)(Rgt eps R0)->
      (Rgt (Rmult eps (Rinv (Rplus R1 R1))) R0).
Intros;Fourier.
Qed.

(*********)
Lemma eps2:(eps:R)(Rplus (Rmult eps (Rinv (Rplus R1 R1)))
                        (Rmult eps (Rinv (Rplus R1 R1))))==eps.
Intro esp.
Assert H := (double_var esp).
Unfold Rdiv in H.
Symmetry; Exact H.
Qed.

(*********)
Lemma eps4:(eps:R)
  (Rplus (Rmult eps (Rinv (Rplus (Rplus R1 R1) (Rplus R1 R1) )))
        (Rmult eps (Rinv (Rplus (Rplus R1 R1) (Rplus R1 R1) ))))==
                  (Rmult eps (Rinv (Rplus R1 R1))).
Intro eps.
Replace ``2+2`` with ``2*2``.
Pattern 3 eps; Rewrite double_var.
Rewrite (Rmult_Rplus_distrl ``eps/2`` ``eps/2`` ``/2``).
Unfold Rdiv.
Repeat Rewrite Rmult_assoc.
Rewrite <- Rinv_Rmult.
Reflexivity.
DiscrR.
DiscrR.
Ring.
Qed.

(*********)
Lemma Rlt_eps2_eps:(eps:R)(Rgt eps R0)->
        (Rlt (Rmult eps (Rinv (Rplus R1 R1))) eps).
Intros.
Pattern 2 eps; Rewrite <- Rmult_1r.
Repeat Rewrite (Rmult_sym eps).
Apply Rlt_monotony_r.
Exact H.
Apply Rlt_monotony_contra with ``2``.
Fourier.
Rewrite Rmult_1r; Rewrite <- Rinv_r_sym.
Fourier.
DiscrR.
Qed.

(*********)
Lemma Rlt_eps4_eps:(eps:R)(Rgt eps R0)->
        (Rlt (Rmult eps (Rinv (Rplus (Rplus R1 R1) (Rplus R1 R1)))) eps).
Intros.
Replace ``2+2`` with ``4``.
Pattern 2 eps; Rewrite <- Rmult_1r.
Repeat Rewrite (Rmult_sym eps).
Apply Rlt_monotony_r.
Exact H.
Apply Rlt_monotony_contra with ``4``.
Replace ``4`` with ``2*2``.
Apply Rmult_lt_pos; Fourier.
Ring.
Rewrite Rmult_1r; Rewrite <- Rinv_r_sym.
Fourier.
DiscrR.
Ring.
Qed. 

(*********)
Lemma prop_eps:(r:R)((eps:R)(Rgt eps R0)->(Rlt r eps))->(Rle r R0).
Intros;Elim (total_order r R0); Intro.
Apply Rlt_le; Assumption.
Elim H0; Intro.
Apply eq_Rle; Assumption.
Clear H0;Generalize (H r H1); Intro;Generalize (Rlt_antirefl r);
 Intro;ElimType False; Auto.
Qed.

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
Qed.

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
Qed.

(*********)
Lemma mul_factor_gt_f:(eps:R)(l,l':R)(Rgt eps R0)->
      (Rgt (Rmin R1 (Rmult eps (mul_factor l l'))) R0).
Intros;Apply Rmin_Rgt_r;Split.
Exact Rlt_R0_R1.
Exact (mul_factor_gt eps l l' H).
Qed.


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
Intros f D l x0 H H0.
Case (Rabsolu_pos (Rminus (f x0) l)); Intros H1.
Absurd (Rlt (dist R_met (f x0) l) (dist R_met (f x0) l)).
Apply Rlt_antirefl.
Case (H0 (dist R_met (f x0) l)); Auto.
Intros alpha1 (H2, H3); Apply H3; Auto; Split; Auto.
Case (dist_refl R_met x0 x0); Intros Hr1 Hr2; Rewrite Hr2; Auto.
Case (dist_refl R_met (f x0) l); Intros Hr1 Hr2; Apply sym_eqT; Auto.
Qed.

(*********)
Lemma tech_limit_contr:(f:R->R)(D:R->Prop)(l:R)(x0:R)(D x0)->~l==(f x0)
   ->~(limit1_in f D l x0).
Intros;Generalize (tech_limit f D l x0);Tauto.
Qed.

(*********)
Lemma lim_x:(D:R->Prop)(x0:R)(limit1_in [x:R]x D x0 x0).
Unfold limit1_in; Unfold limit_in; Simpl; Intros;Split with eps;
 Split; Auto;Intros;Elim H0; Intros; Auto.
Qed.

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
Qed.

(*********)
Lemma limit_Ropp:(f:R->R)(D:R->Prop)(l:R)(x0:R)
   (limit1_in f D l x0)->(limit1_in [x:R](Ropp (f x)) D (Ropp l) x0).
Unfold limit1_in;Unfold limit_in;Simpl;Intros;Elim (H eps H0);Clear H;
 Intros;Elim H;Clear H;Intros;Split with x;Split;Auto;Intros;
 Generalize (H1 x1 H2);Clear H1;Intro;Unfold R_dist;Unfold Rminus;
 Rewrite (Ropp_Ropp l);Rewrite (Rplus_sym (Ropp (f x1)) l);
 Fold (Rminus l (f x1));Fold (R_dist l (f x1));Rewrite R_dist_sym;
 Assumption.
Qed.

(*********)
Lemma limit_minus:(f,g:R->R)(D:R->Prop)(l,l':R)(x0:R)
   (limit1_in f D l x0)->(limit1_in g D l' x0)->
   (limit1_in [x:R](Rminus (f x) (g x)) D (Rminus l l') x0).
Intros;Unfold Rminus;Generalize (limit_Ropp g D l' x0 H0);Intro;
 Exact (limit_plus f [x:R](Ropp (g x)) D l (Ropp l') x0 H H1).
Qed.

(*********)
Lemma limit_free:(f:R->R)(D:R->Prop)(x:R)(x0:R)
   (limit1_in [h:R](f x) D (f x) x0).
Unfold limit1_in;Unfold limit_in;Simpl;Intros;Split with eps;Split;
 Auto;Intros;Elim (R_dist_refl (f x) (f x));Intros a b;
 Rewrite (b (refl_eqT R (f x)));Unfold Rgt in H;Assumption.
Qed.

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
Qed.

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
Qed.

(*********)
Lemma limit_comp:(f,g:R->R)(Df,Dg:R->Prop)(l,l':R)(x0:R)
   (limit1_in f Df l x0)->(limit1_in g Dg l' l)->
   (limit1_in [x:R](g (f x)) (Dgf Df Dg f) l' x0).
Unfold limit1_in limit_in Dgf;Simpl.
Intros f g Df Dg l l' x0 Hf Hg eps eps_pos.
Elim (Hg eps eps_pos).
Intros alpg lg.
Elim (Hf alpg).
2: Tauto.
Intros alpf lf.
Exists alpf.
Intuition.
Qed.

(*********)

Lemma limit_inv : (f:R->R)(D:R->Prop)(l:R)(x0:R) (limit1_in f D l x0)->~(l==R0)->(limit1_in [x:R](Rinv (f x)) D (Rinv l) x0).
Unfold limit1_in; Unfold limit_in; Simpl; Unfold R_dist; Intros; Elim (H ``(Rabsolu l)/2``).
Intros delta1 H2; Elim (H ``eps*((Rsqr l)/2)``).
Intros delta2 H3; Elim H2; Elim H3; Intros; Exists (Rmin delta1 delta2); Split.
Unfold Rmin; Case (total_order_Rle delta1 delta2); Intro; Assumption.
Intro; Generalize (H5 x); Clear H5; Intro H5; Generalize (H7 x); Clear H7; Intro H7; Intro H10; Elim H10; Intros; Cut (D x)/\``(Rabsolu (x-x0))<delta1``.
Cut (D x)/\``(Rabsolu (x-x0))<delta2``.
Intros; Generalize (H5 H11); Clear H5; Intro H5; Generalize (H7 H12); Clear H7; Intro H7; Generalize (Rabsolu_triang_inv l (f x)); Intro; Rewrite Rabsolu_minus_sym in H7; Generalize (Rle_lt_trans ``(Rabsolu l)-(Rabsolu (f x))`` ``(Rabsolu (l-(f x)))`` ``(Rabsolu l)/2`` H13 H7); Intro; Generalize (Rlt_compatibility ``(Rabsolu (f x))-(Rabsolu l)/2`` ``(Rabsolu l)-(Rabsolu (f x))`` ``(Rabsolu l)/2`` H14); Replace ``(Rabsolu (f x))-(Rabsolu l)/2+((Rabsolu l)-(Rabsolu (f x)))`` with ``(Rabsolu l)/2``.
Unfold Rminus; Rewrite Rplus_assoc; Rewrite Rplus_Ropp_l; Rewrite Rplus_Or; Intro; Cut ~``(f x)==0``.
Intro; Replace ``/(f x)+ -/l`` with ``(l-(f x))*/(l*(f x))``.
Rewrite Rabsolu_mult; Rewrite Rabsolu_Rinv.
Cut ``/(Rabsolu (l*(f x)))<2/(Rsqr l)``.
Intro; Rewrite Rabsolu_minus_sym in H5; Cut ``0<=/(Rabsolu (l*(f x)))``.
Intro; Generalize (Rmult_lt2 ``(Rabsolu (l-(f x)))`` ``eps*(Rsqr l)/2`` ``/(Rabsolu (l*(f x)))`` ``2/(Rsqr l)`` (Rabsolu_pos ``l-(f x)``) H18 H5 H17); Replace ``eps*(Rsqr l)/2*2/(Rsqr l)`` with ``eps``.
Intro; Assumption.
Unfold Rdiv; Unfold Rsqr; Rewrite Rinv_Rmult.
Repeat Rewrite Rmult_assoc.
Rewrite (Rmult_sym l).
Repeat Rewrite Rmult_assoc.
Rewrite <- Rinv_l_sym.
Rewrite Rmult_1r.
Rewrite (Rmult_sym l).
Repeat Rewrite Rmult_assoc.
Rewrite <- Rinv_l_sym.
Rewrite Rmult_1r.
Rewrite <- Rinv_l_sym.
Rewrite Rmult_1r; Reflexivity.
DiscrR.
Exact H0.
Exact H0.
Exact H0.
Exact H0.
Left; Apply Rlt_Rinv; Apply Rabsolu_pos_lt; Apply prod_neq_R0; Assumption.
Rewrite Rmult_sym; Rewrite Rabsolu_mult; Rewrite Rinv_Rmult.
Rewrite (Rsqr_abs l); Unfold Rsqr; Unfold Rdiv; Rewrite Rinv_Rmult.
Repeat Rewrite <- Rmult_assoc; Apply Rlt_monotony_r.
Apply Rlt_Rinv; Apply Rabsolu_pos_lt; Assumption.
Apply Rlt_monotony_contra with ``(Rabsolu (f x))*(Rabsolu l)*/2``.
Repeat Apply Rmult_lt_pos.
Apply Rabsolu_pos_lt; Assumption.
Apply Rabsolu_pos_lt; Assumption.
Apply Rlt_Rinv; Cut ~(O=(2)); [Intro H17; Generalize (lt_INR_0 (2) (neq_O_lt (2) H17)); Unfold INR; Intro H18; Assumption | Discriminate].
Replace ``(Rabsolu (f x))*(Rabsolu l)*/2*/(Rabsolu (f x))`` with ``(Rabsolu l)/2``.
Replace ``(Rabsolu (f x))*(Rabsolu l)*/2*(2*/(Rabsolu l))`` with ``(Rabsolu (f x))``.
Assumption.
Repeat Rewrite Rmult_assoc.
Rewrite (Rmult_sym (Rabsolu l)).
Repeat Rewrite Rmult_assoc.
Rewrite <- Rinv_l_sym.
Rewrite Rmult_1r.
Rewrite <- Rinv_l_sym.
Rewrite Rmult_1r; Reflexivity.
DiscrR.
Apply Rabsolu_no_R0.
Assumption.
Unfold Rdiv.
Repeat Rewrite Rmult_assoc.
Rewrite (Rmult_sym (Rabsolu (f x))).
Repeat Rewrite Rmult_assoc.
Rewrite <- Rinv_l_sym.
Rewrite Rmult_1r.
Reflexivity.
Apply Rabsolu_no_R0; Assumption.
Apply Rabsolu_no_R0; Assumption.
Apply Rabsolu_no_R0; Assumption.
Apply Rabsolu_no_R0; Assumption.
Apply Rabsolu_no_R0; Assumption.
Apply prod_neq_R0; Assumption.
Rewrite (Rinv_Rmult ? ? H0 H16).
Unfold Rminus; Rewrite Rmult_Rplus_distrl.
Rewrite <- Rmult_assoc.
Rewrite <- Rinv_r_sym.
Rewrite Rmult_1l.
Rewrite Ropp_mul1.
Rewrite (Rmult_sym (f x)).
Rewrite Rmult_assoc.
Rewrite <- Rinv_l_sym.
Rewrite Rmult_1r.
Reflexivity.
Assumption.
Assumption.
Red; Intro; Rewrite H16 in H15; Rewrite Rabsolu_R0 in H15; Cut ``0<(Rabsolu l)/2``.
Intro; Elim (Rlt_antirefl ``0`` (Rlt_trans ``0`` ``(Rabsolu l)/2`` ``0`` H17 H15)).
Unfold Rdiv; Apply Rmult_lt_pos.
Apply Rabsolu_pos_lt; Assumption.
Apply Rlt_Rinv; Cut ~(O=(2)); [Intro H17; Generalize (lt_INR_0 (2) (neq_O_lt (2) H17)); Unfold INR; Intro; Assumption | Discriminate].
Pattern 3 (Rabsolu l); Rewrite double_var.
Ring.
Split; [Assumption | Apply Rlt_le_trans with (Rmin delta1 delta2); [Assumption | Apply Rmin_r]].
Split; [Assumption | Apply Rlt_le_trans with (Rmin delta1 delta2); [Assumption | Apply Rmin_l]].
Change ``0<eps*(Rsqr l)/2``; Unfold Rdiv; Repeat Rewrite Rmult_assoc; Repeat Apply Rmult_lt_pos.
Assumption.
Apply Rsqr_pos_lt; Assumption.
Apply Rlt_Rinv; Cut ~(O=(2)); [Intro H3; Generalize (lt_INR_0 (2) (neq_O_lt (2) H3)); Unfold INR; Intro; Assumption | Discriminate].
Change ``0<(Rabsolu l)/2``; Unfold Rdiv; Apply Rmult_lt_pos; [Apply Rabsolu_pos_lt; Assumption | Apply Rlt_Rinv; Cut ~(O=(2)); [Intro H3; Generalize (lt_INR_0 (2) (neq_O_lt (2) H3)); Unfold INR; Intro; Assumption | Discriminate]].
Qed.
