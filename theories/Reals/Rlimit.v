
(* $Id$ *)

(*********************************************************)
(*           Definition of the limit                     *)
(*                                                       *)
(*********************************************************)

Require Export Rbasic_fun.
Require Export Classical_Prop.

(*******************************)
(*      Calculus               *)
(*******************************)
(*********)
Lemma eps2_Rgt_R0:(eps:R)(Rgt eps R0)->
      (Rgt (Rmult eps (Rinv (Rplus R1 R1))) R0).
Intros;Generalize (Rlt_compatibility R1 R0 R1 Rlt_R0_R1);Intro;
 Elim (Rplus_ne R1);Intros a b;Rewrite a in H0;Clear a b;
 Generalize (Rlt_Rinv (Rplus R1 R1) 
                       (Rlt_trans R0 R1 (Rplus R1 R1) Rlt_R0_R1 H0));Intro;
 Unfold Rgt in H;
 Generalize (Rlt_monotony (Rinv (Rplus R1 R1)) R0 eps H1 H);Intro;
 Rewrite (Rmult_Or (Rinv (Rplus R1 R1))) in H2;
 Rewrite (Rmult_sym (Rinv (Rplus R1 R1)) eps) in H2;
 Unfold Rgt;Assumption.
Save.

(*********)
Lemma eps2:(eps:R)(Rplus (Rmult eps (Rinv (Rplus R1 R1)))
                        (Rmult eps (Rinv (Rplus R1 R1))))==eps.
Intro;Rewrite<-(Rmult_Rplus_distr eps (Rinv (Rplus R1 R1)) (Rinv (Rplus R1 R1)));
 Elim (Rmult_ne eps);Intros a b;Pattern 2 eps;Rewrite <- a;Clear a b;
 Apply Rmult_mult_r;Clear eps;Cut ~(Rplus R1 R1)==R0.
Intro;Apply (r_Rmult_mult (Rplus R1 R1) 
         (Rplus (Rinv (Rplus R1 R1)) (Rinv (Rplus R1 R1))) R1);Auto;
Rewrite (Rmult_Rplus_distr (Rplus R1 R1) (Rinv (Rplus R1 R1)) 
                              (Rinv (Rplus R1 R1)));
 Rewrite (Rinv_r (Rplus R1 R1) H);Elim (Rmult_ne (Rplus R1 R1));Intros a b;
 Rewrite a;Clear a b;Reflexivity.
Red;Intro;Generalize Rlt_R0_R1;Intro;
 Generalize (Rlt_compatibility R1 R0 R1 H0);Intro;Elim (Rplus_ne R1);
 Intros a b;Rewrite a in H1;Clear a b;
 Generalize (Rlt_trans R0 R1 (Rplus R1 R1) H0 H1);Intro;
 Elim (imp_not_Req R0 (Rplus R1 R1));Auto;Left;Assumption.
Save.

(*********)
Lemma eps4:(eps:R)
  (Rplus (Rmult eps (Rinv (Rplus (Rplus R1 R1) (Rplus R1 R1) )))
        (Rmult eps (Rinv (Rplus (Rplus R1 R1) (Rplus R1 R1) ))))==
                  (Rmult eps (Rinv (Rplus R1 R1))).
Intro;Rewrite<-(Rmult_Rplus_distr eps (Rinv (Rplus (Rplus R1 R1) (Rplus R1 R1))) 
                            (Rinv (Rplus (Rplus R1 R1) (Rplus R1 R1))));
 Apply Rmult_mult_r;Clear eps;
 Rewrite <-(let (H1,H2)=
     (Rmult_ne (Rinv (Rplus (Rplus R1 R1) (Rplus R1 R1)))) in H1);
 Rewrite <-(Rmult_Rplus_distr (Rinv (Rplus (Rplus R1 R1) (Rplus R1 R1))) R1 R1);
 Cut ~(Rplus R1 R1)==R0. 
Intro;Apply (r_Rmult_mult (Rplus R1 R1) 
           (Rmult (Rinv (Rplus (Rplus R1 R1) (Rplus R1 R1))) (Rplus R1 R1)) 
           (Rinv (Rplus R1 R1)));Auto.
Rewrite (Rmult_sym (Rinv (Rplus (Rplus R1 R1) (Rplus R1 R1)))
                      (Rplus R1 R1));
 Rewrite <-(Rmult_assoc (Rplus R1 R1) (Rplus R1 R1) 
             (Rinv (Rplus (Rplus R1 R1) (Rplus R1 R1))));
 Rewrite (Rinv_r (Rplus R1 R1) H);Rewrite (Rmult_Rplus_distr (Rplus R1 R1) R1 R1);
 Rewrite (let (H1,H2)=(Rmult_ne (Rplus R1 R1)) in H1);
 Apply (Rinv_r (Rplus (Rplus R1 R1) (Rplus R1 R1))).
Apply (imp_not_Req (Rplus (Rplus R1 R1) (Rplus R1 R1)) R0);Right;Unfold Rgt;
 Generalize Rlt_R0_R1;Intro;
 Generalize (Rlt_compatibility R1 R0 R1 H0);Intro;
 Rewrite (let (H1,H2)=(Rplus_ne R1) in H1) in H1;
 Generalize (Rlt_trans R0 R1 (Rplus R1 R1) H0 H1);Intro;
 Clear H0 H1;
 Generalize (Rlt_compatibility (Rplus R1 R1) R0 (Rplus R1 R1) H2);Intro;
 Rewrite (let (H1,H2)=(Rplus_ne (Rplus R1 R1)) in H1) in H0;
 Apply (Rlt_trans R0 (Rplus R1 R1) (Rplus (Rplus R1 R1) (Rplus R1 R1))
    H2 H0).
Apply (imp_not_Req (Rplus R1 R1) R0);Right;Unfold Rgt;Generalize Rlt_R0_R1;Intro;
 Generalize (Rlt_compatibility R1 R0 R1 H);Intro;
 Rewrite (let (H1,H2)=(Rplus_ne R1) in H1) in H0;
 Apply (Rlt_trans R0 R1 (Rplus R1 R1) H H0).
Save.

(*********)
Lemma Rlt_eps2_eps:(eps:R)(Rgt eps R0)->
        (Rlt (Rmult eps (Rinv (Rplus R1 R1))) eps).
Intros;Unfold Rgt in H;Elim (Rmult_ne eps);Intros a b;Pattern 2 eps;
 Rewrite <- a;Clear a b;
 Apply (Rlt_monotony eps (Rinv (Rplus R1 R1)) R1 H);
 Apply (Rlt_anti_compatibility (Rinv (Rplus R1 R1)) (Rinv (Rplus R1 R1))
      R1);Elim (Rmult_ne (Rinv (Rplus R1 R1)));Intros a b;
 Pattern 1 2 (Rinv (Rplus R1 R1));Rewrite <-b;Clear a b;
 Rewrite (eps2 R1);Elim (Rplus_ne R1);Intros a b;Pattern 1 R1;
 Rewrite <-a;Clear a b;Rewrite (Rplus_sym (Rinv (Rplus R1 R1)) R1);
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
Intros; Unfold R_dist; Unfold Rabsolu;
 Case (case_Rabsolu (Rminus x y)); Case (case_Rabsolu (Rminus y x));
 Intros l l0.
Generalize (Rlt_RoppO (Rminus y x) l); Intro;
 Rewrite (Ropp_distr2 y x) in H;
 Generalize (Rlt_antisym (Rminus x y) R0 l0); Intro;Unfold Rgt in H;
 ElimType False; Auto.
Apply (Ropp_distr2 x y).
Apply sym_eqT;Apply (Ropp_distr2 y x). 
Generalize (minus_Rge y x l); Intro;
 Generalize (minus_Rge x y l0); Intro;
 Generalize (Rge_ge_eq x y H0 H); Intro;Rewrite H1;Trivial.
Save.

(*********)
Lemma R_dist_refl:(x,y:R)((R_dist x y)==R0<->x==y).
Intros;Unfold R_dist; Unfold Rabsolu;
 Case (case_Rabsolu (Rminus x y));Intro;Split;Intro.
Rewrite (Ropp_distr2 x y) in H;Apply sym_eqT;
 Apply (Rminus_eq y x H).
Rewrite (Ropp_distr2 x y);Generalize (sym_eqT R x y H);Intro;
 Apply (eq_Rminus y x H0).
Apply (Rminus_eq x y H).
Apply (eq_Rminus x y H). 
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
Unfold limit1_in;Unfold limit_in;Simpl;Intros;
 Elim (H (Rmult eps (Rinv (Rplus R1 R1))) (eps2_Rgt_R0 eps H1));
 Elim (H0 (Rmult eps (Rinv (Rplus R1 R1))) (eps2_Rgt_R0 eps H1));
 Clear H H0;Intros;Elim H;Elim H0;Clear H H0;Intros;
 Split with (Rmin x1 x);Split.
Elim (Rmin_Rgt x1 x R0);Intros a b;
 Apply (b (conj (Rgt x1 R0) (Rgt x R0) H H2));Clear a b.
Intros;Elim H4;Clear H4;Intros;Elim (Rmin_Rgt x1 x (R_dist x2 x0));
 Intros a b;Clear b;Unfold Rgt in a;Elim (a H5);Clear H5 a;Intros;
 Generalize (H0 x2 (conj (D x2) (Rlt (R_dist x2 x0) x1) H4 H5)); 
 Generalize (H3 x2 (conj (D x2) (Rlt (R_dist x2 x0) x) H4 H6));
 Clear H0 H3 H5 H6;Intros;
 Generalize (Rplus_lt (R_dist (f x2) l) 
                     (Rmult eps (Rinv (Rplus R1 R1))) 
                     (R_dist (g x2) l')
                     (Rmult eps (Rinv (Rplus R1 R1))) H3 H0);
 Clear H0 H3 H4;Intro;Rewrite (eps2 eps) in H0;Unfold R_dist;
 Unfold Rminus;Rewrite (Rplus_sym l l');Rewrite (Ropp_distr1 l' l);
 Rewrite <-(Rplus_assoc (Rplus (f x2) (g x2)) (Ropp l') (Ropp l));
 Rewrite (Rplus_assoc (f x2) (g x2) (Ropp l'));
 Rewrite (Rplus_sym (Rplus (f x2) (Rplus (g x2) (Ropp l'))) 
   (Ropp l));
 Rewrite <-(Rplus_assoc (Ropp l) (f x2) (Rplus (g x2) (Ropp l')));
 Rewrite (Rplus_sym (Ropp l) (f x2));
 Fold (Rminus (f x2) l);Fold (Rminus (g x2) l');Unfold R_dist in H0;
 Apply (Rle_lt_trans 
  (Rabsolu (Rplus (Rminus (f x2) l) (Rminus (g x2) l')))
  (Rplus (Rabsolu (Rminus (f x2) l)) (Rabsolu (Rminus (g x2) l')))
  eps 
  (Rabsolu_triang (Rminus (f x2) l) (Rminus (g x2) l')) H0).
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
Unfold limit1_in;Unfold limit_in;Simpl;Intros;
 Elim (Req_EM l R0);Elim (Req_EM l' R0);Intros.
(**)
Rewrite H2;Rewrite H3;Rewrite H2 in H0;Rewrite H3 in H;
 Rewrite (Rmult_Or R0);Unfold R_dist;Unfold R_dist in H H0;
 Elim (H eps H1);Clear H;Unfold 1 Rgt in H0;Elim (H0 R1 Rlt_R0_R1);
 Clear H0;Intros;Elim H;Elim H0;Clear H H0;Intros;
 Split with (Rmin x1 x);Split.
Elim (Rmin_Rgt x1 x R0);Intros a b;
 Apply (b (conj (Rgt x1 R0) (Rgt x R0) H H4));Clear a b.
Intros;Elim H6;Clear H6;Intros;Elim (Rmin_Rgt x1 x (R_dist x2 x0));
 Intros a b;Clear b;Unfold Rgt in a;Elim (a H7);Clear H7 a;Intros;
 Unfold R_dist in H7 H8;
 Generalize (H0 x2 (conj (D x2) 
          (Rlt (Rabsolu (Rminus x2 x0)) x1) H6 H7));
 Generalize (H5 x2 (conj (D x2) 
          (Rlt (Rabsolu (Rminus x2 x0)) x) H6 H8));Intros;
 Clear H0 H5 H7 H8;Rewrite (minus_R0 (g x2)) in H9;
 Rewrite (minus_R0 (f x2)) in H10;
 Rewrite (minus_R0 (Rmult (f x2) (g x2)));
 Generalize Rlt_R0_R1;Intro;Fold (Rgt R1 R0) in H0;
 Rewrite (Rabsolu_mult (f x2) (g x2));
 Rewrite <-(let (H1,H2)=(Rmult_ne eps) in H1);
 Generalize (Rabsolu_pos (g x2));Unfold Rle;Intro;Elim H5;Clear H5;
 Intro.
Apply (Rmult_lt (Rabsolu (f x2)) eps (Rabsolu (g x2)) R1 H5 H1 H10 H9).
Rewrite <-H5;Rewrite (Rmult_Or (Rabsolu (f x2))); 
 Rewrite (let (H1,H2)=(Rmult_ne eps) in H1);Unfold Rgt in H1;Assumption.
(**)
Rewrite H3;Rewrite H3 in H;Rewrite (Rmult_Ol l');
 Elim (H0 (Rmult eps (Rinv (Rplus R1 R1))) (eps2_Rgt_R0 eps H1));Intros;
 Elim H4;Clear H4;Intros;
 Generalize Rlt_R0_R1;Fold (Rgt R1 R0);Intro;Elim (H R1 H6);Intros;
 Elim H7;Clear H7;Intros;
 Cut (Rgt (Rmult eps (Rinv (Rmult (Rplus R1 R1) (Rabsolu l')))) R0).
Intro;Elim (H (Rmult eps (Rinv (Rmult (Rplus R1 R1) (Rabsolu l')))) H9);
 Intros;Elim H10;Clear H10;Intros;Split with (Rmin (Rmin x x1) x2);
 Split.
Elim (Rmin_Rgt (Rmin x x1) x2 R0);Intros;Elim (Rmin_Rgt x x1 R0);Intros;
 Generalize (H15 (conj (Rgt x R0) (Rgt x1 R0) H4 H7));Clear H14 H15;
 Intro;Clear H12;
 Apply (H13 (conj (Rgt (Rmin x x1) R0) (Rgt x2 R0) H14 H10)).
Intros;Elim H12;Clear H12;Intros;
 Elim (Rmin_Rgt (Rmin x x1) x2 (R_dist x3 x0));Intros;Clear H15;
 Unfold 1 Rgt in H14;Elim (H14 H13);Clear H14;Intros;Unfold Rgt in H15;
 Clear H13;Elim (Rmin_Rgt x x1 (R_dist x3 x0));Intros;
 Elim (H13 H14);Clear H14 H13 H16;Intros;Unfold Rgt in H13 H14;
 Generalize (H5 x3 (conj (D x3) (Rlt (R_dist x3 x0) x) H12 H13));
 Generalize (H8 x3 (conj (D x3) (Rlt (R_dist x3 x0) x1) H12 H14));
 Generalize (H11 x3 (conj (D x3) (Rlt (R_dist x3 x0) x2) H12 H15));
 Clear H5 H8 H11 H15 H13 H14 H12;Intros;Unfold R_dist in H5 H8 H11;
 Unfold R_dist;Rewrite (minus_R0 (Rmult (f x3) (g x3)));
 Rewrite (minus_R0 (f x3)) in H5;Rewrite (minus_R0 (f x3)) in H8;
 Rewrite <-(let (H1,H2)=(Rplus_ne (Rmult (f x3) (g x3))) in H1);
 Rewrite <-(Rplus_Ropp_l (Rmult (f x3) l'));Rewrite (Rmult_sym (f x3) l');
 Rewrite <-(Ropp_mul1 l' (f x3));
 Rewrite (Rmult_sym (Ropp l') (f x3));
 Rewrite <-(Rplus_assoc (Rmult (f x3) (g x3)) 
                     (Rmult (f x3) (Ropp l')) (Rmult l' (f x3)));
 Rewrite <-(Rmult_Rplus_distr (f x3) (g x3) (Ropp l'));Fold (Rminus (g x3) l');
 Generalize (Rabsolu_triang (Rmult (f x3) (Rminus (g x3) l'))
                            (Rmult l' (f x3)));Intro;
 Apply (Rle_lt_trans 
   (Rabsolu (Rplus (Rmult (f x3) (Rminus (g x3) l')) (Rmult l' (f x3))))
   (Rplus (Rabsolu (Rmult (f x3) (Rminus (g x3) l')))
         (Rabsolu (Rmult l' (f x3)))) eps H12);Clear H12;
 Rewrite (Rabsolu_mult (f x3) (Rminus (g x3) l'));
 Rewrite (Rabsolu_mult l' (f x3));
 Elim (Req_EM (f x3) R0);Intros.
Rewrite H12;Rewrite Rabsolu_R0;
 Rewrite (Rmult_Ol (Rabsolu (Rminus (g x3) l')));
 Rewrite (Rmult_Or (Rabsolu l'));
 Rewrite (let (H1,H2)=(Rplus_ne R0) in H1); 
 Unfold Rgt in H1;Assumption.
Generalize (Rabsolu_pos_lt (f x3) H12);Intro;
 Fold (Rgt (Rabsolu (f x3)) R0) in H13;
 Generalize (Rmult_lt (Rabsolu (Rminus (g x3) l')) 
                      (Rmult eps (Rinv (Rplus R1 R1)))
                      (Rabsolu (f x3)) R1 H13 (eps2_Rgt_R0 eps H1) 
         H11 H8);Intro;
 Generalize (Rlt_monotony (Rabsolu l') (Rabsolu (f x3))
   (Rmult eps (Rinv (Rmult (Rplus R1 R1) (Rabsolu l'))))  
      (Rabsolu_pos_lt l' H2) H5);Clear H5 H8 H11 H12 H13;Intro;
 Rewrite (Rmult_sym (Rabsolu (Rminus (g x3) l')) (Rabsolu (f x3))) 
  in H14;Generalize (Rplus_lt 
     (Rmult (Rabsolu (f x3)) (Rabsolu (Rminus (g x3) l')))
     (Rmult (Rmult eps (Rinv (Rplus R1 R1))) R1)
     (Rmult (Rabsolu l') (Rabsolu (f x3)))
     (Rmult (Rabsolu l')
        (Rmult eps (Rinv (Rmult (Rplus R1 R1) (Rabsolu l'))))) H14 H5);
 Clear H5 H14;Intro;
 Cut eps==(Rplus (Rmult (Rmult eps (Rinv (Rplus R1 R1))) R1)
             (Rmult (Rabsolu l')
               (Rmult eps (Rinv (Rmult (Rplus R1 R1) (Rabsolu l')))))).
Intro;Rewrite <-H8 in H5;Assumption.
Rewrite (let (H1,H2)=
  (Rmult_ne (Rmult eps (Rinv (Rplus R1 R1)))) in H1);
 Cut ~(Rabsolu l')==R0. 
Intro;Rewrite (Rinv_Rmult (Rplus R1 R1) (Rabsolu l'));Auto.
Rewrite (Rmult_sym (Rabsolu l') 
  (Rmult eps (Rmult (Rinv (Rplus R1 R1)) (Rinv (Rabsolu l')))));
 Rewrite (Rmult_assoc eps 
    (Rmult (Rinv (Rplus R1 R1)) (Rinv (Rabsolu l')))
    (Rabsolu l'));
 Rewrite (Rmult_assoc (Rinv (Rplus R1 R1)) (Rinv (Rabsolu l'))
   (Rabsolu l'));
 Rewrite (Rinv_l (Rabsolu l') H8);
 Rewrite (let (H1,H2)=
  (Rmult_ne (Rinv (Rplus R1 R1))) in H1);
 Apply sym_eqT;Apply eps2.
Apply (imp_not_Req (Rplus R1 R1) R0);Right;Unfold Rgt;Generalize Rlt_R0_R1;Intro;
 Generalize (Rlt_compatibility R1 R0 R1 H11);Intro;
 Rewrite (let (H1,H2)=(Rplus_ne R1) in H1) in H12;
 Apply (Rlt_trans R0 R1 (Rplus R1 R1) H11 H12).
Generalize (Rabsolu_pos_lt l' H2);Intro;
 Apply (imp_not_Req (Rabsolu l') R0);Auto.
Unfold Rgt;Unfold Rgt in H1;
 Rewrite <-(Rmult_Or (Rinv (Rmult (Rplus R1 R1) (Rabsolu l'))));
 Rewrite (Rmult_sym eps (Rinv (Rmult (Rplus R1 R1) (Rabsolu l'))));
 Apply (Rlt_monotony (Rinv (Rmult (Rplus R1 R1) (Rabsolu l'))) R0 eps);
 Auto.
Apply (Rlt_Rinv (Rmult (Rplus R1 R1) (Rabsolu l')));
 Generalize (Rabsolu_pos_lt l' H2);
 Clear H H0 H3 H4 H5 H7 H8 f g D l x0 x x1;Intro;
 Rewrite <-(Rmult_Or (Rplus R1 R1)); 
 Apply (Rlt_monotony (Rplus R1 R1) R0 (Rabsolu l'));Auto.
Unfold Rgt in H6;Generalize (Rlt_compatibility R1 R0 R1 H6);Intro;
 Rewrite (let (H1,H2)=(Rplus_ne R1) in H1) in H0;
 Apply (Rlt_trans R0 R1 (Rplus R1 R1) H6 H0).
(**)
Rewrite H2;Rewrite H2 in H0;Rewrite (Rmult_Or l);
 Elim (H (Rmult eps (Rinv (Rplus R1 R1))) (eps2_Rgt_R0 eps H1));Intros;
 Elim H4;Clear H4;Intros;
 Generalize Rlt_R0_R1;Fold (Rgt R1 R0);Intro;Elim (H0 R1 H6);Intros;
 Elim H7;Clear H7;Intros;
 Cut (Rgt (Rmult eps (Rinv (Rmult (Rplus R1 R1) (Rabsolu l)))) R0).
Intro;Elim (H0 (Rmult eps (Rinv (Rmult (Rplus R1 R1) (Rabsolu l)))) H9);
 Intros;Elim H10;Clear H10;Intros;Split with (Rmin (Rmin x x1) x2);
 Split.
Elim (Rmin_Rgt (Rmin x x1) x2 R0);Intros;Elim (Rmin_Rgt x x1 R0);Intros;
 Generalize (H15 (conj (Rgt x R0) (Rgt x1 R0) H4 H7));Clear H14 H15;
 Intro;Clear H12;
 Apply (H13 (conj (Rgt (Rmin x x1) R0) (Rgt x2 R0) H14 H10)).
Intros;Elim H12;Clear H12;Intros;
 Elim (Rmin_Rgt (Rmin x x1) x2 (R_dist x3 x0));Intros;Clear H15;
 Unfold 1 Rgt in H14;Elim (H14 H13);Clear H14;Intros;Unfold Rgt in H15;
 Clear H13;Elim (Rmin_Rgt x x1 (R_dist x3 x0));Intros;
 Elim (H13 H14);Clear H14 H13 H16;Intros;Unfold Rgt in H13 H14;
 Generalize (H5 x3 (conj (D x3) (Rlt (R_dist x3 x0) x) H12 H13));
 Generalize (H8 x3 (conj (D x3) (Rlt (R_dist x3 x0) x1) H12 H14));
 Generalize (H11 x3 (conj (D x3) (Rlt (R_dist x3 x0) x2) H12 H15));
 Clear H5 H8 H11 H15 H13 H14 H12;Intros;Unfold R_dist in H5 H8 H11;
 Unfold R_dist;Rewrite (minus_R0 (Rmult (f x3) (g x3)));
 Rewrite (minus_R0 (g x3)) in H8;Rewrite (minus_R0 (g x3)) in H5;
 Rewrite <-(let (H1,H2)=(Rplus_ne (Rmult (f x3) (g x3))) in H1);
 Rewrite <-(Rplus_Ropp_l (Rmult (g x3) l));Rewrite (Rmult_sym (g x3) l);
 Rewrite <-(Ropp_mul1 l (g x3));
 Rewrite (Rmult_sym (Ropp l) (g x3));
 Rewrite <-(Rplus_assoc (Rmult (f x3) (g x3)) 
                     (Rmult (g x3) (Ropp l)) (Rmult l (g x3)));
 Rewrite (Rmult_sym (f x3) (g x3));
 Rewrite <-(Rmult_Rplus_distr (g x3) (f x3) (Ropp l));Fold (Rminus (f x3) l);
 Generalize (Rabsolu_triang (Rmult (g x3) (Rminus (f x3) l))
                            (Rmult l (g x3)));Intro;
 Apply (Rle_lt_trans 
   (Rabsolu (Rplus (Rmult (g x3) (Rminus (f x3) l)) (Rmult l (g x3))))
   (Rplus (Rabsolu (Rmult (g x3) (Rminus (f x3) l)))
         (Rabsolu (Rmult l (g x3)))) eps H12);Clear H12;
 Rewrite (Rabsolu_mult (g x3) (Rminus (f x3) l));
 Rewrite (Rabsolu_mult l (g x3));
 Elim (Req_EM (g x3) R0);Intros.
Rewrite H12;Rewrite Rabsolu_R0;
 Rewrite (Rmult_Ol (Rabsolu (Rminus (f x3) l)));
 Rewrite (Rmult_Or (Rabsolu l));
 Rewrite (let (H1,H2)=(Rplus_ne R0) in H1); 
 Unfold Rgt in H1;Assumption.
Generalize (Rabsolu_pos_lt (g x3) H12);Intro;
 Fold (Rgt (Rabsolu (g x3)) R0) in H13;
 Generalize (Rmult_lt (Rabsolu (Rminus (f x3) l)) 
                      (Rmult eps (Rinv (Rplus R1 R1)))
                      (Rabsolu (g x3)) R1 H13 (eps2_Rgt_R0 eps H1) 
         H11 H8);Intro;
 Generalize (Rlt_monotony (Rabsolu l) (Rabsolu (g x3))
   (Rmult eps (Rinv (Rmult (Rplus R1 R1) (Rabsolu l))))  
      (Rabsolu_pos_lt l H3) H5);Clear H5 H8 H11 H12 H13;Intro;
 Rewrite (Rmult_sym (Rabsolu (Rminus (f x3) l)) (Rabsolu (g x3))) 
  in H14;Generalize (Rplus_lt 
     (Rmult (Rabsolu (g x3)) (Rabsolu (Rminus (f x3) l)))
     (Rmult (Rmult eps (Rinv (Rplus R1 R1))) R1)
     (Rmult (Rabsolu l) (Rabsolu (g x3)))
     (Rmult (Rabsolu l)
        (Rmult eps (Rinv (Rmult (Rplus R1 R1) (Rabsolu l))))) H14 H5);
 Clear H5 H14;Intro;
 Cut eps==(Rplus (Rmult (Rmult eps (Rinv (Rplus R1 R1))) R1)
             (Rmult (Rabsolu l)
               (Rmult eps (Rinv (Rmult (Rplus R1 R1) (Rabsolu l)))))).
Intro;Rewrite <-H8 in H5;Assumption.
Rewrite (let (H1,H2)=
  (Rmult_ne (Rmult eps (Rinv (Rplus R1 R1)))) in H1);
 Cut ~(Rabsolu l)==R0. 
Intro;Rewrite (Rinv_Rmult (Rplus R1 R1) (Rabsolu l));Auto.
Rewrite (Rmult_sym (Rabsolu l) 
  (Rmult eps (Rmult (Rinv (Rplus R1 R1)) (Rinv (Rabsolu l)))));
 Rewrite (Rmult_assoc eps 
    (Rmult (Rinv (Rplus R1 R1)) (Rinv (Rabsolu l)))
    (Rabsolu l));
 Rewrite (Rmult_assoc (Rinv (Rplus R1 R1)) (Rinv (Rabsolu l))
   (Rabsolu l));
 Rewrite (Rinv_l (Rabsolu l) H8);
 Rewrite (let (H1,H2)=
  (Rmult_ne (Rinv (Rplus R1 R1))) in H1);
 Apply sym_eqT;Apply eps2.
Apply (imp_not_Req (Rplus R1 R1) R0);Right;Unfold Rgt;Generalize Rlt_R0_R1;Intro;
 Generalize (Rlt_compatibility R1 R0 R1 H11);Intro;
 Rewrite (let (H1,H2)=(Rplus_ne R1) in H1) in H12;
 Apply (Rlt_trans R0 R1 (Rplus R1 R1) H11 H12).
Generalize (Rabsolu_pos_lt l H3);Intro;
 Apply (imp_not_Req (Rabsolu l) R0);Auto.
Unfold Rgt;Unfold Rgt in H1;
 Rewrite <-(Rmult_Or (Rinv (Rmult (Rplus R1 R1) (Rabsolu l))));
 Rewrite (Rmult_sym eps (Rinv (Rmult (Rplus R1 R1) (Rabsolu l))));
 Apply (Rlt_monotony (Rinv (Rmult (Rplus R1 R1) (Rabsolu l))) R0 eps);
 Auto.
Apply (Rlt_Rinv (Rmult (Rplus R1 R1) (Rabsolu l)));
 Generalize (Rabsolu_pos_lt l H3);
 Clear H H0 H2 H4 H5 H7 H8 f g D l' x0 x x1;Intro;
 Rewrite <-(Rmult_Or (Rplus R1 R1)); 
 Apply (Rlt_monotony (Rplus R1 R1) R0 (Rabsolu l));Auto.
Unfold Rgt in H6;Generalize (Rlt_compatibility R1 R0 R1 H6);Intro;
 Rewrite (let (H1,H2)=(Rplus_ne R1) in H1) in H0;
 Apply (Rlt_trans R0 R1 (Rplus R1 R1) H6 H0).
(**)
Cut ~(Rplus (Rplus R1 R1) (Rplus R1 R1))==R0.
Cut ~(Rabsolu l)==R0.
Cut ~(Rabsolu l')==R0.
Intros tl' tl add4;
 Elim (H (Rmult eps (Rinv (Rplus R1 R1))) (eps2_Rgt_R0 eps H1));
 Intros;Elim H4;Clear H4;Intros;
 Generalize Rlt_R0_R1;Fold (Rgt R1 R0);Intro;Elim (H0 R1 H6);Intros;
 Elim H7;Clear H7;Intros;
 Cut (Rgt (Rmult eps 
 (Rinv (Rmult (Rplus (Rplus R1 R1) (Rplus R1 R1)) (Rabsolu l)))) R0).
Cut (Rgt (Rmult eps 
 (Rinv (Rmult (Rplus (Rplus R1 R1) (Rplus R1 R1)) (Rabsolu l')))) R0).
Intros;Elim (H0 (Rmult eps 
   (Rinv (Rmult (Rplus (Rplus R1 R1) (Rplus R1 R1)) (Rabsolu l)))) H10);
 Intros;Elim H11;Clear H11;Intros;
 Elim (H (Rmult eps 
   (Rinv (Rmult (Rplus (Rplus R1 R1) (Rplus R1 R1)) (Rabsolu l')))) H9);
 Intros;Elim H13;Clear H13;Intros;
 Split with (Rmin (Rmin x x1) (Rmin x2 x3));Split.
Elim (Rmin_Rgt (Rmin x x1) (Rmin x2 x3) R0);Intros;
 Elim (Rmin_Rgt x x1 R0);Elim (Rmin_Rgt x2 x3 R0);Intros;
 Apply (H16 (conj (Rgt (Rmin x x1) R0) (Rgt (Rmin x2 x3) R0) 
  (H20 (conj (Rgt x R0) (Rgt x1 R0) H4 H7)) 
  (H18 (conj (Rgt x2 R0) (Rgt x3 R0) H11 H13)))).
Intros;Elim H15;Clear H15;Intros;
 Elim (Rmin_Rgt (Rmin x x1) (Rmin x2 x3) (R_dist x4 x0));Intros;
 Clear H18;Unfold 1 Rgt in H17;Elim (H17 H16);Clear H17 H16;Intros;
 Elim (Rmin_Rgt x x1 (R_dist x4 x0));
 Elim (Rmin_Rgt x2 x3 (R_dist x4 x0));Intros;
 Unfold 1 Rgt in H17;Unfold 1 Rgt in H20;Elim (H18 H17);Elim (H20 H16);
 Clear H16 H17 H18 H19 H20 H21;Intros;Unfold Rgt in H16 H17 H18 H19;
 Generalize (H5 x4 (conj (D x4) (Rlt (R_dist x4 x0) x) H15 H16));
 Generalize (H8 x4 (conj (D x4) (Rlt (R_dist x4 x0) x1) H15 H17));
 Generalize (H12 x4 (conj (D x4) (Rlt (R_dist x4 x0) x2) H15 H18));
 Generalize (H14 x4 (conj (D x4) (Rlt (R_dist x4 x0) x3) H15 H19));
 Clear H H0 H5 H8 H12 H14 H16 H17 H18 H19;Intros;
 Unfold R_dist in H H0 H5 H8;Unfold R_dist; 
 Rewrite <-(let (H1,H2)=(Rplus_ne (Rmult (f x4) (g x4))) in H1);
 Rewrite <-(Rplus_Ropp_l (Rmult (g x4) l));Rewrite (Rmult_sym (g x4) l);
 Rewrite <-(Ropp_mul1 l (g x4));
 Rewrite (Rmult_sym (Ropp l) (g x4));
 Rewrite <-(Rplus_assoc (Rmult (f x4) (g x4)) 
                     (Rmult (g x4) (Ropp l)) (Rmult l (g x4)));
 Rewrite (Rmult_sym (f x4) (g x4));
 Rewrite <-(Rmult_Rplus_distr (g x4) (f x4) (Ropp l));Fold (Rminus (f x4) l);
 Unfold 1 Rminus;Rewrite (Rmult_sym l l');Rewrite <-(Ropp_mul1 l' l);
 Rewrite (Rmult_sym (Ropp l') l);
 Rewrite (Rplus_assoc (Rmult (g x4) (Rminus (f x4) l)) 
                     (Rmult l (g x4)) (Rmult l (Ropp l')));
 Rewrite <-(Rmult_Rplus_distr l (g x4) (Ropp l'));
 Fold (Rminus (g x4) l');
 Generalize (Rabsolu_triang (Rmult (g x4) (Rminus (f x4) l))
                            (Rmult l (Rminus (g x4) l')));Intro;
 Apply (Rle_lt_trans 
   (Rabsolu (Rplus (Rmult (g x4) (Rminus (f x4) l)) 
                  (Rmult l (Rminus (g x4) l'))))
   (Rplus (Rabsolu (Rmult (g x4) (Rminus (f x4) l)))
         (Rabsolu (Rmult l (Rminus (g x4) l')))) eps H12);Clear H12;
 Generalize (Rlt_monotony (Rabsolu l) (Rabsolu (Rminus (g x4) l')) 
                      (Rmult eps
           (Rinv (Rmult (Rplus (Rplus R1 R1) (Rplus R1 R1)) (Rabsolu l))))
                      (Rabsolu_pos_lt l H3) H0);Intro;
 Generalize (Rlt_monotony (Rabsolu l') (Rabsolu (Rminus (f x4) l)) 
                      (Rmult eps
           (Rinv (Rmult (Rplus (Rplus R1 R1) (Rplus R1 R1)) (Rabsolu l'))))
                      (Rabsolu_pos_lt l' H2) H);Intro;
 Elim (Req_EM (f x4) l);Intros.
Rewrite H16;Rewrite (eq_Rminus l l (refl_eqT R l));
 Rewrite (Rmult_Or (g x4));Rewrite Rabsolu_R0;
 Rewrite (let (H1,H2)=(Rplus_ne (Rabsolu (Rmult l (Rminus (g x4) l')))) 
   in H2);Rewrite (Rabsolu_mult l (Rminus (g x4) l'));
 Apply (Rlt_trans (Rmult (Rabsolu l) (Rabsolu (Rminus (g x4) l')))
     (Rmult (Rabsolu l)
            (Rmult eps
              (Rinv
                (Rmult (Rplus (Rplus R1 R1) (Rplus R1 R1)) (Rabsolu l)))))
     eps H12); 
 Rewrite (Rmult_sym eps 
   (Rinv (Rmult (Rplus (Rplus R1 R1) (Rplus R1 R1)) (Rabsolu l))));
 Rewrite <-(Rmult_assoc (Rabsolu l) 
  (Rinv (Rmult (Rplus (Rplus R1 R1) (Rplus R1 R1)) (Rabsolu l))) eps);
 Rewrite (Rinv_Rmult (Rplus (Rplus R1 R1) (Rplus R1 R1)) (Rabsolu l) add4 
    tl);
 Rewrite (Rmult_sym (Rinv (Rplus (Rplus R1 R1) (Rplus R1 R1)))
                     (Rinv (Rabsolu l))); 
 Rewrite <-(Rmult_assoc (Rabsolu l) (Rinv (Rabsolu l)) 
                      (Rinv (Rplus (Rplus R1 R1) (Rplus R1 R1))));
 Rewrite (Rinv_r (Rabsolu l) tl);
 Rewrite (let (H1,H2)=(Rmult_ne (Rinv (Rplus (Rplus R1 R1) (Rplus R1 R1))))
  in H2);Rewrite (Rmult_sym (Rinv (Rplus (Rplus R1 R1) (Rplus R1 R1)))
           eps);Apply (Rlt_eps4_eps eps H1).
Generalize Rlt_R0_R1;Fold (Rgt R1 R0);Intro;
 Cut (Rgt (Rabsolu (Rminus (f x4) l)) R0).
Intro;
 Generalize (Rmult_lt (Rabsolu (Rminus (g x4) l')) R1 
                     (Rabsolu (Rminus (f x4) l)) 
                     (Rmult eps (Rinv (Rplus R1 R1)))
                      H18 H17 H5 H8);Intro;
 Rewrite (let (H1,H2)=(Rmult_ne (Rmult eps (Rinv (Rplus R1 R1)))) in H2)
  in H19;Generalize (Rplus_lt (Rmult (Rabsolu (Rminus (g x4) l'))
            (Rabsolu (Rminus (f x4) l)))
                             (Rmult eps (Rinv (Rplus R1 R1)))
                      (Rmult (Rabsolu l') (Rabsolu (Rminus (f x4) l)))
                      (Rmult (Rabsolu l')
            (Rmult eps (Rinv
                (Rmult (Rplus (Rplus R1 R1) (Rplus R1 R1)) (Rabsolu l')))))
              H19 H14);Intro;
 Generalize (Rplus_lt (Rmult (Rabsolu l) (Rabsolu (Rminus (g x4) l')))
                     (Rmult (Rabsolu l)
            (Rmult eps
              (Rinv
                (Rmult (Rplus (Rplus R1 R1) (Rplus R1 R1)) (Rabsolu l)))))
             (Rplus
            (Rmult (Rabsolu (Rminus (g x4) l'))
              (Rabsolu (Rminus (f x4) l)))
            (Rmult (Rabsolu l') (Rabsolu (Rminus (f x4) l))))
            (Rplus (Rmult eps (Rinv (Rplus R1 R1)))
            (Rmult (Rabsolu l')
              (Rmult eps
                (Rinv
              (Rmult (Rplus (Rplus R1 R1) (Rplus R1 R1)) (Rabsolu l'))))))
              H12 H20);
 Clear H5 H8 H12 H14 H19 H20 H H0 H9 H10;Replace (Rplus
            (Rmult (Rabsolu l)
              (Rmult eps
                (Rinv
                  (Rmult (Rplus (Rplus R1 R1) (Rplus R1 R1)) (Rabsolu l)))))
            (Rplus (Rmult eps (Rinv (Rplus R1 R1)))
              (Rmult (Rabsolu l')
                (Rmult eps
                  (Rinv
                    (Rmult (Rplus (Rplus R1 R1) (Rplus R1 R1))
                      (Rabsolu l'))))))) with eps.
Intro;Rewrite (Rplus_sym (Rabsolu (Rmult (g x4) (Rminus (f x4) l)))
           (Rabsolu (Rmult l (Rminus (g x4) l'))));
 Pattern 2 (g x4);
 Rewrite <-(let (H1,H2)=(Rplus_ne (g x4)) in H1);
 Rewrite <-(Rplus_Ropp_r l');Rewrite <-(Rplus_assoc (g x4) l' (Ropp l')); 
 Rewrite (Rmult_sym (Rplus (Rplus (g x4) l') (Ropp l')) 
                      (Rminus (f x4) l));
 Rewrite (Rabsolu_mult (Rminus (f x4) l)
                      (Rplus (Rplus (g x4) l') (Ropp l')));
 Rewrite (Rmult_sym (Rabsolu (Rminus (g x4) l'))
                      (Rabsolu (Rminus (f x4) l))) in H;
 Rewrite (Rmult_sym (Rabsolu l') 
                      (Rabsolu (Rminus (f x4) l))) in H;
 Rewrite <-(Rmult_Rplus_distr (Rabsolu (Rminus (f x4) l))
                  (Rabsolu (Rminus (g x4) l'))
                  (Rabsolu l')) in H;
 Rewrite <-(Rabsolu_mult l (Rminus (g x4) l')) in H;
 Rewrite (Rplus_assoc (g x4) l' (Ropp l'));
 Rewrite (Rplus_sym l' (Ropp l'));
 Rewrite <-(Rplus_assoc (g x4) (Ropp l') l');
 Fold (Rminus (g x4) l');
 Generalize (Rabsolu_triang (Rminus (g x4) l') l');Intro;
 Unfold Rle in H0;Elim H0;Clear H0;Intro.
Unfold Rgt in H18.
 Generalize (Rlt_monotony (Rabsolu (Rminus (f x4) l)) 
        (Rabsolu (Rplus (Rminus (g x4) l') l'))
        (Rplus (Rabsolu (Rminus (g x4) l')) (Rabsolu l')) 
        H18 H0);Intro;
 Generalize (Rlt_compatibility (Rabsolu (Rmult l (Rminus (g x4) l')))
        (Rmult (Rabsolu (Rminus (f x4) l))
           (Rabsolu (Rplus (Rminus (g x4) l') l')))
        (Rmult (Rabsolu (Rminus (f x4) l))
           (Rplus (Rabsolu (Rminus (g x4) l')) (Rabsolu l')))
        H5);Clear H0 H5;Intro;
 Apply (Rlt_trans (Rplus (Rabsolu (Rmult l (Rminus (g x4) l')))
           (Rmult (Rabsolu (Rminus (f x4) l))
             (Rabsolu (Rplus (Rminus (g x4) l') l'))))
                   (Rplus (Rabsolu (Rmult l (Rminus (g x4) l')))
           (Rmult (Rabsolu (Rminus (f x4) l))
             (Rplus (Rabsolu (Rminus (g x4) l')) (Rabsolu l'))))
                   eps H0 H).
Rewrite H0;Assumption. 
Rewrite (Rinv_Rmult (Rplus (Rplus R1 R1) (Rplus R1 R1))
                            (Rabsolu l) add4 tl);
 Rewrite (Rinv_Rmult (Rplus (Rplus R1 R1) (Rplus R1 R1))
                            (Rabsolu l') add4 tl');
 Rewrite (Rmult_sym eps (Rmult (Rinv (Rplus (Rplus R1 R1) (Rplus R1 R1)))
              (Rinv (Rabsolu l))));
 Rewrite (Rmult_sym eps (Rmult (Rinv (Rplus (Rplus R1 R1) (Rplus R1 R1)))
              (Rinv (Rabsolu l'))));
 Rewrite (Rmult_sym (Rinv (Rplus (Rplus R1 R1) (Rplus R1 R1))) 
                      (Rinv (Rabsolu l)));
 Rewrite (Rmult_sym (Rinv (Rplus (Rplus R1 R1) (Rplus R1 R1))) 
                      (Rinv (Rabsolu l')));
 Rewrite (Rmult_assoc (Rinv (Rabsolu l)) 
        (Rinv (Rplus (Rplus R1 R1) (Rplus R1 R1))) eps);
 Rewrite (Rmult_assoc (Rinv (Rabsolu l')) 
        (Rinv (Rplus (Rplus R1 R1) (Rplus R1 R1))) eps);
 Rewrite <-(Rmult_assoc (Rabsolu l) (Rinv (Rabsolu l))
        (Rmult (Rinv (Rplus (Rplus R1 R1) (Rplus R1 R1))) eps));
 Rewrite <-(Rmult_assoc (Rabsolu l') (Rinv (Rabsolu l'))
        (Rmult (Rinv (Rplus (Rplus R1 R1) (Rplus R1 R1))) eps));
 Rewrite (Rinv_r (Rabsolu l) tl);Rewrite (Rinv_r (Rabsolu l') tl');
 Rewrite (let (H1,H2)=(Rmult_ne 
      (Rmult (Rinv (Rplus (Rplus R1 R1) (Rplus R1 R1))) eps)) in H2);
 Rewrite (Rmult_sym (Rinv (Rplus (Rplus R1 R1) (Rplus R1 R1))) eps);
 Rewrite (Rplus_sym (Rmult eps (Rinv (Rplus R1 R1)))
                  (Rmult eps (Rinv (Rplus (Rplus R1 R1) (Rplus R1 R1)))));
 Rewrite <- (Rplus_assoc 
     (Rmult eps (Rinv (Rplus (Rplus R1 R1) (Rplus R1 R1))))
     (Rmult eps (Rinv (Rplus (Rplus R1 R1) (Rplus R1 R1))))
     (Rmult eps (Rinv (Rplus R1 R1))));
 Rewrite eps4;Rewrite eps2;Trivial.
Unfold Rgt;Apply (Rabsolu_pos_lt (Rminus (f x4) l));Red;Intro;Elim H16;
 Apply (Rminus_eq (f x4) l H18).
Apply (Rmult_gt eps 
  (Rinv (Rmult (Rplus (Rplus R1 R1) (Rplus R1 R1)) (Rabsolu l'))) H1);
 Rewrite (Rinv_Rmult (Rplus (Rplus R1 R1) (Rplus R1 R1)) (Rabsolu l') 
           add4 tl'); 
 Apply (Rmult_gt (Rinv (Rplus (Rplus R1 R1) (Rplus R1 R1))) 
  (Rinv (Rabsolu l'))).
Unfold Rgt;Apply (Rlt_Rinv (Rplus (Rplus R1 R1) (Rplus R1 R1))).
Generalize Rlt_R0_R1;Intro;
 Generalize (Rlt_compatibility R1 R0 R1 H9);Intro;
 Rewrite (let (H1,H2)=(Rplus_ne R1) in H1) in H10;
 Generalize (Rlt_trans R0 R1 (Rplus R1 R1) H9 H10);Intro;
 Clear H9 H10;
 Generalize (Rlt_compatibility (Rplus R1 R1) R0 (Rplus R1 R1) H11);Intro;
 Rewrite (let (H1,H2)=(Rplus_ne (Rplus R1 R1)) in H1) in H9;
 Apply (Rlt_trans R0 (Rplus R1 R1) (Rplus (Rplus R1 R1) (Rplus R1 R1))
    H11 H9).
Unfold Rgt;Apply (Rlt_Rinv (Rabsolu l') (Rabsolu_pos_lt l' H2)).
Apply (Rmult_gt eps 
  (Rinv (Rmult (Rplus (Rplus R1 R1) (Rplus R1 R1)) (Rabsolu l))) H1);
 Rewrite (Rinv_Rmult (Rplus (Rplus R1 R1) (Rplus R1 R1)) (Rabsolu l) 
           add4 tl); 
 Apply (Rmult_gt (Rinv (Rplus (Rplus R1 R1) (Rplus R1 R1))) 
  (Rinv (Rabsolu l))).
Unfold Rgt;Apply (Rlt_Rinv (Rplus (Rplus R1 R1) (Rplus R1 R1))).
Generalize Rlt_R0_R1;Intro;
 Generalize (Rlt_compatibility R1 R0 R1 H9);Intro;
 Rewrite (let (H1,H2)=(Rplus_ne R1) in H1) in H10;
 Generalize (Rlt_trans R0 R1 (Rplus R1 R1) H9 H10);Intro;
 Clear H9 H10;
 Generalize (Rlt_compatibility (Rplus R1 R1) R0 (Rplus R1 R1) H11);Intro;
 Rewrite (let (H1,H2)=(Rplus_ne (Rplus R1 R1)) in H1) in H9;
 Apply (Rlt_trans R0 (Rplus R1 R1) (Rplus (Rplus R1 R1) (Rplus R1 R1))
    H11 H9).
Unfold Rgt;Apply (Rlt_Rinv (Rabsolu l) (Rabsolu_pos_lt l H3)).
Generalize (Rabsolu_pos_lt l' H2);Intro;
 Apply (imp_not_Req (Rabsolu l') R0);Auto.
Generalize (Rabsolu_pos_lt l H3);Intro;
 Apply (imp_not_Req (Rabsolu l) R0);Auto.
Apply (imp_not_Req (Rplus (Rplus R1 R1) (Rplus R1 R1)) R0);Right;Unfold Rgt;
 Generalize Rlt_R0_R1;Intro;
 Generalize (Rlt_compatibility R1 R0 R1 H4);Intro;
 Rewrite (let (H1,H2)=(Rplus_ne R1) in H1) in H5;
 Generalize (Rlt_trans R0 R1 (Rplus R1 R1) H4 H5);Intro;
 Clear H4 H5;
 Generalize (Rlt_compatibility (Rplus R1 R1) R0 (Rplus R1 R1) H6);Intro;
 Rewrite (let (H1,H2)=(Rplus_ne (Rplus R1 R1)) in H1) in H4;
 Apply (Rlt_trans R0 (Rplus R1 R1) (Rplus (Rplus R1 R1) (Rplus R1 R1))
    H6 H4).
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
