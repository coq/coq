
(* $Id$ *)

(*********************************************************)
(*           Complements for the real numbers            *)
(*                                                       *)
(*********************************************************)

Require Export R_Ifp.

(*******************************)
(*           Rmin              *)
(*******************************)

(*********)
Definition Rmin :R->R->R:=[x,y:R]
  Cases (total_order_Rle x y) of 
    (leftT _)  => x
  | (rightT _) => y
  end.

(*********)
Lemma Rmin_Rgt:(r1,r2,r:R)(Rgt (Rmin r1 r2) r)<->
    ((Rgt r1 r)/\(Rgt r2 r)).
Intros;Split.
Unfold Rmin;Case (total_order_Rle r1 r2);Intros.
Split;Auto.
Unfold Rgt in H;Unfold Rgt;Apply (Rlt_le_trans r r1 r2 H r0).
Split;Auto.
Generalize (not_Rle r1 r2 n);Intro;Clear n;
 Apply (Rgt_trans r1 r2 r H0 H).
Intro;Elim H;Intros;Clear H;Unfold Rmin;Case (total_order_Rle r1 r2);
 Intros;Auto.
Save.

(*******************************)
(*           Rmax              *)
(*******************************)

(*********)
Definition Rmax :R->R->R:=[x,y:R]
  Cases (total_order_Rle x y) of 
    (leftT _)  => y
  | (rightT _) => x
  end.

(*********)
Lemma Rmax_Rle:(r1,r2,r:R)(Rle r (Rmax r1 r2))<->
    ((Rle r r1)\/(Rle r r2)).
Intros;Split.
Unfold Rmax;Case (total_order_Rle r1 r2);Intros;Auto.
Intro;Unfold Rmax;Case (total_order_Rle r1 r2);Elim H;Clear H;Intros;Auto.
Apply (Rle_trans r r1 r2);Auto.
Generalize (not_Rle r1 r2 n);Clear n;Intro;Unfold Rgt in H0;
 Apply (Rlt_le r r1 (Rle_lt_trans r r2 r1 H H0)).
Save.

(*******************************)
(*           Rabsolu           *)
(*******************************)

(*********)
Lemma case_Rabsolu:(r:R)(sumboolT (Rlt r R0) (Rge r R0)). 
Intro;Generalize (total_order_Rle R0 r);Intro;Elim X;Intro;Clear X.
Right;Apply (Rle_sym1 R0 r y).
Left;Fold (Rgt R0 r);Apply (not_Rle R0 r y).
Save.

(*********)
Definition Rabsolu:R->R:=
      [r:R](Cases (case_Rabsolu r) of
              (leftT  _) => (Ropp r)
             |(rightT _) => r
            end).

(*********)
Lemma Rabsolu_R0:(Rabsolu R0)==R0.
Unfold Rabsolu;Case (case_Rabsolu R0);Auto;Intro.
Generalize (Rlt_antirefl R0);Intro;ElimType False;Auto.
Save.

(*********)
Lemma Rabsolu_no_R0:(r:R)~r==R0->~(Rabsolu r)==R0.
Intros;Unfold Rabsolu;Case (case_Rabsolu r);Intro;Auto.
Apply Ropp_neq;Auto.
Save.

(*********)
Lemma Rabsolu_pos:(x:R)(Rle R0 (Rabsolu x)).
Intros;Unfold Rabsolu;Case (case_Rabsolu x);Intro.
Generalize (Rlt_Ropp x R0 r);Intro;Unfold Rgt in H;
 Rewrite Ropp_O in H;Unfold Rle;Left;Assumption.
Apply Rle_sym2;Assumption.
Save.

(*********)
Lemma Rabsolu_pos_lt:(x:R)(~x==R0)->(Rlt R0 (Rabsolu x)).
Intros;Generalize (Rabsolu_pos x);Intro;Unfold Rle in H0;
 Elim H0;Intro;Auto.
ElimType False;Clear H0;Elim H;Clear H;Generalize H1;
 Unfold Rabsolu;Case (case_Rabsolu x);Intros;Auto.
Clear r H1; Generalize (Rplus_plus_r x R0 (Ropp x) H0);
 Rewrite (let (H1,H2)=(Rplus_ne x) in H1);Rewrite (Rplus_Ropp_r x);Trivial.
Save.

(*********)
Lemma Rabsolu_minus_sym:(x,y:R)
 (Rabsolu (Rminus x y))==(Rabsolu (Rminus y x)).
Intros;Unfold Rabsolu;Case (case_Rabsolu (Rminus x y)); 
 Case (case_Rabsolu (Rminus y x));Intros.
 Generalize (Rminus_lt y x r);Generalize (Rminus_lt x y r0);Intros;
 Generalize (Rlt_antisym x y H);Intro;ElimType False;Auto.
Rewrite (Ropp_distr2 x y);Trivial.
Rewrite (Ropp_distr2 y x);Trivial.
Unfold Rge in r r0;Elim r;Elim r0;Intros;Clear r r0.
Generalize (Rgt_RoppO (Rminus x y) H);Rewrite (Ropp_distr2 x y);
 Intro;Unfold Rgt in H0;Generalize (Rlt_antisym R0 (Rminus y x) H0);
 Intro;ElimType False;Auto.
Rewrite (Rminus_eq x y H);Trivial.
Rewrite (Rminus_eq y x H0);Trivial.
Rewrite (Rminus_eq y x H0);Trivial.
Save.

(*********)
Lemma Rabsolu_mult:(x,y:R)
 (Rabsolu (Rmult x y))==(Rmult (Rabsolu x) (Rabsolu y)).
Intros;Unfold Rabsolu;Case (case_Rabsolu (Rmult x y));
 Case (case_Rabsolu x);Case (case_Rabsolu y);Intros;Auto.
Generalize (Rlt_anti_monotony y x R0 r r0);Intro;
 Rewrite (Rmult_Or y) in H;Generalize (Rlt_antisym (Rmult x y) R0 r1);
 Intro;Unfold Rgt in H;ElimType False;Rewrite (Rmult_sym y x) in H;
 Auto.
Rewrite (Ropp_mul1 x y);Trivial. 
Rewrite (Rmult_sym x (Ropp y));Rewrite (Ropp_mul1 y x);
 Rewrite (Rmult_sym  x y);Trivial.
Unfold Rge in r r0;Elim r;Elim r0;Clear r r0;Intros;Unfold Rgt in H H0.
Generalize (Rlt_monotony x R0 y H H0);Intro;Rewrite (Rmult_Or x) in H1;
 Generalize (Rlt_antisym (Rmult x y) R0 r1);Intro;ElimType False;Auto.
Rewrite H in r1;Rewrite (Rmult_Ol y) in r1;Generalize (Rlt_antirefl R0);
 Intro;ElimType False;Auto.
Rewrite H0 in r1;Rewrite (Rmult_Or x) in r1;Generalize (Rlt_antirefl R0);
 Intro;ElimType False;Auto.
Rewrite H0 in r1;Rewrite (Rmult_Or x) in r1;Generalize (Rlt_antirefl R0);
 Intro;ElimType False;Auto.
Rewrite (Ropp_mul2 x y);Trivial.
Unfold Rge in r r1;Elim r;Elim r1;Clear r r1;Intros;Unfold Rgt in H0 H.
Generalize (Rlt_monotony y x R0 H0 r0);Intro;Rewrite (Rmult_Or y) in H1;
 Rewrite (Rmult_sym y x) in H1; 
 Generalize (Rlt_antisym (Rmult x y) R0 H1);Intro;ElimType False;Auto.
Generalize (imp_not_Req x R0 (or_introl (Rlt x R0) (Rgt x R0) r0));
 Generalize (imp_not_Req y R0 (or_intror (Rlt y R0) (Rgt y R0) H0));Intros;
 Generalize (without_div_Od x y H);Intro;Elim H3;Intro;ElimType False;
 Auto.  
Rewrite H0 in H;Rewrite (Rmult_Or x) in H;Unfold Rgt in H;
 Generalize (Rlt_antirefl R0);Intro;ElimType False;Auto.
Rewrite H0;Rewrite (Rmult_Or x);Rewrite (Rmult_Or (Ropp x));Trivial.
Unfold Rge in r0 r1;Elim r0;Elim r1;Clear r0 r1;Intros;Unfold Rgt in H0 H.
Generalize (Rlt_monotony x y R0 H0 r);Intro;Rewrite (Rmult_Or x) in H1;
 Generalize (Rlt_antisym (Rmult x y) R0 H1);Intro;ElimType False;Auto.
Generalize (imp_not_Req y R0 (or_introl (Rlt y R0) (Rgt y R0) r));
 Generalize (imp_not_Req R0 x (or_introl (Rlt R0 x) (Rgt R0 x) H0));Intros;
 Generalize (without_div_Od x y H);Intro;Elim H3;Intro;ElimType False;
 Auto.  
Rewrite H0 in H;Rewrite (Rmult_Ol y) in H;Unfold Rgt in H;
 Generalize (Rlt_antirefl R0);Intro;ElimType False;Auto.
Rewrite H0;Rewrite (Rmult_Ol y);Rewrite (Rmult_Ol (Ropp y));Trivial.
Save.

(*********)
Lemma Rabsolu_Rinv:(r:R)(~r==R0)->(Rabsolu (Rinv r))==
                                  (Rinv (Rabsolu r)).
Intro;Unfold Rabsolu;Case (case_Rabsolu r);
 Case (case_Rabsolu (Rinv r));Auto;Intros.
Apply Ropp_Rinv;Auto.
Generalize (Rlt_Rinv2 r r1);Intro;Unfold Rge in r0;Elim r0;Intros.
Unfold Rgt in H1;Generalize (Rlt_antisym R0 (Rinv r) H1);Intro; 
 ElimType False;Auto.
Generalize 
  (imp_not_Req (Rinv r) R0 
   (or_introl (Rlt (Rinv r) R0) (Rgt (Rinv r) R0) H0));Intro;
 ElimType False;Auto.
Unfold Rge in r1;Elim r1;Clear r1;Intro.
Unfold Rgt in H0;Generalize (Rlt_antisym R0 (Rinv r)  
     (Rlt_Rinv r H0));Intro;ElimType False;Auto.
ElimType False;Auto.
Save. 

(*********)
Lemma Rabsolu_triang:(a,b:R)(Rle (Rabsolu (Rplus a b)) 
                                (Rplus (Rabsolu a) (Rabsolu b))).
Intros a b;Unfold Rabsolu;Case (case_Rabsolu (Rplus a b));
 Case (case_Rabsolu a);Case (case_Rabsolu b);Intros.
Apply (eq_Rle (Ropp (Rplus a b)) (Rplus (Ropp a) (Ropp b)));
 Rewrite (Ropp_distr1 a b);Reflexivity.
(**)
Rewrite (Ropp_distr1 a b);
 Apply (Rle_compatibility (Ropp a) (Ropp b) b);
 Unfold Rle;Unfold Rge in r;Elim r;Intro.
Left;Unfold Rgt in H;Generalize (Rlt_compatibility (Ropp b) R0 b H);
 Intro;Elim (Rplus_ne (Ropp b));Intros v w;Rewrite v in H0;Clear v w;
 Rewrite (Rplus_Ropp_l b) in H0;Apply (Rlt_trans (Ropp b) R0 b H0 H).
Right;Rewrite H;Apply Ropp_O.
(**)
Rewrite (Ropp_distr1 a b);
 Rewrite (Rplus_sym (Ropp a) (Ropp b));
 Rewrite (Rplus_sym a (Ropp b));
 Apply (Rle_compatibility (Ropp b) (Ropp a) a);
 Unfold Rle;Unfold Rge in r0;Elim r0;Intro.
Left;Unfold Rgt in H;Generalize (Rlt_compatibility (Ropp a) R0 a H);
 Intro;Elim (Rplus_ne (Ropp a));Intros v w;Rewrite v in H0;Clear v w;
 Rewrite (Rplus_Ropp_l a) in H0;Apply (Rlt_trans (Ropp a) R0 a H0 H).
Right;Rewrite H;Apply Ropp_O.
(**)
ElimType False;Generalize (Rge_plus_plus_r a b R0 r);Intro;
 Elim (Rplus_ne a);Intros v w;Rewrite v in H;Clear v w; 
 Generalize (Rge_trans (Rplus a b) a R0 H r0);Intro;Clear H;
 Unfold Rge in H0;Elim H0;Intro;Clear H0.
Unfold Rgt in H;Generalize (Rlt_antisym (Rplus a b) R0 r1);Intro;Auto.
Absurd (Rplus a b)==R0;Auto.
Apply (imp_not_Req (Rplus a b) R0);Left;Assumption.
(**)
ElimType False;Generalize (Rlt_compatibility a b R0 r);Intro;
 Elim (Rplus_ne a);Intros v w;Rewrite v in H;Clear v w;
 Generalize (Rlt_trans (Rplus a b) a R0 H r0);Intro;Clear H;
 Unfold Rge in r1;Elim r1;Clear r1;Intro.
Unfold Rgt in H;
 Generalize (Rlt_trans (Rplus a b) R0 (Rplus a b) H0 H);Intro;
 Apply (Rlt_antirefl (Rplus a b));Assumption.
Rewrite H in H0;Apply (Rlt_antirefl R0);Assumption.
(**)
Rewrite (Rplus_sym a b);Rewrite (Rplus_sym (Ropp a) b);
 Apply (Rle_compatibility b a (Ropp a));
 Apply (Rminus_le a (Ropp a));Unfold Rminus;Rewrite (Ropp_Ropp a);
 Generalize (Rlt_compatibility a a R0 r0);Clear r r1;Intro;
 Elim (Rplus_ne a);Intros v w;Rewrite v in H;Clear v w;
 Generalize (Rlt_trans (Rplus a a) a R0 H r0);Intro;
 Apply (Rlt_le (Rplus a a) R0 H0).
(**)
Apply (Rle_compatibility a b (Ropp b));
 Apply (Rminus_le b (Ropp b));Unfold Rminus;Rewrite (Ropp_Ropp b);
 Generalize (Rlt_compatibility b b R0 r);Clear r0 r1;Intro;
 Elim (Rplus_ne b);Intros v w;Rewrite v in H;Clear v w;
 Generalize (Rlt_trans (Rplus b b) b R0 H r);Intro;
 Apply (Rlt_le (Rplus b b) R0 H0).
(**)
Unfold Rle;Right;Reflexivity.
Save.

(*********)
Lemma Rabsolu_triang_inv:(a,b:R)(Rle (Rminus (Rabsolu a) (Rabsolu b))
                                     (Rabsolu (Rminus a b))).
Intros;Unfold Rabsolu;Case (case_Rabsolu a);Case (case_Rabsolu b);
 Case (case_Rabsolu (Rminus a b));Intros.
Unfold Rle;Right;Rewrite (Ropp_distr2 a b);Unfold Rminus;
 Rewrite Ropp_Ropp;Apply Rplus_sym.
Unfold 1 Rminus;Rewrite Ropp_Ropp;Rewrite Rplus_sym;
 Fold (Rminus b a);Generalize (minus_Rge a b r);Intro;
 Generalize (Rle_sym2 b a H);Intro;Generalize (Rle_minus b a H0);
 Intro;Generalize (Rle_sym2 R0 (Rminus a b) r);Intro;
 Apply (Rle_trans (Rminus b a) R0 (Rminus a b) H1 H2).
Rewrite (Ropp_distr2 a b);Unfold Rminus;
 Rewrite (Rplus_sym b (Ropp a));Apply Rle_compatibility; 
 Unfold Rge in r0;Elim r0;Intros.
Unfold Rle;Left;Generalize (Rgt_RoppO b H);Intro;Unfold Rgt in H;
 Apply (Rlt_trans (Ropp b) R0 b H0 H).
Unfold Rle;Right;Rewrite H;Apply Ropp_O.
Generalize (minus_Rge a b r);Intro;
 Generalize (Rge_trans a b R0 H r0);Intro;
 Generalize (Rlt_antisym a R0 r1);Intro; 
 Unfold Rge in H0;Elim H0;Intro.
Unfold Rgt in H2;ElimType False;Auto.
Rewrite H2 in r1;Generalize (Rlt_antirefl R0);Intro;ElimType False;
 Auto.
Generalize (Rminus_lt a b r);Intro;Generalize (Rlt_trans a b R0 H r0);
 Intro;Unfold Rge in r1;Elim r1;Intro.
Generalize (Rlt_antisym a R0 H0);Intro;Unfold Rgt in H1;ElimType False;
 Auto.
Rewrite H1 in H0;Generalize (Rlt_antirefl R0);Intro;ElimType False;
 Auto.
Unfold Rminus;Apply Rle_compatibility;Rewrite Ropp_Ropp;
 Generalize (Rlt_compatibility (Ropp b) b R0 r0);Intro; 
 Rewrite Rplus_Ropp_l in H;
 Rewrite (let (H1,H2)=(Rplus_ne (Ropp b)) in H1) in H;
 Generalize (Rlt_trans b R0 (Ropp b) r0 H);Intro;
 Apply Rlt_le;Assumption.
Generalize (Rlt_compatibility (Ropp (Rminus a b)) (Rminus a b)  R0 r);
Intro; Rewrite Rplus_Ropp_l in H;
 Rewrite (let (H1,H2)=(Rplus_ne (Ropp (Rminus a b))) in H1) in H;
 Generalize (Rlt_trans (Rminus a b) R0 (Ropp (Rminus a b)) r H);Intro;
 Apply Rlt_le;Assumption.
Unfold Rle;Right;Trivial.  
Save.

(*********)
Lemma Rabsolu_def1:(x,a:R)(Rlt x a)->(Rlt (Ropp a) x)->(Rlt (Rabsolu x) a).
Unfold Rabsolu;Intros;Case (case_Rabsolu x);Intro.
Generalize (Rlt_Ropp (Ropp a) x H0);Unfold Rgt;Rewrite Ropp_Ropp;Intro;
 Assumption.
Assumption.
Save.

(*********)
Lemma Rabsolu_def2:(x,a:R)(Rlt (Rabsolu x) a)->(Rlt x a)/\(Rlt (Ropp a) x).
Unfold Rabsolu;Intro x;Case (case_Rabsolu x);Intros.
Generalize (Rlt_RoppO x r);Unfold Rgt;Intro;
 Generalize (Rlt_trans R0 (Ropp x) a H0 H);Intro;Split. 
Apply (Rlt_trans x R0 a r H1).
Generalize (Rlt_Ropp (Ropp x) a H);Rewrite (Ropp_Ropp x);Unfold Rgt;Trivial.
Fold (Rgt a x) in H;Generalize (Rgt_ge_trans a x R0 H r);Intro;
 Generalize (Rgt_RoppO a H0);Intro;Fold (Rgt R0 (Ropp a));
 Generalize (Rge_gt_trans x R0 (Ropp a) r H1);Unfold Rgt;Intro;Split;
 Assumption.
Save.

