Require Rbase.
Require DiscrR.
Require Rbasic_fun.


(****************************************************)
(* Rsqr : some results                              *)
(****************************************************)

Tactic Definition SqRing := Unfold Rsqr; Ring.

Lemma Rsqr_neg : (x:R) ``(Rsqr x)==(Rsqr (-x))``.
Intros; SqRing.
Save.

Lemma Rsqr_times : (x,y:R) ``(Rsqr (x*y))==(Rsqr x)*(Rsqr y)``.
Intros; SqRing.
Save.

Lemma Rsqr_plus : (x,y:R) ``(Rsqr (x+y))==(Rsqr x)+(Rsqr y)+2*x*y``.
Intros; SqRing.
Save.

Lemma Rsqr_minus : (x,y:R) ``(Rsqr (x-y))==(Rsqr x)+(Rsqr y)-2*x*y``.
Intros; SqRing.
Save.

Lemma Rsqr_neg_minus : (x,y:R) ``(Rsqr (x-y))==(Rsqr (y-x))``.
Intros; SqRing.
Save.

Lemma Rsqr_1 : ``(Rsqr 1)==1``.
SqRing.
Save.

Lemma Rsqr_gt_0_0 : (x:R) ``0<(Rsqr x)`` -> ~``x==0``.
Intros; Red; Intro; Rewrite H0 in H; Rewrite Rsqr_O in H; Elim (Rlt_antirefl ``0`` H).
Save.

Lemma Rsqr_div : (x,y:R) ~``y==0`` -> ``(Rsqr (x/y))==(Rsqr x)/(Rsqr y)``.
Intros; Unfold Rsqr; Field; Repeat Apply prod_neq_R0; Assumption.
Save.

Lemma Rsqr_eq_0 : (x:R) ``(Rsqr x)==0`` -> ``x==0``.
Unfold Rsqr; Intros; Generalize (without_div_Od x x H); Intro; Elim H0; Intro ; Assumption.
Save.

Lemma Rsqr_incr_0 : (x,y:R) ``(Rsqr x)<=(Rsqr y)`` -> ``0<=x`` -> ``0<=y`` -> ``x<=y``.
Intros; Case (total_order_Rle x y); Intro; [Assumption | Cut ``y<x``; [Intro; Unfold Rsqr in H; Generalize (Rmult_lt2 y x y x H1 H1 H2 H2); Intro; Generalize (Rle_lt_trans ``x*x`` ``y*y`` ``x*x`` H H3); Intro; Elim (Rlt_antirefl ``x*x`` H4) | Auto with real]].
Save.

Lemma Rsqr_incr_0_var : (x,y:R) ``(Rsqr x)<=(Rsqr y)`` -> ``0<=y`` -> ``x<=y``.
Intros; Case (total_order_Rle x y); Intro; [Assumption | Cut ``y<x``; [Intro; Unfold Rsqr in H; Generalize (Rmult_lt2 y x y x H0 H0 H1 H1); Intro; Generalize (Rle_lt_trans ``x*x`` ``y*y`` ``x*x`` H H2); Intro; Elim (Rlt_antirefl ``x*x`` H3) | Auto with real]].
Save.

Lemma Rsqr_incr_1 : (x,y:R) ``x<=y``->``0<=x``->``0<= y``->``(Rsqr x)<=(Rsqr y)``.
Intros; Unfold Rsqr; Apply Rle_Rmult_comp; Assumption.
Save.

Lemma Rsqr_incrst_0 : (x,y:R) ``(Rsqr x)<(Rsqr y)``->``0<=x``->``0<=y``-> ``x<y``.
Intros; Case (total_order x y); Intro; [Assumption | Elim H2; Intro; [Rewrite H3 in H; Elim (Rlt_antirefl (Rsqr y) H) | Generalize (Rmult_lt2 y x y x H1 H1 H3 H3); Intro; Unfold Rsqr in H; Generalize (Rlt_trans ``x*x`` ``y*y`` ``x*x`` H H4); Intro; Elim (Rlt_antirefl ``x*x`` H5)]].
Save.

Lemma Rsqr_incrst_1 : (x,y:R) ``x<y``->``0<=x``->``0<=y``->``(Rsqr x)<(Rsqr y)``.
Intros; Unfold Rsqr; Apply Rmult_lt2; Assumption.
Save.

Lemma Rsqr_neg_pos_le_0 : (x,y:R) ``(Rsqr x)<=(Rsqr y)``->``0<=y``->``-y<=x``.
Intros; Case (case_Rabsolu x); Intro.
Generalize (Rlt_Ropp x ``0`` r); Rewrite Ropp_O; Intro; Generalize (Rlt_le ``0`` ``-x`` H1); Intro; Rewrite (Rsqr_neg x) in H; Generalize (Rsqr_incr_0 (Ropp x) y H H2 H0); Intro; Rewrite <- (Ropp_Ropp x); Apply Rge_Ropp; Apply Rle_sym1; Assumption.
Apply Rle_trans with ``0``; [Rewrite <- Ropp_O; Apply Rge_Ropp; Apply Rle_sym1; Assumption | Apply Rle_sym2; Assumption].
Save.

Lemma Rsqr_neg_pos_le_1 : (x,y:R) ``(-y)<=x`` -> ``x<=y`` -> ``0<=y`` -> ``(Rsqr x)<=(Rsqr y)``.
Intros; Case (case_Rabsolu x); Intro.
Generalize (Rlt_Ropp x ``0`` r); Rewrite Ropp_O; Intro; Generalize (Rlt_le ``0`` ``-x`` H2); Intro; Generalize (Rle_Ropp ``-y`` x H); Rewrite Ropp_Ropp; Intro; Generalize (Rle_sym2 ``-x`` y H4); Intro; Rewrite (Rsqr_neg x); Apply Rsqr_incr_1; Assumption.
Generalize (Rle_sym2 ``0`` x r); Intro; Apply Rsqr_incr_1; Assumption.
Save.

Lemma neg_pos_Rsqr_le : (x,y:R) ``(-y)<=x``->``x<=y``->``(Rsqr x)<=(Rsqr y)``.
Intros; Case (case_Rabsolu x); Intro.
Generalize (Rlt_Ropp x ``0`` r); Rewrite Ropp_O; Intro; Generalize (Rle_Ropp ``-y`` x H); Rewrite Ropp_Ropp; Intro; Generalize (Rle_sym2 ``-x`` y H2); Intro; Generalize (Rlt_le ``0`` ``-x`` H1); Intro; Generalize (Rle_trans ``0`` ``-x`` y H4 H3); Intro; Rewrite (Rsqr_neg x); Apply Rsqr_incr_1; Assumption.
Generalize (Rle_sym2 ``0`` x r); Intro; Generalize (Rle_trans ``0`` x y H1 H0); Intro; Apply Rsqr_incr_1; Assumption.
Save.

Lemma Rsqr_abs : (x:R) ``(Rsqr x)==(Rsqr (Rabsolu x))``.
Intro; Unfold Rabsolu; Case (case_Rabsolu x); Intro; [Apply Rsqr_neg | Reflexivity].
Save.

Lemma Rsqr_le_abs_0 : (x,y:R) ``(Rsqr x)<=(Rsqr y)`` -> ``(Rabsolu x)<=(Rabsolu y)``.
Intros; Apply Rsqr_incr_0; Repeat Rewrite <- Rsqr_abs; [Assumption | Apply Rabsolu_pos | Apply Rabsolu_pos].
Save.

Lemma Rsqr_le_abs_1 : (x,y:R) ``(Rabsolu x)<=(Rabsolu y)`` -> ``(Rsqr x)<=(Rsqr y)``.
Intros; Rewrite (Rsqr_abs x); Rewrite (Rsqr_abs y); Apply (Rsqr_incr_1 (Rabsolu x) (Rabsolu y)  H (Rabsolu_pos x) (Rabsolu_pos y)).
Save.

Lemma Rsqr_lt_abs_0 : (x,y:R) ``(Rsqr x)<(Rsqr y)`` -> ``(Rabsolu x)<(Rabsolu y)``.
Intros; Apply Rsqr_incrst_0; Repeat Rewrite <- Rsqr_abs; [Assumption | Apply Rabsolu_pos | Apply Rabsolu_pos].
Save.

Lemma Rsqr_lt_abs_1 : (x,y:R) ``(Rabsolu x)<(Rabsolu y)`` -> ``(Rsqr x)<(Rsqr y)``.
Intros; Rewrite (Rsqr_abs x); Rewrite (Rsqr_abs y); Apply (Rsqr_incrst_1 (Rabsolu x) (Rabsolu y)  H (Rabsolu_pos x) (Rabsolu_pos y)).
Save.

Lemma Rsqr_inj : (x,y:R) ``0<=x`` -> ``0<=y`` -> (Rsqr x)==(Rsqr y) -> x==y.
Intros; Generalize (Rle_le_eq (Rsqr x) (Rsqr y)); Intro; Elim H2; Intros _ H3; Generalize (H3 H1); Intro; Elim H4; Intros; Apply Rle_antisym; Apply Rsqr_incr_0; Assumption.
Save.

Lemma Rsqr_eq_abs_0 : (x,y:R) (Rsqr x)==(Rsqr y) -> (Rabsolu x)==(Rabsolu y).
Intros; Unfold Rabsolu; Case (case_Rabsolu x); Case (case_Rabsolu y); Intros.
Rewrite -> (Rsqr_neg x) in H; Rewrite -> (Rsqr_neg y) in H; Generalize (Rlt_Ropp y ``0`` r); Generalize (Rlt_Ropp x ``0`` r0); Rewrite Ropp_O; Intros; Generalize (Rlt_le ``0`` ``-x`` H0); Generalize (Rlt_le ``0`` ``-y`` H1); Intros; Apply Rsqr_inj; Assumption.
Rewrite -> (Rsqr_neg x) in H; Generalize (Rle_sym2 ``0`` y r); Intro; Generalize (Rlt_Ropp x ``0`` r0); Rewrite Ropp_O; Intro; Generalize (Rlt_le ``0`` ``-x`` H1); Intro; Apply Rsqr_inj; Assumption.
Rewrite -> (Rsqr_neg y) in H; Generalize (Rle_sym2 ``0`` x r0); Intro; Generalize (Rlt_Ropp y ``0`` r); Rewrite Ropp_O; Intro; Generalize (Rlt_le ``0`` ``-y`` H1); Intro; Apply Rsqr_inj; Assumption.
Generalize (Rle_sym2 ``0`` x r0); Generalize (Rle_sym2 ``0`` y r); Intros; Apply Rsqr_inj; Assumption.
Save.

Lemma Rsqr_eq_asb_1 : (x,y:R) (Rabsolu x)==(Rabsolu y) -> (Rsqr x)==(Rsqr y).
Intros; Cut ``(Rsqr (Rabsolu x))==(Rsqr (Rabsolu y))``.
Intro; Repeat Rewrite <- Rsqr_abs in H0; Assumption.
Rewrite H; Reflexivity.
Save.

Lemma triangle_rectangle : (x,y,z:R) ``0<=z``->``(Rsqr x)+(Rsqr y)<=(Rsqr z)``->``-z<=x<=z`` /\``-z<=y<=z``.
Intros; Generalize (plus_le_is_le (Rsqr x) (Rsqr y) (Rsqr z) (pos_Rsqr y) H0); Rewrite Rplus_sym in H0; Generalize (plus_le_is_le (Rsqr y) (Rsqr x) (Rsqr z) (pos_Rsqr x) H0); Intros; Split; [Split; [Apply Rsqr_neg_pos_le_0; Assumption | Apply Rsqr_incr_0_var; Assumption] | Split; [Apply Rsqr_neg_pos_le_0; Assumption | Apply Rsqr_incr_0_var; Assumption]].
Save.

Lemma triangle_rectangle_lt : (x,y,z:R) ``(Rsqr x)+(Rsqr y)<(Rsqr z)`` -> ``(Rabsolu x)<(Rabsolu z)``/\``(Rabsolu y)<(Rabsolu z)``.
Intros; Split; [Generalize (plus_lt_is_lt (Rsqr x) (Rsqr y) (Rsqr z) (pos_Rsqr y) H); Intro; Apply Rsqr_lt_abs_0; Assumption | Rewrite Rplus_sym in H; Generalize (plus_lt_is_lt (Rsqr y) (Rsqr x) (Rsqr z) (pos_Rsqr x) H); Intro; Apply Rsqr_lt_abs_0; Assumption].
Save.

Lemma triangle_rectangle_le : (x,y,z:R) ``(Rsqr x)+(Rsqr y)<=(Rsqr z)`` -> ``(Rabsolu x)<=(Rabsolu z)``/\``(Rabsolu y)<=(Rabsolu z)``.
Intros; Split; [Generalize (plus_le_is_le (Rsqr x) (Rsqr y) (Rsqr z) (pos_Rsqr y) H); Intro; Apply Rsqr_le_abs_0; Assumption | Rewrite Rplus_sym in H; Generalize (plus_le_is_le (Rsqr y) (Rsqr x) (Rsqr z) (pos_Rsqr x) H); Intro; Apply Rsqr_le_abs_0; Assumption].
Save.


(*********************************************************************)
(* An axiomatic definition of sqrt                                   *)
(*********************************************************************)

Parameter sqrt : R -> R.

Axiom foo : (x:R) ``0<=x`` -> ``0<=(sqrt x)``.

Axiom bar : (x:R) ``0<=x`` -> ``(sqrt x)*(sqrt x)==x``.

Lemma sqrt_0 : ``(sqrt 0)==0``.
Apply Rsqr_eq_0; Unfold Rsqr; Apply bar; Right; Reflexivity. 
Save.

Lemma sqrt_1 : ``(sqrt 1)==1``.
Apply (Rsqr_inj (sqrt R1) R1); [Apply foo; Left | Left | Unfold Rsqr; Rewrite -> bar; [Ring | Left]]; Apply Rlt_R0_R1.
Save.

Lemma sqrt_eq_0 : (x:R) ``0<=x``->``(sqrt x)==0``->``x==0``.
Intros; Cut ``(Rsqr (sqrt x))==0``.
Intro; Unfold Rsqr in H1; Rewrite -> bar in H1; Assumption.
Rewrite H0; Apply Rsqr_O.
Save.

Lemma sqrt_lem_0 : (x,y:R) ``0<=x``->``0<=y``->(sqrt x)==y->``y*y==x``.
Intros; Rewrite <- H1; Apply (bar x H).
Save.

Lemma sqtr_lem_1 : (x,y:R) ``0<=x``->``0<=y``->``y*y==x``->(sqrt x)==y.
Intros; Apply Rsqr_inj; [Apply (foo x H) | Assumption | Unfold Rsqr; Rewrite -> H1; Apply (bar x H)].
Save.

Lemma sqrt_def : (x:R) ``0<=x``->``(sqrt x)*(sqrt x)==x``.
Intros; Apply (bar x H).
Save.

Lemma sqrt_square : (x:R) ``0<=x``->``(sqrt (x*x))==x``.
Intros; Apply (Rsqr_inj (sqrt (Rsqr x)) x (foo (Rsqr x) (pos_Rsqr x)) H); Unfold Rsqr; Apply (bar (Rsqr x) (pos_Rsqr x)).
Save.

Lemma sqrt_Rsqr : (x:R) ``0<=x``->``(sqrt (Rsqr x))==x``.
Intros; Unfold Rsqr; Apply sqrt_square; Assumption.
Save.

Lemma sqrt_Rsqr_abs : (x:R) (sqrt (Rsqr x))==(Rabsolu x).
Intro x; Rewrite -> Rsqr_abs; Apply sqrt_Rsqr; Apply Rabsolu_pos.
Save.

Lemma Rsqr_sqrt : (x:R) ``0<=x``->(Rsqr (sqrt x))==x.
Intros x H1; Unfold Rsqr; Apply (bar x H1).
Save.

Lemma sqrt_times : (x,y:R) ``0<=x``->``0<=y``->``(sqrt (x*y))==(sqrt x)*(sqrt y)``.
Intros x y H1 H2; Apply (Rsqr_inj (sqrt (Rmult x y)) (Rmult (sqrt x) (sqrt y)) (foo (Rmult x y) (Rmult_le_pos x y H1 H2)) (Rmult_le_pos (sqrt x) (sqrt y) (foo x H1) (foo y H2))); Rewrite Rsqr_times; Repeat Rewrite Rsqr_sqrt; [Ring | Assumption |Assumption | Apply (Rmult_le_pos x y H1 H2)].
Save.

Lemma sqrt_lt_R0 : (x:R) ``0<x`` -> ``0<(sqrt x)``.
Intros x H1; Apply Rsqr_incrst_0; [Rewrite Rsqr_O; Rewrite Rsqr_sqrt ; [Assumption | Left; Assumption] | Right; Reflexivity | Apply (foo x (Rlt_le R0 x H1))].
Save.

Lemma sqrt_div : (x,y:R) ``0<=x``->``0<y``->``(sqrt (x/y))==(sqrt x)/(sqrt y)``.
Intros x y H1 H2; Apply Rsqr_inj; [ Apply foo; Apply (Rmult_le_pos x (Rinv y)); [ Assumption | Generalize (Rlt_Rinv y H2); Clear H2; Intro H2; Left; Assumption] | Apply (Rmult_le_pos (sqrt x) (Rinv (sqrt y))) ; [ Apply (foo x H1) | Generalize (sqrt_lt_R0 y H2); Clear H2; Intro H2; Generalize (Rlt_Rinv (sqrt y) H2); Clear H2; Intro H2; Left; Assumption] | Rewrite Rsqr_div; Repeat Rewrite Rsqr_sqrt; [ Reflexivity | Left; Assumption | Assumption | Generalize (Rlt_Rinv y H2); Intro H3; Generalize (Rlt_le R0 (Rinv y) H3); Intro H4; Apply (Rmult_le_pos x (Rinv y) H1 H4) |Red; Intro H3; Generalize (Rlt_le R0 y H2); Intro H4; Generalize (sqrt_eq_0 y H4 H3); Intro H5; Rewrite H5 in H2; Elim (Rlt_antirefl R0 H2)]].
Save.

Lemma sqrt_lt_0 : (x,y:R) ``0<=x``->``0<=y``->``(sqrt x)<(sqrt y)``->``x<y``.
Intros x y H1 H2 H3; Generalize (Rsqr_incrst_1 (sqrt x) (sqrt y) H3 (foo x H1) (foo y H2)); Intro H4; Rewrite (Rsqr_sqrt x H1) in H4; Rewrite (Rsqr_sqrt y H2) in H4; Assumption.
Save.

Lemma sqrt_lt_1 : (x,y:R) ``0<=x``->``0<=y``->``x<y``->``(sqrt x)<(sqrt y)``.
Intros x y H1 H2 H3; Apply Rsqr_incrst_0; [Rewrite (Rsqr_sqrt x H1); Rewrite (Rsqr_sqrt y H2); Assumption | Apply (foo x H1) | Apply (foo y H2)].
Save.

Lemma sqrt_le_0 : (x,y:R) ``0<=x``->``0<=y``->``(sqrt x)<=(sqrt y)``->``x<=y``.
Intros x y H1 H2 H3; Generalize (Rsqr_incr_1 (sqrt x) (sqrt y) H3 (foo x H1) (foo y H2)); Intro H4; Rewrite (Rsqr_sqrt x H1) in H4; Rewrite (Rsqr_sqrt y H2) in H4; Assumption.
Save.

Lemma sqrt_le_1 : (x,y:R) ``0<=x``->``0<=y``->``x<=y``->``(sqrt x)<=(sqrt y)``.
Intros x y H1 H2 H3; Apply Rsqr_incr_0; [ Rewrite (Rsqr_sqrt x H1); Rewrite (Rsqr_sqrt y H2); Assumption | Apply (foo x H1) | Apply (foo y H2)].
Save.

Lemma sqrt_inj : (x,y:R) ``0<=x``->``0<=y``->(sqrt x)==(sqrt y)->x==y.
Intros; Cut ``(Rsqr (sqrt x))==(Rsqr (sqrt y))``.
Intro; Rewrite (Rsqr_sqrt x H) in H2; Rewrite (Rsqr_sqrt y H0) in H2; Assumption.
Rewrite H1; Reflexivity.
Save.

Lemma sqrt_less : (x:R)  ``0<=x``->``1<x``->``(sqrt x)<x``.
Intros x H1 H2; Generalize (sqrt_lt_1 R1 x (Rlt_le R0 R1 (Rlt_R0_R1)) H1 H2); Intro H3; Rewrite  sqrt_1 in H3; Generalize (Rmult_ne (sqrt x)); Intro H4; Elim H4; Intros H5 H6; Rewrite <- H5; Pattern 2 x; Rewrite <- (sqrt_def x H1); Apply (Rlt_monotony (sqrt x) R1 (sqrt x) (sqrt_lt_R0 x (Rlt_trans R0 R1 x Rlt_R0_R1 H2)) H3).
Save.

Lemma sqrt_more : (x:R) ``0<x``->``x<1``->``x<(sqrt x)``.
Intros x H1 H2; Generalize (sqrt_lt_1 x R1 (Rlt_le R0 x H1) (Rlt_le R0 R1 (Rlt_R0_R1)) H2); Intro H3; Rewrite  sqrt_1 in H3; Generalize (Rmult_ne (sqrt x)); Intro H4; Elim H4; Intros H5 H6; Rewrite <- H5; Pattern 1 x; Rewrite <- (sqrt_def x (Rlt_le R0 x H1)); Apply (Rlt_monotony (sqrt x) (sqrt x) R1 (sqrt_lt_R0 x H1) H3).
Save.

Lemma sqrt_cauchy : (a,b,c,d:R) ``a*c+b*d<=(sqrt ((Rsqr a)+(Rsqr b)))*(sqrt ((Rsqr c)+(Rsqr d)))``.
Intros a b c d; Apply Rsqr_incr_0_var; [Rewrite Rsqr_times; Repeat Rewrite Rsqr_sqrt; Unfold Rsqr; [Replace ``(a*c+b*d)*(a*c+b*d)`` with ``(a*a*c*c+b*b*d*d)+(2*a*b*c*d)``; [Replace ``(a*a+b*b)*(c*c+d*d)`` with ``(a*a*c*c+b*b*d*d)+(a*a*d*d+b*b*c*c)``; [Apply Rle_compatibility; Replace ``a*a*d*d+b*b*c*c`` with ``(2*a*b*c*d)+(a*a*d*d+b*b*c*c-2*a*b*c*d)``; [Pattern 1 ``2*a*b*c*d``; Rewrite <- Rplus_Or; Apply Rle_compatibility; Replace ``a*a*d*d+b*b*c*c-2*a*b*c*d`` with (Rsqr (Rminus (Rmult a d) (Rmult b c))); [Apply pos_Rsqr | Unfold Rsqr; Ring] | Ring] | Ring] | Ring] | Apply (ge0_plus_ge0_is_ge0 (Rsqr c) (Rsqr d) (pos_Rsqr c) (pos_Rsqr d)) | Apply (ge0_plus_ge0_is_ge0 (Rsqr a) (Rsqr b) (pos_Rsqr a) (pos_Rsqr b))] | Apply Rmult_le_pos; Apply foo; Apply ge0_plus_ge0_is_ge0; Apply pos_Rsqr].
Save.

(************************************************************)
(* Resolution of a*X^2+b*X+c=0                              *)
(************************************************************)

Definition Delta [a:nonzeroreal;b,c:R] : R := ``(Rsqr b)-4*a*c``.

Definition Delta_is_pos [a:nonzeroreal;b,c:R] : Prop := ``0<=(Delta a b c)``.

Definition sol_x1 [a:nonzeroreal;b,c:R] : R := ``(-b+(sqrt (Delta a b c)))/(2*a)``.

Definition sol_x2 [a:nonzeroreal;b,c:R] : R := ``(-b-(sqrt (Delta a b c)))/(2*a)``.

Lemma Rsqr_inv : (x:R) ~``x==0`` -> ``(Rsqr (/x))==/(Rsqr x)``.
Intros; Unfold Rsqr; Field; Repeat Apply prod_neq_R0; Assumption.
Save.

Lemma Rsqr_sol_eq_0_1 : (a:nonzeroreal;b,c,x:R) (Delta_is_pos a b c) -> (x==(sol_x1 a b c))\/(x==(sol_x2 a b c)) -> ``a*(Rsqr x)+b*x+c==0``.
Intros.
Elim H0; Intro.
Unfold sol_x1 in H1; Unfold Delta in H1; Rewrite H1; Unfold Rdiv; Repeat Rewrite Rsqr_times; Rewrite Rsqr_plus; Rewrite <- Rsqr_neg; Rewrite Rsqr_sqrt.
Rewrite Rsqr_inv.
Unfold Rsqr; Field.
Case a.
Intros y H2; Repeat Rewrite Rmult_assoc; Repeat Apply prod_neq_R0; Assumption Orelse DiscrR.
Apply prod_neq_R0; [DiscrR | Apply (cond_nonzero a)].
Unfold Delta_is_pos in H.
Unfold Delta in H.
Assumption.
Unfold sol_x2 in H1; Unfold Delta in H1; Rewrite H1; Unfold Rdiv; Repeat Rewrite Rsqr_times; Rewrite Rsqr_minus; Rewrite <- Rsqr_neg; Rewrite Rsqr_sqrt.
Rewrite Rsqr_inv.
Unfold Rsqr; Field.
Case a.
Intros y H2; Repeat Rewrite Rmult_assoc; Repeat Apply prod_neq_R0; Assumption Orelse DiscrR.
Apply prod_neq_R0; [DiscrR | Apply (cond_nonzero a)].
Unfold Delta_is_pos in H.
Unfold Delta in H.
Assumption.
Save.

Lemma canonical_Rsqr : (a:nonzeroreal;b,c,x:R) ``a*(Rsqr x)+b*x+c == a* (Rsqr (x+b/(2*a))) + (4*a*c - (Rsqr b))/(4*a)``.
Intros; Unfold Rsqr; Field; Case a; Intros y H1; Repeat Rewrite Rmult_assoc; Repeat Apply prod_neq_R0; Assumption Orelse DiscrR.
Save.

Lemma Rsqr_eq : (x,y:R) (Rsqr x)==(Rsqr y) -> x==y \/ x==``-y``.
Intros; Unfold Rsqr in H; Generalize (Rplus_plus_r ``-(y*y)`` ``x*x`` ``y*y`` H); Rewrite Rplus_Ropp_l; Replace ``-(y*y)+x*x`` with ``(x-y)*(x+y)``; [Intro; Generalize (without_div_Od ``x-y`` ``x+y`` H0); Intro; Elim H1; Intros; [Left; Apply Rminus_eq; Assumption | Right; Apply Rminus_eq; Unfold Rminus; Rewrite Ropp_Ropp; Assumption] | Ring].
Save.

Lemma Rsqr_sol_eq_0_0 : (a:nonzeroreal;b,c,x:R) (Delta_is_pos a b c) -> ``a*(Rsqr x)+b*x+c==0`` -> (x==(sol_x1 a b c))\/(x==(sol_x2 a b c)).
Intros; Rewrite (canonical_Rsqr a b c x) in H0; Rewrite Rplus_sym in H0; Generalize (Rplus_Ropp  ``(4*a*c-(Rsqr b))/(4*a)`` ``a*(Rsqr (x+b/(2*a)))`` H0); Cut ``(Rsqr b)-4*a*c==(Delta a b c)``.
Intro; Replace ``-((4*a*c-(Rsqr b))/(4*a))`` with ``((Rsqr b)-4*a*c)/(4*a)``.
Rewrite H1; Intro; Generalize (Rmult_mult_r ``/a`` ``a*(Rsqr (x+b/(2*a)))`` ``(Delta a b c)/(4*a)`` H2); Replace ``/a*(a*(Rsqr (x+b/(2*a))))`` with ``(Rsqr (x+b/(2*a)))``.
Replace ``/a*(Delta a b c)/(4*a)`` with ``(Rsqr ((sqrt (Delta a b c))/(2*a)))``.
Intro; Generalize (Rsqr_eq ``(x+b/(2*a))`` ``((sqrt (Delta a b c))/(2*a))`` H3); Intro; Elim H4; Intro.
Left; Unfold sol_x1; Generalize (Rplus_plus_r ``-(b/(2*a))`` ``x+b/(2*a)`` ``(sqrt (Delta a b c))/(2*a)`` H5); Replace `` -(b/(2*a))+(x+b/(2*a))`` with x.
Intro; Rewrite H6; Unfold Rdiv; Ring.
Ring.
Right; Unfold sol_x2; Generalize (Rplus_plus_r ``-(b/(2*a))`` ``x+b/(2*a)`` ``-((sqrt (Delta a b c))/(2*a))`` H5); Replace `` -(b/(2*a))+(x+b/(2*a))`` with x.
Intro; Rewrite H6; Unfold Rdiv; Ring.
Ring.
Rewrite Rsqr_div.
Rewrite Rsqr_sqrt; [Unfold Rdiv Rsqr; Field; Case a; Intros y H3; Repeat Rewrite Rmult_assoc; Repeat Apply prod_neq_R0; Assumption Orelse DiscrR | Unfold Delta_is_pos in H; Assumption].
Apply prod_neq_R0; [DiscrR | Apply (cond_nonzero a)].
Rewrite <- Rmult_assoc; Rewrite <- Rinv_l_sym.
Symmetry; Apply Rmult_1l.
Apply (cond_nonzero a).
Unfold Rdiv; Field; Case a; Intros y H3; Apply prod_neq_R0; [DiscrR | Assumption].
Unfold Delta; Reflexivity.
Save.