(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(*i Some properties about pow and sum have been made with John Harrison i*)
(*i Some Lemmas (about pow and powerRZ) have been done by Laurent Thery i*)

(********************************************************)
(**          Definition of the sum functions            *)
(*                                                      *)
(********************************************************)

Require Rbase.
Require Export R_Ifp.
Require Export Rbasic_fun.
Require Export R_sqr.
Require Export SplitAbsolu.
Require Export SplitRmult.
Require Export ArithProp.
Require Omega.
Require Zpower.
V7only [ Import nat_scope. Import Z_scope. Import R_scope. ].
Open Local Scope nat_scope.
Open Local Scope R_scope.

(*******************************)
(**  Lemmas about factorial    *)
(*******************************)
(*********)
Lemma INR_fact_neq_0:(n:nat)~(INR (fact n))==R0.
Proof.
Intro;Red;Intro;Apply (not_O_INR (fact n) (fact_neq_0 n));Assumption.
Qed.    

(*********)
Lemma fact_simpl : (n:nat) (fact (S n))=(mult (S n) (fact n)).
Proof.
Intro; Reflexivity.
Qed. 

(*********)
Lemma simpl_fact:(n:nat)(Rmult (Rinv (INR (fact (S n)))) 
         (Rinv (Rinv (INR (fact n)))))==
         (Rinv (INR (S n))).
Proof.
Intro;Rewrite (Rinv_Rinv (INR (fact n)) (INR_fact_neq_0 n)); 
 Unfold 1 fact;Cbv Beta Iota;Fold fact;
 Rewrite (mult_INR (S n) (fact n));
 Rewrite (Rinv_Rmult (INR (S n)) (INR (fact n))).
Rewrite (Rmult_assoc (Rinv (INR (S n))) (Rinv (INR (fact n))) 
  (INR (fact n)));Rewrite (Rinv_l (INR (fact n)) (INR_fact_neq_0 n));
 Apply (let (H1,H2)=(Rmult_ne (Rinv (INR (S n)))) in H1).
Apply not_O_INR;Auto.
Apply INR_fact_neq_0.
Qed.

(*******************************)
(*          Power              *)
(*******************************)
(*********)
Fixpoint pow [r:R;n:nat]:R:=
  Cases n of
     O     => R1
    |(S n) => (Rmult r (pow r n))
  end.

V8Infix "^" pow : R_scope.

Lemma pow_O: (x : R)  (pow x O) == R1.
Proof.
Reflexivity.
Qed.
 
Lemma pow_1: (x : R)  (pow x (1)) == x.
Proof.
Simpl; Auto with real.
Qed.
 
Lemma pow_add:
 (x : R) (n, m : nat)  (pow x (plus n m)) == (Rmult (pow x n) (pow x m)).
Proof.
Intros x n; Elim n; Simpl; Auto with real.
Intros n0 H' m; Rewrite H'; Auto with real.
Qed.

Lemma pow_nonzero:
  (x:R) (n:nat) ~(x==R0) -> ~((pow x n)==R0).
Proof.
Intro; Induction n; Simpl.
Intro; Red;Intro;Apply R1_neq_R0;Assumption.
Intros;Red; Intro;Elim (without_div_Od x (pow x n0) H1).
Intro; Auto.
Apply H;Assumption.
Qed.

Hints Resolve pow_O pow_1 pow_add pow_nonzero:real.
 
Lemma pow_RN_plus:
 (x : R)
 (n, m : nat)
 ~ x == R0 ->  (pow x n) == (Rmult (pow x (plus n m)) (Rinv (pow x m))).
Proof.
Intros x n; Elim n; Simpl; Auto with real.
Intros n0 H' m H'0.
Rewrite Rmult_assoc; Rewrite <- H'; Auto.
Qed.

Lemma pow_lt: (x : R) (n : nat) (Rlt R0 x) ->  (Rlt R0 (pow x n)).
Proof.
Intros x n; Elim n; Simpl; Auto with real.
Intros n0 H' H'0; Replace R0 with (Rmult x R0); Auto with real.
Qed.
Hints Resolve pow_lt :real.

Lemma Rlt_pow_R1:
 (x : R) (n : nat) (Rlt R1 x) -> (lt O n) ->  (Rlt R1 (pow x n)).
Proof.
Intros x n; Elim n; Simpl; Auto with real.
Intros H' H'0; ElimType False; Omega.
Intros n0; Case n0.
Simpl; Rewrite Rmult_1r; Auto.
Intros n1 H' H'0 H'1.
Replace R1 with (Rmult R1 R1); Auto with real.
Apply Rlt_trans with r2 := (Rmult x R1); Auto with real.
Apply Rlt_monotony; Auto with real.
Apply Rlt_trans with r2 := R1; Auto with real.
Apply H'; Auto with arith.
Qed.
Hints Resolve Rlt_pow_R1 :real.

Lemma Rlt_pow:
 (x : R) (n, m : nat) (Rlt R1 x) -> (lt n m) ->  (Rlt (pow x n) (pow x m)).
Proof.
Intros x n m H' H'0; Replace m with (plus (minus m n) n).
Rewrite pow_add.
Pattern 1 (pow x n); Replace (pow x n) with (Rmult R1 (pow x n)); 
 Auto with real.
Apply Rminus_lt.
Repeat Rewrite [y : R]  (Rmult_sym y (pow x n)); Rewrite <- Rminus_distr.
Replace R0 with (Rmult (pow x n) R0); Auto with real.
Apply Rlt_monotony; Auto with real.
Apply pow_lt; Auto with real.
Apply Rlt_trans with r2 := R1; Auto with real.
Apply Rlt_minus; Auto with real.
Apply Rlt_pow_R1; Auto with arith.
Apply simpl_lt_plus_l with p := n; Auto with arith.
Rewrite le_plus_minus_r; Auto with arith; Rewrite <- plus_n_O; Auto.
Rewrite plus_sym; Auto with arith.
Qed.
Hints Resolve Rlt_pow :real.

(*********)
Lemma tech_pow_Rmult:(x:R)(n:nat)(Rmult x (pow x n))==(pow x (S n)).
Proof.
Induction n; Simpl; Trivial.
Qed.

(*********)
Lemma tech_pow_Rplus:(x:R)(a,n:nat)
  (Rplus (pow x a) (Rmult (INR n) (pow x a)))==
           (Rmult (INR (S n)) (pow x a)).
Proof.
Intros; Pattern 1 (pow x a);  
 Rewrite <-(let (H1,H2)=(Rmult_ne (pow x a)) in H1); 
 Rewrite (Rmult_sym (INR n) (pow x a));
 Rewrite <- (Rmult_Rplus_distr (pow x a) R1 (INR n));
 Rewrite (Rplus_sym R1 (INR n)); Rewrite <-(S_INR n);
 Apply Rmult_sym.
Qed.

Lemma poly: (n:nat)(x:R)(Rlt R0 x)->
 (Rle (Rplus R1 (Rmult (INR n) x)) (pow  (Rplus R1 x) n)).
Proof.
Intros;Elim n.
Simpl;Cut (Rplus R1 (Rmult R0 x))==R1.
Intro;Rewrite H0;Unfold Rle;Right; Reflexivity.
Ring.
Intros;Unfold pow; Fold pow;
 Apply (Rle_trans (Rplus R1 (Rmult (INR (S n0)) x))
    (Rmult (Rplus R1 x) (Rplus R1 (Rmult (INR n0) x))) 
    (Rmult (Rplus R1 x) (pow (Rplus R1 x) n0))).
Cut (Rmult (Rplus R1 x) (Rplus R1 (Rmult (INR n0) x)))== 
  (Rplus (Rplus R1 (Rmult (INR (S n0)) x)) 
         (Rmult (INR n0) (Rmult x x))).
Intro;Rewrite H1;Pattern 1 (Rplus R1 (Rmult (INR (S n0)) x));
 Rewrite <-(let (H1,H2)=
   (Rplus_ne (Rplus R1 (Rmult (INR (S n0)) x))) in H1);
 Apply Rle_compatibility;Elim n0;Intros.
Simpl;Rewrite Rmult_Ol;Unfold Rle;Right;Auto.
Unfold Rle;Left;Generalize Rmult_gt;Unfold Rgt;Intro;
 Fold (Rsqr x);Apply (H3 (INR (S n1)) (Rsqr x) 
        (lt_INR_0 (S n1) (lt_O_Sn n1)));Fold (Rgt x R0) in H;
 Apply (pos_Rsqr1 x (imp_not_Req x R0 
  (or_intror (Rlt x R0) (Rgt x R0) H))).
Rewrite (S_INR n0);Ring.
Unfold Rle in H0;Elim H0;Intro. 
Unfold Rle;Left;Apply Rlt_monotony.
Rewrite Rplus_sym;
 Apply (Rlt_r_plus_R1 x (Rlt_le R0 x H)).
Assumption.
Rewrite H1;Unfold Rle;Right;Trivial.
Qed.

Lemma Power_monotonic:
 (x:R) (m,n:nat) (Rgt (Rabsolu x) R1) 
        -> (le m n)
           -> (Rle (Rabsolu (pow x m)) (Rabsolu (pow x n))).
Proof.
Intros x m n H;Induction n;Intros;Inversion H0.
Unfold Rle; Right; Reflexivity.
Unfold Rle; Right; Reflexivity.
Apply (Rle_trans (Rabsolu (pow x m))
                 (Rabsolu (pow x n))
                 (Rabsolu (pow x (S n)))).
Apply Hrecn; Assumption.
Simpl;Rewrite Rabsolu_mult.
Pattern 1 (Rabsolu (pow x n)).
Rewrite <-Rmult_1r.
Rewrite (Rmult_sym (Rabsolu x) (Rabsolu (pow x n))).
Apply Rle_monotony.
Apply Rabsolu_pos.
Unfold Rgt in H.
Apply Rlt_le; Assumption.
Qed.

Lemma Pow_Rabsolu: (x:R) (n:nat)
     (pow (Rabsolu x) n)==(Rabsolu (pow x n)).
Proof.
Intro;Induction n;Simpl.
Apply sym_eqT;Apply Rabsolu_pos_eq;Apply Rlt_le;Apply Rlt_R0_R1.
Intros; Rewrite H;Apply sym_eqT;Apply Rabsolu_mult.
Qed.


Lemma Pow_x_infinity:
  (x:R) (Rgt (Rabsolu x) R1)
        -> (b:R) (Ex [N:nat] ((n:nat) (ge n N) 
                     -> (Rge (Rabsolu (pow x n)) b ))).
Proof.
Intros;Elim (archimed (Rmult b (Rinv (Rminus (Rabsolu x) R1))));Intros;
  Clear H1;
  Cut (Ex[N:nat] (Rge (INR N) (Rmult b (Rinv (Rminus (Rabsolu x) R1))))).
Intro; Elim H1;Clear H1;Intros;Exists x0;Intros;
 Apply (Rge_trans (Rabsolu (pow x n)) (Rabsolu (pow x x0)) b).
Apply Rle_sym1;Apply Power_monotonic;Assumption.
Rewrite <- Pow_Rabsolu;Cut (Rabsolu x)==(Rplus R1 (Rminus (Rabsolu x) R1)).
Intro; Rewrite H3;
 Apply (Rge_trans (pow (Rplus R1 (Rminus (Rabsolu x) R1)) x0)
                 (Rplus R1 (Rmult (INR x0)  
                                  (Rminus (Rabsolu x) R1)))
                 b).
Apply Rle_sym1;Apply poly;Fold (Rgt (Rminus (Rabsolu x) R1) R0);
 Apply Rgt_minus;Assumption.
Apply (Rge_trans 
         (Rplus R1 (Rmult (INR x0) (Rminus (Rabsolu x) R1)))
         (Rmult (INR x0) (Rminus (Rabsolu x) R1))
         b).
Apply Rle_sym1; Apply Rlt_le;Rewrite (Rplus_sym R1 
                   (Rmult (INR x0) (Rminus (Rabsolu x) R1)));
 Pattern 1 (Rmult (INR x0) (Rminus (Rabsolu x) R1));
 Rewrite <- (let (H1,H2) = (Rplus_ne 
            (Rmult (INR x0) (Rminus (Rabsolu x) R1))) in
         H1);
 Apply Rlt_compatibility;
 Apply Rlt_R0_R1.
Cut b==(Rmult (Rmult b (Rinv (Rminus (Rabsolu x) R1)))
              (Rminus (Rabsolu x) R1)).
Intros; Rewrite H4;Apply Rge_monotony.
Apply Rge_minus;Unfold Rge; Left; Assumption.
Assumption.
Rewrite Rmult_assoc;Rewrite Rinv_l.
Ring.
Apply imp_not_Req; Right;Apply Rgt_minus;Assumption.
Ring.
Cut `0<= (up (Rmult b (Rinv (Rminus (Rabsolu x) R1))))`\/
     `(up (Rmult b (Rinv (Rminus (Rabsolu x) R1)))) <=  0`.
Intros;Elim H1;Intro.
Elim (IZN (up (Rmult b (Rinv (Rminus (Rabsolu x) R1)))) H2);Intros;Exists x0;
 Apply (Rge_trans 
   (INR x0)
   (IZR (up (Rmult b (Rinv (Rminus (Rabsolu x) R1)))))
   (Rmult b (Rinv (Rminus (Rabsolu x) R1)))).
Rewrite INR_IZR_INZ;Apply IZR_ge;Omega.
Unfold Rge; Left; Assumption.
Exists O;Apply (Rge_trans (INR (0))
          (IZR (up (Rmult b (Rinv (Rminus (Rabsolu x) R1)))))
          (Rmult b (Rinv (Rminus (Rabsolu x) R1)))).
Rewrite INR_IZR_INZ;Apply IZR_ge;Simpl;Omega.
Unfold Rge; Left; Assumption.
Omega.
Qed.

Lemma pow_ne_zero:
  (n:nat) ~(n=(0))-> (pow R0 n) == R0.
Proof.
Induction n.
Simpl;Auto.
Intros;Elim H;Reflexivity.
Intros; Simpl;Apply Rmult_Ol.
Qed.

Lemma Rinv_pow:
  (x:R) (n:nat) ~(x==R0) -> (Rinv (pow x n))==(pow (Rinv x) n).
Proof.
Intros; Elim n; Simpl.
Apply Rinv_R1.
Intro m;Intro;Rewrite Rinv_Rmult.
Rewrite H0; Reflexivity;Assumption.
Assumption.
Apply pow_nonzero;Assumption.
Qed.

Lemma pow_lt_1_zero:
  (x:R) (Rlt (Rabsolu x) R1)
        -> (y:R) (Rlt R0 y) 
                 -> (Ex[N:nat] (n:nat) (ge n N)
                         -> (Rlt (Rabsolu (pow x n)) y)).
Proof.
Intros;Elim (Req_EM x R0);Intro. 
Exists (1);Rewrite H1;Intros n GE;Rewrite pow_ne_zero.
Rewrite Rabsolu_R0;Assumption.
Inversion GE;Auto.
Cut (Rgt (Rabsolu (Rinv x)) R1).
Intros;Elim (Pow_x_infinity (Rinv x) H2 (Rplus (Rinv y) R1));Intros N.
Exists N;Intros;Rewrite <- (Rinv_Rinv y).
Rewrite <- (Rinv_Rinv (Rabsolu (pow x n))).
Apply Rinv_lt.
Apply Rmult_lt_pos.
Apply Rlt_Rinv.
Assumption.
Apply Rlt_Rinv.
Apply Rabsolu_pos_lt.
Apply pow_nonzero.
Assumption.
Rewrite <- Rabsolu_Rinv.
Rewrite Rinv_pow.
Apply (Rlt_le_trans (Rinv y)
                    (Rplus (Rinv y) R1)
                    (Rabsolu (pow (Rinv x) n))).
Pattern 1 (Rinv y).
Rewrite <- (let (H1,H2) = 
                (Rplus_ne (Rinv y)) in H1).
Apply Rlt_compatibility.
Apply Rlt_R0_R1.
Apply Rle_sym2.
Apply H3.
Assumption.
Assumption.
Apply pow_nonzero.
Assumption.
Apply Rabsolu_no_R0.
Apply pow_nonzero.
Assumption.
Apply imp_not_Req.
Right; Unfold Rgt; Assumption.
Rewrite <- (Rinv_Rinv R1).
Rewrite Rabsolu_Rinv.
Unfold Rgt; Apply Rinv_lt.
Apply Rmult_lt_pos.
Apply Rabsolu_pos_lt.
Assumption.
Rewrite Rinv_R1; Apply Rlt_R0_R1.
Rewrite Rinv_R1; Assumption.
Assumption.
Red;Intro; Apply R1_neq_R0;Assumption.
Qed.

Lemma pow_R1:
 (r : R) (n : nat) (pow r n) == R1 ->  (Rabsolu r) == R1 \/ n = O.
Proof.
Intros r n H'.
Case (Req_EM (Rabsolu r) R1); Auto; Intros H'1.
Case (not_Req ? ? H'1); Intros H'2.
Generalize H'; Case n; Auto.
Intros n0 H'0.
Cut ~ r == R0; [Intros Eq1 | Idtac].
Cut ~ (Rabsolu r) == R0; [Intros Eq2 | Apply Rabsolu_no_R0]; Auto.
Absurd (Rlt (pow (Rabsolu (Rinv r)) O) (pow (Rabsolu (Rinv r)) (S n0))); Auto.
Replace (pow (Rabsolu (Rinv r)) (S n0)) with R1.
Simpl; Apply Rlt_antirefl; Auto.
Rewrite Rabsolu_Rinv; Auto.
Rewrite <- Rinv_pow; Auto.
Rewrite Pow_Rabsolu; Auto.
Rewrite H'0; Rewrite Rabsolu_right; Auto with real.
Apply Rle_ge; Auto with real.
Apply Rlt_pow; Auto with arith.
Rewrite Rabsolu_Rinv; Auto.
Apply Rlt_monotony_contra with z := (Rabsolu r).
Case (Rabsolu_pos r); Auto.
Intros H'3; Case Eq2; Auto.
Rewrite Rmult_1r; Rewrite Rinv_r; Auto with real.
Red;Intro;Absurd ``(pow r (S n0)) == 1``;Auto.
Simpl; Rewrite H; Rewrite Rmult_Ol; Auto with real.
Generalize H'; Case n; Auto.
Intros n0 H'0.
Cut ~ r == R0; [Intros Eq1 | Auto with real].
Cut ~ (Rabsolu r) == R0; [Intros Eq2 | Apply Rabsolu_no_R0]; Auto.
Absurd (Rlt (pow (Rabsolu r) O) (pow (Rabsolu r) (S n0))); 
  Auto with real arith.
Repeat Rewrite Pow_Rabsolu; Rewrite H'0; Simpl; Auto with real.
Red;Intro;Absurd ``(pow r (S n0)) == 1``;Auto.
Simpl; Rewrite H; Rewrite Rmult_Ol; Auto with real.
Qed.

Lemma pow_Rsqr : (x:R;n:nat) (pow x (mult (2) n))==(pow (Rsqr x) n).
Proof.
Intros; Induction n.
Reflexivity.
Replace (mult (2) (S n)) with (S (S (mult (2) n))).
Replace (pow x (S (S (mult (2) n)))) with ``x*x*(pow x (mult (S (S O)) n))``.
Rewrite Hrecn; Reflexivity.
Simpl; Ring.
Apply INR_eq; Do 2 Rewrite S_INR; Do 2 Rewrite mult_INR; Repeat Rewrite S_INR; Ring.
Qed.

Lemma pow_le : (a:R;n:nat) ``0<=a`` -> ``0<=(pow a n)``.
Proof.
Intros; Induction n.
Simpl; Left; Apply Rlt_R0_R1.
Simpl; Apply Rmult_le_pos; Assumption.
Qed.

(**********)
Lemma pow_1_even : (n:nat) ``(pow (-1) (mult (S (S O)) n))==1``.
Proof.
Intro; Induction n.
Reflexivity.
Replace (mult (2) (S n)) with (plus (2) (mult (2) n)).
Rewrite pow_add; Rewrite Hrecn; Simpl; Ring.
Replace (S n) with (plus n (1)); [Ring | Ring].
Qed.

(**********)
Lemma pow_1_odd : (n:nat) ``(pow (-1) (S (mult (S (S O)) n)))==-1``.
Proof.
Intro; Replace (S (mult (2) n)) with (plus (mult (2) n) (1)); [Idtac | Ring].
Rewrite pow_add; Rewrite pow_1_even; Simpl; Ring.
Qed.

(**********)
Lemma pow_1_abs : (n:nat) ``(Rabsolu (pow (-1) n))==1``.
Proof.
Intro; Induction n.
Simpl; Apply Rabsolu_R1.
Replace (S n) with (plus n (1)); [Rewrite pow_add | Ring].
Rewrite Rabsolu_mult.
Rewrite Hrecn; Rewrite Rmult_1l; Simpl; Rewrite Rmult_1r; Rewrite Rabsolu_Ropp; Apply Rabsolu_R1.
Qed.

Lemma pow_mult : (x:R;n1,n2:nat) (pow x (mult n1 n2))==(pow (pow x n1) n2).
Proof.
Intros; Induction n2.
Simpl; Replace (mult n1 O) with O; [Reflexivity | Ring].
Replace (mult n1 (S n2)) with (plus (mult n1 n2) n1).
Replace (S n2) with (plus n2 (1)); [Idtac | Ring].
Do 2 Rewrite pow_add.
Rewrite Hrecn2.
Simpl.
Ring.
Apply INR_eq; Rewrite plus_INR; Do 2 Rewrite mult_INR; Rewrite S_INR; Ring.
Qed.

Lemma pow_incr : (x,y:R;n:nat) ``0<=x<=y`` -> ``(pow x n)<=(pow y n)``.
Proof.
Intros.
Induction n.
Right; Reflexivity.
Simpl.
Elim H; Intros.
Apply Rle_trans with ``y*(pow x n)``.
Do 2 Rewrite <- (Rmult_sym (pow x n)).
Apply Rle_monotony.
Apply pow_le; Assumption.
Assumption.
Apply Rle_monotony.
Apply Rle_trans with x; Assumption.
Apply Hrecn.
Qed.

Lemma pow_R1_Rle : (x:R;k:nat) ``1<=x`` -> ``1<=(pow x k)``.
Proof.
Intros.
Induction k.
Right; Reflexivity.
Simpl.
Apply Rle_trans with ``x*1``.
Rewrite Rmult_1r; Assumption.
Apply Rle_monotony.
Left; Apply Rlt_le_trans with R1; [Apply Rlt_R0_R1 | Assumption].
Exact Hreck.
Qed.

Lemma Rle_pow : (x:R;m,n:nat) ``1<=x`` -> (le m n) -> ``(pow x m)<=(pow x n)``.
Proof.
Intros.
Replace n with (plus (minus n m) m).
Rewrite pow_add.
Rewrite Rmult_sym.
Pattern 1 (pow x m); Rewrite <- Rmult_1r.
Apply Rle_monotony.
Apply pow_le; Left; Apply Rlt_le_trans with R1; [Apply Rlt_R0_R1 | Assumption].
Apply pow_R1_Rle; Assumption.
Rewrite plus_sym.
Symmetry; Apply le_plus_minus; Assumption.
Qed.

Lemma pow1 : (n:nat) (pow R1 n)==R1.
Proof.
Intro; Induction n.
Reflexivity.
Simpl; Rewrite Hrecn; Rewrite Rmult_1r; Reflexivity.
Qed.

Lemma pow_Rabs : (x:R;n:nat) ``(pow x n)<=(pow (Rabsolu x) n)``.
Proof.
Intros; Induction n.
Right; Reflexivity.
Simpl; Case (case_Rabsolu x); Intro.
Apply Rle_trans with (Rabsolu ``x*(pow x n)``).
Apply Rle_Rabsolu.
Rewrite Rabsolu_mult.
Apply Rle_monotony.
Apply Rabsolu_pos.
Right; Symmetry; Apply Pow_Rabsolu.
Pattern 1 (Rabsolu x); Rewrite (Rabsolu_right x r); Apply Rle_monotony.
Apply Rle_sym2; Exact r.
Apply Hrecn.
Qed.

Lemma pow_maj_Rabs : (x,y:R;n:nat) ``(Rabsolu y)<=x`` -> ``(pow y n)<=(pow x n)``.
Proof.
Intros; Cut ``0<=x``.
Intro; Apply Rle_trans with (pow (Rabsolu y) n).
Apply pow_Rabs.
Induction n.
Right; Reflexivity.
Simpl; Apply Rle_trans with ``x*(pow (Rabsolu y) n)``.
Do 2 Rewrite <- (Rmult_sym (pow (Rabsolu y) n)).
Apply Rle_monotony.
Apply pow_le; Apply Rabsolu_pos.
Assumption.
Apply Rle_monotony.
Apply H0.
Apply Hrecn.
Apply Rle_trans with (Rabsolu y); [Apply Rabsolu_pos | Exact H].
Qed.

(*******************************)
(**         PowerRZ            *)
(*******************************)
(*i Due to L.Thery i*)

Tactic Definition CaseEqk name :=
Generalize (refl_equal ? name); Pattern -1 name; Case name.

Definition powerRZ :=
   [x : R] [n : Z]  Cases n of
                      ZERO => R1
                     | (POS p) => (pow x (convert p))
                     | (NEG p) => (Rinv (pow x (convert p)))
                    end.

Infix Local "^Z" powerRZ (at level 2, left associativity) : R_scope.

Lemma Zpower_NR0:
 (x : Z) (n : nat) (Zle ZERO x) ->  (Zle ZERO (Zpower_nat x n)).
Proof.
NewInduction n; Unfold Zpower_nat; Simpl; Auto with zarith.
Qed.

Lemma powerRZ_O: (x : R)  (powerRZ x ZERO) == R1.
Proof.
Reflexivity.
Qed.
 
Lemma powerRZ_1: (x : R)  (powerRZ x (Zs ZERO)) == x.
Proof.
Simpl; Auto with real.
Qed.
 
Lemma powerRZ_NOR: (x : R) (z : Z) ~ x == R0 ->  ~ (powerRZ x z) == R0.
Proof.
NewDestruct z; Simpl; Auto with real.
Qed.
 
Lemma powerRZ_add:
 (x : R)
 (n, m : Z)
 ~ x == R0 ->  (powerRZ x (Zplus n m)) == (Rmult (powerRZ x n) (powerRZ x m)).
Proof.
Intro x; NewDestruct n as [|n1|n1]; NewDestruct m as [|m1|m1]; Simpl;
  Auto with real.
(* POS/POS *)
Rewrite convert_add; Auto with real.
(* POS/NEG *)
(CaseEqk '(compare n1 m1 EGAL)); Simpl; Auto with real.
Intros H' H'0; Rewrite compare_convert_EGAL with 1 := H'; Auto with real.
Intros H' H'0; Rewrite (true_sub_convert m1 n1); Auto with real.
Rewrite (pow_RN_plus x (minus (convert m1) (convert n1)) (convert n1));
 Auto with real.
Rewrite plus_sym; Rewrite le_plus_minus_r; Auto with real.
Rewrite Rinv_Rmult; Auto with real.
Rewrite Rinv_Rinv; Auto with real.
Apply lt_le_weak.
Apply compare_convert_INFERIEUR; Auto.
Apply ZC2; Auto.
Intros H' H'0; Rewrite (true_sub_convert n1 m1); Auto with real.
Rewrite (pow_RN_plus x (minus (convert n1) (convert m1)) (convert m1));
 Auto with real.
Rewrite plus_sym; Rewrite le_plus_minus_r; Auto with real.
Apply lt_le_weak.
Change (gt (convert n1) (convert m1)).
Apply compare_convert_SUPERIEUR; Auto.
(* NEG/POS *)
(CaseEqk '(compare n1 m1 EGAL)); Simpl; Auto with real.
Intros H' H'0; Rewrite compare_convert_EGAL with 1 := H'; Auto with real.
Intros H' H'0; Rewrite (true_sub_convert m1 n1); Auto with real.
Rewrite (pow_RN_plus x (minus (convert m1) (convert n1)) (convert n1));
 Auto with real.
Rewrite plus_sym; Rewrite le_plus_minus_r; Auto with real.
Apply lt_le_weak.
Apply compare_convert_INFERIEUR; Auto.
Apply ZC2; Auto.
Intros H' H'0; Rewrite (true_sub_convert n1 m1); Auto with real.
Rewrite (pow_RN_plus x (minus (convert n1) (convert m1)) (convert m1));
 Auto with real.
Rewrite plus_sym; Rewrite le_plus_minus_r; Auto with real.
Rewrite Rinv_Rmult; Auto with real.
Apply lt_le_weak.
Change (gt (convert n1) (convert m1)).
Apply compare_convert_SUPERIEUR; Auto.
(* NEG/NEG *)
Rewrite convert_add; Auto with real.
Intros H'; Rewrite pow_add; Auto with real.
Apply Rinv_Rmult; Auto.
Apply pow_nonzero; Auto.
Apply pow_nonzero; Auto.
Qed.
Hints Resolve powerRZ_O powerRZ_1 powerRZ_NOR powerRZ_add :real.
 
Lemma Zpower_nat_powerRZ:
 (n, m : nat)
  (IZR (Zpower_nat (inject_nat n) m)) == (powerRZ (INR n) (inject_nat m)).
Proof.
Intros n m; Elim m; Simpl; Auto with real.
Intros m1 H'; Rewrite bij1; Simpl.
Replace (Zpower_nat (inject_nat n) (S m1))
     with (Zmult (inject_nat n) (Zpower_nat (inject_nat n) m1)).
Rewrite mult_IZR; Auto with real.
Repeat Rewrite <- INR_IZR_INZ; Simpl.
Rewrite H'; Simpl.
Case m1; Simpl; Auto with real.
Intros m2; Rewrite bij1; Auto.
Unfold Zpower_nat; Auto.
Qed.
 
Lemma powerRZ_lt: (x : R) (z : Z) (Rlt R0 x) ->  (Rlt R0 (powerRZ x z)).
Proof.
Intros x z; Case z; Simpl; Auto with real.
Qed.
Hints Resolve powerRZ_lt :real.
 
Lemma powerRZ_le: (x : R) (z : Z) (Rlt R0 x) ->  (Rle R0 (powerRZ x z)).
Proof.
Intros x z H'; Apply Rlt_le; Auto with real.
Qed.
Hints Resolve powerRZ_le :real.
 
Lemma Zpower_nat_powerRZ_absolu:
 (n, m : Z)
 (Zle ZERO m) ->  (IZR (Zpower_nat n (absolu m))) == (powerRZ (IZR n) m).
Proof.
Intros n m; Case m; Simpl; Auto with zarith.
Intros p H'; Elim (convert p); Simpl; Auto with zarith.
Intros n0 H'0; Rewrite <- H'0; Simpl; Auto with zarith.
Rewrite <- mult_IZR; Auto.
Intros p H'; Absurd `0 <= (NEG p)`;Auto with zarith.
Qed.

Lemma powerRZ_R1: (n : Z)  (powerRZ R1 n) == R1.
Proof.
Intros n; Case n; Simpl; Auto.
Intros p; Elim (convert p); Simpl; Auto; Intros n0 H'; Rewrite H'; Ring.
Intros p; Elim (convert p); Simpl.
Exact Rinv_R1.
Intros n1 H'; Rewrite Rinv_Rmult; Try Rewrite Rinv_R1; Try Rewrite H';
 Auto with real.
Qed.

(*******************************)
(** Sum of n first naturals    *)
(*******************************)
(*********)
Fixpoint sum_nat_f_O [f:nat->nat;n:nat]:nat:=       
  Cases n of                            
    O => (f O)                               
   |(S n') => (plus (sum_nat_f_O f n') (f (S n'))) 
  end.

(*********)
Definition sum_nat_f [s,n:nat;f:nat->nat]:nat:=      
  (sum_nat_f_O [x:nat](f (plus x s)) (minus n s)).

(*********)
Definition sum_nat_O [n:nat]:nat:=
  (sum_nat_f_O [x:nat]x n).

(*********)
Definition sum_nat [s,n:nat]:nat:=
  (sum_nat_f s n [x:nat]x).

(*******************************)
(**            Sum             *)
(*******************************)
(*********)
Fixpoint sum_f_R0 [f:nat->R;N:nat]:R:=
  Cases N of
     O     => (f O)
    |(S i) => (Rplus (sum_f_R0 f i) (f (S i)))
  end.

(*********)
Definition sum_f [s,n:nat;f:nat->R]:R:=      
  (sum_f_R0 [x:nat](f (plus x s)) (minus n s)).

Lemma GP_finite:
  (x:R) (n:nat) (Rmult (sum_f_R0 [n:nat] (pow x n) n)
                       (Rminus x R1)) ==
                (Rminus (pow x (plus n (1))) R1).
Proof.
Intros; Induction n; Simpl.
Ring.
Rewrite Rmult_Rplus_distrl;Rewrite Hrecn;Cut (plus n (1))=(S n).
Intro H;Rewrite H;Simpl;Ring.
Omega.
Qed.

Lemma sum_f_R0_triangle:
  (x:nat->R)(n:nat) (Rle (Rabsolu (sum_f_R0 x n))
                         (sum_f_R0 [i:nat] (Rabsolu (x i)) n)).
Proof.
Intro; Induction n; Simpl.
Unfold Rle; Right; Reflexivity.
Intro m; Intro;Apply (Rle_trans
          (Rabsolu (Rplus (sum_f_R0 x m) (x (S m))))
          (Rplus (Rabsolu (sum_f_R0 x m))
                 (Rabsolu (x (S m))))
          (Rplus (sum_f_R0 [i:nat](Rabsolu (x i)) m) 
                 (Rabsolu (x (S m))))).
Apply Rabsolu_triang.
Rewrite Rplus_sym;Rewrite (Rplus_sym 
  (sum_f_R0 [i:nat](Rabsolu (x i)) m) (Rabsolu (x (S m))));
  Apply Rle_compatibility;Assumption.
Qed.

(*******************************)
(*        Distance  in R       *)
(*******************************)

(*********)
Definition R_dist:R->R->R:=[x,y:R](Rabsolu (Rminus x y)).

(*********)
Lemma R_dist_pos:(x,y:R)(Rge (R_dist x y) R0).
Proof.
Intros;Unfold R_dist;Unfold Rabsolu;Case (case_Rabsolu (Rminus x y));Intro l.
Unfold Rge;Left;Apply (Rlt_RoppO (Rminus x y) l).
Trivial.
Qed.

(*********)
Lemma R_dist_sym:(x,y:R)(R_dist x y)==(R_dist y x).
Proof.
Unfold R_dist;Intros;SplitAbsolu;Ring.
Generalize (Rlt_RoppO (Rminus y x) r); Intro;
 Rewrite (Ropp_distr2 y x) in H;
 Generalize (Rlt_antisym (Rminus x y) R0 r0); Intro;Unfold Rgt in H;
 ElimType False; Auto.
Generalize (minus_Rge y x r); Intro;
 Generalize (minus_Rge x y r0); Intro;
 Generalize (Rge_ge_eq x y H0 H); Intro;Rewrite H1;Ring.
Qed.

(*********)
Lemma R_dist_refl:(x,y:R)((R_dist x y)==R0<->x==y).
Proof.
Unfold R_dist;Intros;SplitAbsolu;Split;Intros.
Rewrite (Ropp_distr2 x y) in H;Apply sym_eqT;
 Apply (Rminus_eq y x H).
Rewrite (Ropp_distr2 x y);Generalize (sym_eqT R x y H);Intro;
 Apply (eq_Rminus y x H0).
Apply (Rminus_eq x y H).
Apply (eq_Rminus x y H). 
Qed.

Lemma R_dist_eq:(x:R)(R_dist x x)==R0.
Proof.
Unfold R_dist;Intros;SplitAbsolu;Intros;Ring.
Qed.

(***********)
Lemma R_dist_tri:(x,y,z:R)(Rle (R_dist x y) 
                   (Rplus (R_dist x z) (R_dist z y))).
Proof.
Intros;Unfold R_dist; Replace ``x-y`` with ``(x-z)+(z-y)``;
  [Apply (Rabsolu_triang ``x-z`` ``z-y``)|Ring].
Qed.

(*********)
Lemma R_dist_plus: (a,b,c,d:R)(Rle (R_dist (Rplus a c) (Rplus b d))
                   (Rplus (R_dist a b) (R_dist c d))).
Proof.
Intros;Unfold R_dist;
 Replace (Rminus (Rplus a c) (Rplus b d))
  with (Rplus (Rminus a b) (Rminus c d)).
Exact (Rabsolu_triang (Rminus a b) (Rminus c d)).
Ring.
Qed.

(*******************************)
(**       Infinit Sum          *)
(*******************************)
(*********)
Definition infinit_sum:(nat->R)->R->Prop:=[s:nat->R;l:R]
  (eps:R)(Rgt eps R0)->
  (Ex[N:nat](n:nat)(ge n N)->(Rlt (R_dist (sum_f_R0 s n) l) eps)).
