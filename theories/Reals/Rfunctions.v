(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(*i Some properties about pow and sum have been made with John Harrison i*)
(*i Some Lemmas (about pow and powerRZ) have been done by Laurent Thery i*)
(*********************************************************)
(*           Definition of the some functions            *)
(*                                                       *)
(*********************************************************)

Require Export Rlimit.
Require Omega.
Require Import Zpower.

(*******************************)
(*      Factorial              *)
(*******************************)
(*********)
Fixpoint fact [n:nat]:nat:=
  Cases n of
     O     => (S O)
    |(S n) => (mult (S n) (fact n))
  end.

(*********)
Lemma fact_neq_0:(n:nat)~(fact n)=O.
Cut (n,m:nat)~n=O->~m=O->~(mult n m)=O.
Intro;Induction n;Simpl;Auto.
Intros; Replace (plus (fact n0) (mult n0 (fact n0))) with 
  (mult (fact n0) (plus n0 (1))).
Cut ~(plus n0 (1))=O.
Intro;Apply H;Assumption.
Replace (plus n0 (1)) with (S n0);[Auto|Ring].
Intros;Ring.
Double Induction 1 2;Simpl;Auto.
Save.

(*********)
Lemma INR_fact_neq_0:(n:nat)~(INR (fact n))==R0.
Intro;Red;Intro;Apply (not_O_INR (fact n) (fact_neq_0 n));Assumption.
Save.    

(*********)
Lemma simpl_fact:(n:nat)(Rmult (Rinv (INR (fact (S n)))) 
         (Rinv (Rinv (INR (fact n)))))==
         (Rinv (INR (S n))).
Intro;Rewrite (Rinv_Rinv (INR (fact n)) (INR_fact_neq_0 n)); 
 Unfold 1 fact;Cbv Beta Iota;Fold fact;
 Rewrite (mult_INR (S n) (fact n));
 Rewrite (Rinv_Rmult (INR (S n)) (INR (fact n))).
Rewrite (Rmult_assoc (Rinv (INR (S n))) (Rinv (INR (fact n))) 
  (INR (fact n)));Rewrite (Rinv_l (INR (fact n)) (INR_fact_neq_0 n));
 Apply (let (H1,H2)=(Rmult_ne (Rinv (INR (S n)))) in H1).
Apply not_O_INR;Auto.
Apply INR_fact_neq_0.
Save.

(*******************************)
(*          Power              *)
(*******************************)
(*********)
Fixpoint pow [r:R;n:nat]:R:=
  Cases n of
     O     => R1
    |(S n) => (Rmult r (pow r n))
  end.

Lemma pow_O: (e : R)  (pow e O) == R1.
Simpl; Auto with real.
Save.
 
Lemma pow_1: (e : R)  (pow e (1)) == e.
Simpl; Auto with real.
Save.
 
Lemma pow_add:
 (e : R) (n, m : nat)  (pow e (plus n m)) == (Rmult (pow e n) (pow e m)).
Intros e n; Elim n; Simpl; Auto with real.
Intros n0 H' m; Rewrite H'; Auto with real.
Save.

Lemma pow_nonzero:
  (x:R) (n:nat) ~(x==R0) -> ~((pow x n)==R0).
Intro; Induction n; Simpl.
Intro; Red;Intro;Apply R1_neq_R0;Assumption.
Intros;Red; Intro;Elim (without_div_Od x (pow x n0) H1).
Intro; Auto.
Apply H;Assumption.
Save.

Hints Resolve pow_O pow_1 pow_add pow_nonzero:real.
 
Lemma pow_RN_plus:
 (e : R)
 (n, m : nat)
 ~ e == R0 ->  (pow e n) == (Rmult (pow e (plus n m)) (Rinv (pow e m))).
Intros e n; Elim n; Simpl; Auto with real.
Intros n0 H' m H'0.
Rewrite Rmult_assoc; Rewrite <- H'; Auto.
Save.

Lemma pow_lt: (e : R) (n : nat) (Rlt R0 e) ->  (Rlt R0 (pow e n)).
Intros e n; Elim n; Simpl; Auto with real.
Intros n0 H' H'0; Replace R0 with (Rmult e R0); Auto with real.
Save.
Hints Resolve pow_lt :real.

Lemma Rlt_pow_R1:
 (e : R) (n : nat) (Rlt R1 e) -> (lt O n) ->  (Rlt R1 (pow e n)).
Intros e n; Elim n; Simpl; Auto with real.
Intros H' H'0; ElimType False; Omega.
Intros n0; Case n0.
Simpl; Rewrite Rmult_1r; Auto.
Intros n1 H' H'0 H'1.
Replace R1 with (Rmult R1 R1); Auto with real.
Apply Rlt_trans with r2 := (Rmult e R1); Auto with real.
Apply Rlt_monotony; Auto with real.
Apply Rlt_trans with r2 := R1; Auto with real.
Apply H'; Auto with arith.
Save.
Hints Resolve Rlt_pow_R1 :real.

Lemma Rlt_pow:
 (e : R) (n, m : nat) (Rlt R1 e) -> (lt n m) ->  (Rlt (pow e n) (pow e m)).
Intros e n m H' H'0; Replace m with (plus (minus m n) n).
Rewrite pow_add.
Pattern 1 (pow e n); Replace (pow e n) with (Rmult R1 (pow e n)); 
 Auto with real.
Apply Rminus_lt.
Repeat Rewrite [x : R]  (Rmult_sym x (pow e n)); Rewrite <- Rminus_distr.
Replace R0 with (Rmult (pow e n) R0); Auto with real.
Apply Rlt_monotony; Auto with real.
Apply pow_lt; Auto with real.
Apply Rlt_trans with r2 := R1; Auto with real.
Apply Rlt_minus; Auto with real.
Apply Rlt_pow_R1; Auto with arith.
Apply simpl_lt_plus_l with p := n; Auto with arith.
Rewrite le_plus_minus_r; Auto with arith; Rewrite <- plus_n_O; Auto.
Rewrite plus_sym; Auto with arith.
Save.
Hints Resolve Rlt_pow :real.

(*********)
Lemma tech_pow_Rmult:(x:R)(n:nat)(Rmult x (pow x n))==(pow x (S n)).
Induction n; Simpl; Trivial.
Save.

(*********)
Lemma tech_pow_Rplus:(x:R)(a,n:nat)
  (Rplus (pow x a) (Rmult (INR n) (pow x a)))==
           (Rmult (INR (S n)) (pow x a)).
Intros; Pattern 1 (pow x a);  
 Rewrite <-(let (H1,H2)=(Rmult_ne (pow x a)) in H1); 
 Rewrite (Rmult_sym (INR n) (pow x a));
 Rewrite <- (Rmult_Rplus_distr (pow x a) R1 (INR n));
 Rewrite (Rplus_sym R1 (INR n)); Rewrite <-(S_INR n);
 Apply Rmult_sym.
Save.

Lemma poly: (n:nat)(e:R)(Rlt R0 e)->
 (Rle (Rplus R1 (Rmult (INR n) e)) (pow  (Rplus R1 e) n)).
Intros;Elim n.
Simpl;Cut (Rplus R1 (Rmult R0 e))==R1.
Intro;Rewrite H0;Unfold Rle;Right; Reflexivity.
Ring.
Intros;Unfold pow; Fold pow;
 Apply (Rle_trans (Rplus R1 (Rmult (INR (S n0)) e))
    (Rmult (Rplus R1 e) (Rplus R1 (Rmult (INR n0) e))) 
    (Rmult (Rplus R1 e) (pow (Rplus R1 e) n0))).
Cut (Rmult (Rplus R1 e) (Rplus R1 (Rmult (INR n0) e)))== 
  (Rplus (Rplus R1 (Rmult (INR (S n0)) e)) 
         (Rmult (INR n0) (Rmult e e))).
Intro;Rewrite H1;Pattern 1 (Rplus R1 (Rmult (INR (S n0)) e));
 Rewrite <-(let (H1,H2)=
   (Rplus_ne (Rplus R1 (Rmult (INR (S n0)) e))) in H1);
 Apply Rle_compatibility;Elim n0;Intros.
Simpl;Rewrite Rmult_Ol;Unfold Rle;Right;Auto.
Unfold Rle;Left;Generalize Rmult_gt;Unfold Rgt;Intro;
 Fold (Rsqr e);Apply (H3 (INR (S n1)) (Rsqr e) 
        (lt_INR_0 (S n1) (lt_O_Sn n1)));Fold (Rgt e R0) in H;
 Apply (pos_Rsqr1 e (imp_not_Req e R0 
  (or_intror (Rlt e R0) (Rgt e R0) H))).
Rewrite (S_INR n0);Ring.
Unfold Rle in H0;Elim H0;Intro. 
Unfold Rle;Left;Apply Rlt_monotony.
Rewrite Rplus_sym;
 Apply (Rlt_r_plus_R1 e (Rlt_le R0 e H)).
Assumption.
Rewrite H1;Unfold Rle;Right;Trivial.
Save.

Lemma Power_monotonic:
 (x:R) (m,n:nat) (Rgt (Rabsolu x) R1) 
        -> (le m n)
           -> (Rle (Rabsolu (pow x m)) (Rabsolu (pow x n))).
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
Save.

Lemma Pow_Rabsolu: (x:R) (n:nat)
     (pow (Rabsolu x) n)==(Rabsolu (pow x n)).
Intro;Induction n;Simpl.
Apply sym_eqT;Apply Rabsolu_pos_eq;Apply Rlt_le;Apply Rlt_R0_R1.
Intros; Rewrite H;Apply sym_eqT;Apply Rabsolu_mult.
Save.


Lemma Pow_x_infinity:
  (x:R) (Rgt (Rabsolu x) R1)
        -> (b:R) (Ex [N:nat] ((n:nat) (ge n N) 
                     -> (Rge (Rabsolu (pow x n)) b ))).
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
Save.

Lemma pow_ne_zero:
  (n:nat) ~(n=(0))-> (pow R0 n) == R0.
Induction n.
Simpl;Auto.
Intros;Elim H;Reflexivity.
Intros; Simpl;Apply Rmult_Ol.
Save.

Lemma Rinv_pow:
  (x:R) (n:nat) ~(x==R0) -> (Rinv (pow x n))==(pow (Rinv x) n).
Intros; Elim n; Simpl.
Apply Rinv_R1.
Intro m;Intro;Rewrite Rinv_Rmult.
Rewrite H0; Reflexivity;Assumption.
Assumption.
Apply pow_nonzero;Assumption.
Save.

Lemma pow_lt_1_zero:
  (x:R) (Rlt (Rabsolu x) R1)
        -> (e:R) (Rlt R0 e) 
                 -> (Ex[N:nat] (n:nat) (ge n N)
                         -> (Rlt (Rabsolu (pow x n)) e)).
Intros;Elim (Req_EM x R0);Intro. 
Exists (1);Rewrite H1;Intros n GE;Rewrite pow_ne_zero.
Rewrite Rabsolu_R0;Assumption.
Inversion GE;Auto.
Cut (Rgt (Rabsolu (Rinv x)) R1).
Intros;Elim (Pow_x_infinity (Rinv x) H2 (Rplus (Rinv e) R1));Intros N.
Exists N;Intros;Rewrite <- (Rinv_Rinv e).
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
Apply (Rlt_le_trans (Rinv e)
                    (Rplus (Rinv e) R1)
                    (Rabsolu (pow (Rinv x) n))).
Pattern 1 (Rinv e).
Rewrite <- (let (H1,H2) = 
                (Rplus_ne (Rinv e)) in H1).
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
Save.

Lemma pow_R1:
 (r : R) (n : nat) (pow r n) == R1 ->  (Rabsolu r) == R1 \/ n = O.
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
Save.

(*******************************)
(*          PowerRZ            *)
(*******************************)
(*i Due to L.Thery i*)

Tactic Definition CaseEqk name :=
Generalize (refl_equal ? name); Pattern -1 name; Case name.

Definition powerRZ :=
   [e : R] [n : Z]  Cases n of
                      ZERO => R1
                     | (POS p) => (pow e (convert p))
                     | (NEG p) => (Rinv (pow e (convert p)))
                    end.

Lemma Zpower_NR0:
 (e : Z) (n : nat) (Zle ZERO e) ->  (Zle ZERO (Zpower_nat e n)).
Intros e n; Elim n; Unfold Zpower_nat; Simpl; Auto with zarith.
Save.

Lemma powerRZ_O: (e : R)  (powerRZ e ZERO) == R1.
Simpl; Auto.
Save.
 
Lemma powerRZ_1: (e : R)  (powerRZ e (Zs ZERO)) == e.
Simpl; Auto with real.
Save.
 
Lemma powerRZ_NOR: (e : R) (z : Z) ~ e == R0 ->  ~ (powerRZ e z) == R0.
Intros e z; Case z; Simpl; Auto with real.
Save.
 
Lemma powerRZ_add:
 (e : R)
 (n, m : Z)
 ~ e == R0 ->  (powerRZ e (Zplus n m)) == (Rmult (powerRZ e n) (powerRZ e m)).
Intros e n m; Case n; Case m; Simpl; Auto with real.
Intros n1 m1; Rewrite convert_add; Auto with real.
Intros n1 m1; (CaseEqk '(compare m1 n1 EGAL)); Simpl; Auto with real.
Intros H' H'0; Rewrite compare_convert_EGAL with 1 := H'; Auto with real.
Intros H' H'0; Rewrite (true_sub_convert n1 m1); Auto with real.
Rewrite (pow_RN_plus e (minus (convert n1) (convert m1)) (convert m1));
 Auto with real.
Rewrite plus_sym; Rewrite le_plus_minus_r; Auto with real.
Rewrite Rinv_Rmult; Auto with real.
Rewrite Rinv_Rinv; Auto with real.
Apply lt_le_weak.
Apply compare_convert_INFERIEUR; Auto.
Apply ZC2; Auto.
Intros H' H'0; Rewrite (true_sub_convert m1 n1); Auto with real.
Rewrite (pow_RN_plus e (minus (convert m1) (convert n1)) (convert n1));
 Auto with real.
Rewrite plus_sym; Rewrite le_plus_minus_r; Auto with real.
Apply lt_le_weak.
Change (gt (convert m1) (convert n1)).
Apply compare_convert_SUPERIEUR; Auto.
Intros n1 m1; (CaseEqk '(compare m1 n1 EGAL)); Simpl; Auto with real.
Intros H' H'0; Rewrite compare_convert_EGAL with 1 := H'; Auto with real.
Intros H' H'0; Rewrite (true_sub_convert n1 m1); Auto with real.
Rewrite (pow_RN_plus e (minus (convert n1) (convert m1)) (convert m1));
 Auto with real.
Rewrite plus_sym; Rewrite le_plus_minus_r; Auto with real.
Apply lt_le_weak.
Apply compare_convert_INFERIEUR; Auto.
Apply ZC2; Auto.
Intros H' H'0; Rewrite (true_sub_convert m1 n1); Auto with real.
Rewrite (pow_RN_plus e (minus (convert m1) (convert n1)) (convert n1));
 Auto with real.
Rewrite plus_sym; Rewrite le_plus_minus_r; Auto with real.
Rewrite Rinv_Rmult; Auto with real.
Apply lt_le_weak.
Change (gt (convert m1) (convert n1)).
Apply compare_convert_SUPERIEUR; Auto.
Intros n1 m1; Rewrite convert_add; Auto with real.
Intros H'; Rewrite pow_add; Auto with real.
Apply Rinv_Rmult; Auto.
Apply pow_nonzero; Auto.
Apply pow_nonzero; Auto.
Save.
Hints Resolve powerRZ_O powerRZ_1 powerRZ_NOR powerRZ_add :real.
 
Lemma Zpower_nat_powerRZ:
 (n, m : nat)
  (IZR (Zpower_nat (inject_nat n) m)) == (powerRZ (INR n) (inject_nat m)).
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
Save.
 
Lemma powerRZ_lt: (e : R) (z : Z) (Rlt R0 e) ->  (Rlt R0 (powerRZ e z)).
Intros e z; Case z; Simpl; Auto with real.
Save.
Hints Resolve powerRZ_lt :real.
 
Lemma powerRZ_le: (e : R) (z : Z) (Rlt R0 e) ->  (Rle R0 (powerRZ e z)).
Intros e z H'; Apply Rlt_le; Auto with real.
Save.
Hints Resolve powerRZ_le :real.
 
Lemma Zpower_nat_powerRZ_absolu:
 (n, m : Z)
 (Zle ZERO m) ->  (IZR (Zpower_nat n (absolu m))) == (powerRZ (IZR n) m).
Intros n m; Case m; Simpl; Auto with zarith.
Intros p H'; Elim (convert p); Simpl; Auto with zarith.
Intros n0 H'0; Rewrite <- H'0; Simpl; Auto with zarith.
Rewrite <- mult_IZR; Auto.
Intros p H'; Absurd `0 <= (NEG p)`;Auto with zarith.
Save.

Lemma powerRZ_R1: (n : Z)  (powerRZ R1 n) == R1.
Intros n; Case n; Simpl; Auto.
Intros p; Elim (convert p); Simpl; Auto; Intros n0 H'; Rewrite H'; Ring.
Intros p; Elim (convert p); Simpl.
Exact Rinv_R1.
Intros n1 H'; Rewrite Rinv_Rmult; Try Rewrite Rinv_R1; Try Rewrite H';
 Auto with real.
Save.

(*******************************)
(*  Sum of n first naturals    *)
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
  (sum_nat_f_O [x]x n).

(*********)
Definition sum_nat [s,n:nat]:nat:=
  (sum_nat_f s n [x]x).

(*******************************)
(*             Sum             *)
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
Intros; Induction n; Simpl.
Ring.
Rewrite Rmult_Rplus_distrl;Rewrite Hrecn;Cut (plus n (1))=(S n).
Intro H;Rewrite H;Simpl;Ring.
Omega.
Save.

Lemma sum_f_R0_triangle:
  (x:nat->R)(n:nat) (Rle (Rabsolu (sum_f_R0 x n))
                         (sum_f_R0 [i:nat] (Rabsolu (x i)) n)).
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
Save.


(*******************************)
(*        Infinit Sum          *)
(*******************************)
(*********)
Definition infinit_sum:(nat->R)->R->Prop:=[s:nat->R;l:R]
  (eps:R)(Rgt eps R0)->
  (Ex[N:nat](n:nat)(ge n N)->(Rlt (R_dist (sum_f_R0 s n) l) eps)).


