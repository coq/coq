(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(**********************************************************)
(** Complements for the reals.Integer and fractional part *)
(*                                                        *)
(**********************************************************)

Require Rbase.
Require Omega.
V7only [ Import nat_scope. Import Z_scope. Import R_scope. ].
Open Local Scope R_scope.

(*********************************************************)
(**      Fractional part                                 *)
(*********************************************************)

(**********)
Definition Int_part:R->Z:=[r:R](`(up r)-1`).

(**********)
Definition frac_part:R->R:=[r:R](Rminus r (IZR (Int_part r))).

(**********)
Lemma tech_up:(r:R)(z:Z)(Rlt r (IZR z))->(Rle (IZR z) (Rplus r R1))->
  z=(up r).
Intros;Generalize (archimed r);Intro;Elim H1;Intros;Clear H1;
 Unfold Rgt in H2;Unfold Rminus in H3;
Generalize (Rle_compatibility r (Rplus (IZR (up r)) 
 (Ropp r)) R1 H3);Intro;Clear H3;
 Rewrite (Rplus_sym (IZR (up r)) (Ropp r)) in H1;
 Rewrite <-(Rplus_assoc r (Ropp r) (IZR (up r))) in H1;
 Rewrite (Rplus_Ropp_r r) in H1;Elim (Rplus_ne (IZR (up r)));Intros a b;
 Rewrite b in H1;Clear a b;Apply (single_z_r_R1 r z (up r));Auto with zarith real.
Qed.

(**********)
Lemma up_tech:(r:R)(z:Z)(Rle (IZR z) r)->(Rlt r (IZR `z+1`))->
  `z+1`=(up r).
Intros;Generalize (Rle_compatibility R1 (IZR z) r H);Intro;Clear H;
 Rewrite (Rplus_sym R1 (IZR z)) in H1;Rewrite (Rplus_sym R1 r) in H1;
 Cut (R1==(IZR `1`));Auto with zarith real.
Intro;Generalize H1;Pattern 1 R1;Rewrite H;Intro;Clear H H1;
 Rewrite <-(plus_IZR z `1`) in H2;Apply (tech_up r `z+1`);Auto with zarith real.
Qed.

(**********)
Lemma fp_R0:(frac_part R0)==R0.
Unfold frac_part; Unfold Int_part; Elim (archimed R0);
 Intros; Unfold Rminus;
 Elim (Rplus_ne (Ropp (IZR `(up R0)-1`))); Intros a b;
 Rewrite b;Clear a b;Rewrite <- Z_R_minus;Cut (up R0)=`1`.
Intro;Rewrite H1;
 Rewrite (eq_Rminus (IZR `1`) (IZR `1`) (refl_eqT R (IZR `1`)));
 Apply Ropp_O. 
Elim (archimed R0);Intros;Clear H2;Unfold Rgt in H1;
 Rewrite (minus_R0 (IZR (up R0))) in H0;
 Generalize (lt_O_IZR (up R0) H1);Intro;Clear H1;
 Generalize (le_IZR_R1 (up R0) H0);Intro;Clear H H0;Omega.
Qed.

(**********)
Lemma for_base_fp:(r:R)(Rgt (Rminus (IZR (up r)) r) R0)/\ 
                       (Rle (Rminus (IZR (up r)) r) R1).
Intro; Split;
 Cut (Rgt (IZR (up r)) r)/\(Rle (Rminus (IZR (up r)) r) R1).
Intro; Elim H; Intros.
Apply (Rgt_minus (IZR (up r)) r H0).
Apply archimed.
Intro; Elim H; Intros.
Exact H1.
Apply archimed.
Qed.

(**********)
Lemma base_fp:(r:R)(Rge (frac_part r) R0)/\(Rlt (frac_part r) R1).
Intro; Unfold frac_part; Unfold Int_part; Split.
     (*sup a O*)
Cut (Rge (Rminus r (IZR (up r))) (Ropp R1)).
Rewrite <- Z_R_minus;Simpl;Intro; Unfold Rminus;
 Rewrite Ropp_distr1;Rewrite <-Rplus_assoc;
 Fold (Rminus r (IZR (up r)));
 Fold (Rminus (Rminus r (IZR (up r))) (Ropp R1));
 Apply Rge_minus;Auto with zarith real.
Rewrite <- Ropp_distr2;Apply Rle_Ropp;Elim (for_base_fp r); Auto with zarith real.
    (*inf a 1*) 
Cut (Rlt (Rminus r (IZR (up r))) R0).
Rewrite <- Z_R_minus; Simpl;Intro; Unfold Rminus;
 Rewrite Ropp_distr1;Rewrite <-Rplus_assoc;
 Fold (Rminus r (IZR (up r)));Rewrite Ropp_Ropp;
 Elim (Rplus_ne R1);Intros a b;Pattern 2 R1;Rewrite <-a;Clear a b;
 Rewrite (Rplus_sym  (Rminus r (IZR (up r))) R1);
 Apply Rlt_compatibility;Auto with zarith real.
Elim (for_base_fp r);Intros;Rewrite <-Ropp_O;
 Rewrite<-Ropp_distr2;Apply Rgt_Ropp;Auto with zarith real.
Qed.

(*********************************************************)
(**      Properties                                      *)
(*********************************************************)

(**********)
Lemma base_Int_part:(r:R)(Rle (IZR (Int_part r)) r)/\
                    (Rgt (Rminus (IZR (Int_part r)) r) (Ropp R1)). 
Intro;Unfold Int_part;Elim (archimed r);Intros.
Split;Rewrite <- (Z_R_minus (up r) `1`);Simpl.
Generalize (Rle_minus (Rminus (IZR (up r)) r) R1 H0);Intro;
 Unfold Rminus in H1;
 Rewrite (Rplus_assoc (IZR (up r)) (Ropp r) (Ropp R1)) in 
 H1;Rewrite (Rplus_sym (Ropp r) (Ropp R1)) in H1;
 Rewrite <-(Rplus_assoc (IZR (up r)) (Ropp R1) (Ropp r)) in
 H1;Fold (Rminus (IZR (up r)) R1) in H1;
 Fold (Rminus (Rminus (IZR (up r)) R1) r) in H1;
 Apply Rminus_le;Auto with zarith real.
Generalize (Rgt_plus_plus_r (Ropp R1) (IZR (up r)) r H);Intro;
 Rewrite (Rplus_sym (Ropp R1) (IZR (up r))) in H1;
 Generalize (Rgt_plus_plus_r (Ropp r) 
   (Rplus (IZR (up r)) (Ropp R1)) (Rplus (Ropp R1) r) H1);
 Intro;Clear H H0 H1;
 Rewrite (Rplus_sym (Ropp r) (Rplus (IZR (up r)) (Ropp R1)))
 in H2;Fold (Rminus (IZR (up r)) R1) in H2;
 Fold (Rminus (Rminus (IZR (up r)) R1) r) in H2;
 Rewrite (Rplus_sym (Ropp r) (Rplus (Ropp R1) r)) in H2;
 Rewrite (Rplus_assoc (Ropp R1) r (Ropp r)) in H2;
 Rewrite (Rplus_Ropp_r r) in H2;Elim (Rplus_ne (Ropp R1));Intros a b;
 Rewrite a in H2;Clear a b;Auto with zarith real.  
Qed.

(**********)
Lemma Int_part_INR:(n : nat)  (Int_part (INR n)) = (inject_nat n).
Intros n; Unfold Int_part.
Cut (up (INR n)) = (Zplus (inject_nat n) (inject_nat (1))).
Intros H'; Rewrite H'; Simpl; Ring.
Apply sym_equal; Apply tech_up; Auto.
Replace (Zplus (inject_nat n) (inject_nat (1))) with (INZ (S n)).
Repeat Rewrite <- INR_IZR_INZ.
Apply lt_INR; Auto.
Rewrite Zplus_sym; Rewrite <- inj_plus; Simpl; Auto.
Rewrite plus_IZR; Simpl; Auto with real.
Repeat Rewrite <- INR_IZR_INZ; Auto with real.
Qed.

(**********)
Lemma fp_nat:(r:R)(frac_part r)==R0->(Ex [c:Z](r==(IZR c))).
Unfold frac_part;Intros;Split with (Int_part r);Apply Rminus_eq; Auto with zarith real.
Qed.

(**********)
Lemma R0_fp_O:(r:R)~R0==(frac_part r)->~R0==r.
Red;Intros;Rewrite <- H0 in H;Generalize fp_R0;Intro;Auto with zarith real.
Qed.

(**********)
Lemma Rminus_Int_part1:(r1,r2:R)(Rge (frac_part r1) (frac_part r2))->
  (Int_part (Rminus r1 r2))=(Zminus (Int_part r1) (Int_part r2)).
Intros;Elim (base_fp r1);Elim (base_fp r2);Intros;
 Generalize (Rle_sym2 R0 (frac_part r2) H0);Intro;Clear H0;
 Generalize (Rle_Ropp R0 (frac_part r2) H4);Intro;Clear H4;
 Rewrite (Ropp_O) in H0;
 Generalize (Rle_sym2 (Ropp (frac_part r2)) R0 H0);Intro;Clear H0;
 Generalize (Rle_sym2 R0 (frac_part r1) H2);Intro;Clear H2;
 Generalize (Rlt_Ropp (frac_part r2) R1 H1);Intro;Clear H1;
 Unfold Rgt in H2;
 Generalize (sum_inequa_Rle_lt R0 (frac_part r1) R1 (Ropp R1)
   (Ropp (frac_part r2)) R0 H0 H3 H2 H4);Intro;Elim H1;Intros;
 Clear H1;Elim (Rplus_ne R1);Intros a b;Rewrite a in H6;Clear a b H5;
 Generalize (Rge_minus (frac_part r1) (frac_part r2) H);Intro;Clear H;
 Fold (Rminus (frac_part r1) (frac_part r2)) in H6;
 Generalize (Rle_sym2 R0 (Rminus (frac_part r1) (frac_part r2)) H1);
 Intro;Clear H1 H3 H4 H0 H2;Unfold frac_part in H6 H;
 Unfold Rminus in H6 H;
 Rewrite (Ropp_distr1 r2 (Ropp (IZR (Int_part r2)))) in H;
 Rewrite (Ropp_Ropp (IZR (Int_part r2))) in H;
 Rewrite (Rplus_assoc r1 (Ropp (IZR (Int_part r1))) 
  (Rplus (Ropp r2) (IZR (Int_part r2)))) in H;
 Rewrite <-(Rplus_assoc (Ropp (IZR (Int_part r1))) (Ropp r2)
  (IZR (Int_part r2))) in H;
 Rewrite (Rplus_sym (Ropp (IZR (Int_part r1))) (Ropp r2)) in H;
 Rewrite (Rplus_assoc (Ropp r2) (Ropp (IZR (Int_part r1)))
  (IZR (Int_part r2))) in H;
 Rewrite <-(Rplus_assoc r1 (Ropp r2) 
  (Rplus (Ropp (IZR (Int_part r1))) (IZR (Int_part r2)))) in H;
 Rewrite (Rplus_sym (Ropp (IZR (Int_part r1))) (IZR (Int_part r2))) in H;
 Fold (Rminus r1 r2) in H;Fold (Rminus (IZR (Int_part r2)) (IZR (Int_part r1))) 
 in H;Generalize (Rle_compatibility 
  (Rminus (IZR (Int_part r1)) (IZR (Int_part r2))) R0 
  (Rplus (Rminus r1 r2) (Rminus (IZR (Int_part r2)) (IZR (Int_part r1)))) H);Intro;
 Clear H;Rewrite (Rplus_sym (Rminus r1 r2)
  (Rminus (IZR (Int_part r2)) (IZR (Int_part r1)))) in H0;
 Rewrite <-(Rplus_assoc (Rminus (IZR (Int_part r1)) (IZR (Int_part r2)))
  (Rminus (IZR (Int_part r2)) (IZR (Int_part r1))) (Rminus r1 r2)) in H0;
 Unfold Rminus in H0;Fold (Rminus r1 r2) in H0;
 Rewrite (Rplus_assoc (IZR (Int_part r1)) (Ropp (IZR (Int_part r2))) 
  (Rplus (IZR (Int_part r2)) (Ropp (IZR (Int_part r1))))) in H0;
 Rewrite <-(Rplus_assoc (Ropp (IZR (Int_part r2))) (IZR (Int_part r2))
  (Ropp (IZR (Int_part r1)))) in H0;Rewrite (Rplus_Ropp_l (IZR (Int_part r2))) in 
 H0;Elim (Rplus_ne (Ropp (IZR (Int_part r1))));Intros a b;Rewrite b in H0;
 Clear a b;
 Elim (Rplus_ne (Rplus (IZR (Int_part r1)) (Ropp (IZR (Int_part r2)))));
 Intros a b;Rewrite a in H0;Clear a b;Rewrite (Rplus_Ropp_r (IZR (Int_part r1))) 
 in H0;Elim (Rplus_ne (Rminus r1 r2));Intros a b;Rewrite b in H0;
 Clear a b;Fold (Rminus (IZR (Int_part r1)) (IZR (Int_part r2))) in H0;
 Rewrite (Ropp_distr1 r2 (Ropp (IZR (Int_part r2)))) in H6;
 Rewrite (Ropp_Ropp (IZR (Int_part r2))) in H6;
 Rewrite (Rplus_assoc r1 (Ropp (IZR (Int_part r1))) 
  (Rplus (Ropp r2) (IZR (Int_part r2)))) in H6;
 Rewrite <-(Rplus_assoc (Ropp (IZR (Int_part r1))) (Ropp r2)
  (IZR (Int_part r2))) in H6;
 Rewrite (Rplus_sym (Ropp (IZR (Int_part r1))) (Ropp r2)) in H6;
 Rewrite (Rplus_assoc (Ropp r2) (Ropp (IZR (Int_part r1)))
  (IZR (Int_part r2))) in H6;
 Rewrite <-(Rplus_assoc r1 (Ropp r2) 
  (Rplus (Ropp (IZR (Int_part r1))) (IZR (Int_part r2)))) in H6;
 Rewrite (Rplus_sym (Ropp (IZR (Int_part r1))) (IZR (Int_part r2))) in H6;
 Fold (Rminus r1 r2) in H6;Fold (Rminus (IZR (Int_part r2)) (IZR (Int_part r1))) 
 in H6;Generalize (Rlt_compatibility 
   (Rminus (IZR (Int_part r1)) (IZR (Int_part r2))) 
   (Rplus (Rminus r1 r2) (Rminus (IZR (Int_part r2)) (IZR (Int_part r1)))) R1 H6);
 Intro;Clear H6;
 Rewrite (Rplus_sym (Rminus r1 r2)
  (Rminus (IZR (Int_part r2)) (IZR (Int_part r1)))) in H;
 Rewrite <-(Rplus_assoc (Rminus (IZR (Int_part r1)) (IZR (Int_part r2)))
  (Rminus (IZR (Int_part r2)) (IZR (Int_part r1))) (Rminus r1 r2)) in H;
 Rewrite <-(Ropp_distr2 (IZR (Int_part r1)) (IZR (Int_part r2))) in H;
 Rewrite (Rplus_Ropp_r (Rminus (IZR (Int_part r1)) (IZR (Int_part r2)))) in H;
 Elim (Rplus_ne (Rminus r1 r2));Intros a b;Rewrite b in H;Clear a b;
 Rewrite (Z_R_minus (Int_part r1) (Int_part r2)) in H0;
 Rewrite (Z_R_minus (Int_part r1) (Int_part r2)) in H;
 Cut R1==(IZR `1`);Auto with zarith real.
Intro;Rewrite H1 in H;Clear H1;
 Rewrite <-(plus_IZR `(Int_part r1)-(Int_part r2)` `1`) in H;
 Generalize (up_tech  (Rminus r1 r2) `(Int_part r1)-(Int_part r2)`
  H0 H);Intros;Clear H H0;Unfold 1 Int_part;Omega.
Qed.

(**********)
Lemma Rminus_Int_part2:(r1,r2:R)(Rlt (frac_part r1) (frac_part r2))->
  (Int_part (Rminus r1 r2))=(Zminus (Zminus (Int_part r1) (Int_part r2)) `1`).
Intros;Elim (base_fp r1);Elim (base_fp r2);Intros;
 Generalize (Rle_sym2 R0 (frac_part r2) H0);Intro;Clear H0;
 Generalize (Rle_Ropp R0 (frac_part r2) H4);Intro;Clear H4;
 Rewrite (Ropp_O) in H0;
 Generalize (Rle_sym2 (Ropp (frac_part r2)) R0 H0);Intro;Clear H0;
 Generalize (Rle_sym2 R0 (frac_part r1) H2);Intro;Clear H2;
 Generalize (Rlt_Ropp (frac_part r2) R1 H1);Intro;Clear H1;
 Unfold Rgt in H2;
 Generalize (sum_inequa_Rle_lt R0 (frac_part r1) R1 (Ropp R1)
   (Ropp (frac_part r2)) R0 H0 H3 H2 H4);Intro;Elim H1;Intros;
 Clear H1;Elim (Rplus_ne (Ropp R1));Intros a b;Rewrite b in H5;
 Clear a b H6;Generalize (Rlt_minus (frac_part r1) (frac_part r2) H);
 Intro;Clear H;Fold (Rminus (frac_part r1) (frac_part r2)) in H5;
 Clear H3 H4 H0 H2;Unfold frac_part in H5 H1;
 Unfold Rminus in H5 H1;
 Rewrite (Ropp_distr1 r2 (Ropp (IZR (Int_part r2)))) in H5;
 Rewrite (Ropp_Ropp (IZR (Int_part r2))) in H5;
 Rewrite (Rplus_assoc r1 (Ropp (IZR (Int_part r1))) 
  (Rplus (Ropp r2) (IZR (Int_part r2)))) in H5;
 Rewrite <-(Rplus_assoc (Ropp (IZR (Int_part r1))) (Ropp r2)
  (IZR (Int_part r2))) in H5;
 Rewrite (Rplus_sym (Ropp (IZR (Int_part r1))) (Ropp r2)) in H5;
 Rewrite (Rplus_assoc (Ropp r2) (Ropp (IZR (Int_part r1)))
  (IZR (Int_part r2))) in H5;
 Rewrite <-(Rplus_assoc r1 (Ropp r2) 
  (Rplus (Ropp (IZR (Int_part r1))) (IZR (Int_part r2)))) in H5;
 Rewrite (Rplus_sym (Ropp (IZR (Int_part r1))) (IZR (Int_part r2))) in H5;
 Fold (Rminus r1 r2) in H5;Fold (Rminus (IZR (Int_part r2)) (IZR (Int_part r1))) 
 in H5;Generalize (Rlt_compatibility 
  (Rminus (IZR (Int_part r1)) (IZR (Int_part r2))) (Ropp R1) 
  (Rplus (Rminus r1 r2) (Rminus (IZR (Int_part r2)) (IZR (Int_part r1)))) H5);
 Intro;Clear H5;Rewrite (Rplus_sym (Rminus r1 r2)
  (Rminus (IZR (Int_part r2)) (IZR (Int_part r1)))) in H;
 Rewrite <-(Rplus_assoc (Rminus (IZR (Int_part r1)) (IZR (Int_part r2)))
  (Rminus (IZR (Int_part r2)) (IZR (Int_part r1))) (Rminus r1 r2)) in H;
 Unfold Rminus in H;Fold (Rminus r1 r2) in H;
 Rewrite (Rplus_assoc (IZR (Int_part r1)) (Ropp (IZR (Int_part r2))) 
  (Rplus (IZR (Int_part r2)) (Ropp (IZR (Int_part r1))))) in H;
 Rewrite <-(Rplus_assoc (Ropp (IZR (Int_part r2))) (IZR (Int_part r2))
  (Ropp (IZR (Int_part r1)))) in H;Rewrite (Rplus_Ropp_l (IZR (Int_part r2))) in 
 H;Elim (Rplus_ne (Ropp (IZR (Int_part r1))));Intros a b;Rewrite b in H;
 Clear a b;Rewrite (Rplus_Ropp_r (IZR (Int_part r1))) in H;
 Elim (Rplus_ne (Rminus r1 r2));Intros a b;Rewrite b in H;
 Clear a b;Fold (Rminus (IZR (Int_part r1)) (IZR (Int_part r2))) in H;
 Fold (Rminus (Rminus (IZR (Int_part r1)) (IZR (Int_part r2))) R1) in H;
 Rewrite (Ropp_distr1 r2 (Ropp (IZR (Int_part r2)))) in H1;
 Rewrite (Ropp_Ropp (IZR (Int_part r2))) in H1;
 Rewrite (Rplus_assoc r1 (Ropp (IZR (Int_part r1))) 
  (Rplus (Ropp r2) (IZR (Int_part r2)))) in H1;
 Rewrite <-(Rplus_assoc (Ropp (IZR (Int_part r1))) (Ropp r2)
  (IZR (Int_part r2))) in H1;
 Rewrite (Rplus_sym (Ropp (IZR (Int_part r1))) (Ropp r2)) in H1;
 Rewrite (Rplus_assoc (Ropp r2) (Ropp (IZR (Int_part r1)))
  (IZR (Int_part r2))) in H1;
 Rewrite <-(Rplus_assoc r1 (Ropp r2) 
  (Rplus (Ropp (IZR (Int_part r1))) (IZR (Int_part r2)))) in H1;
 Rewrite (Rplus_sym (Ropp (IZR (Int_part r1))) (IZR (Int_part r2))) in H1;
 Fold (Rminus r1 r2) in H1;Fold (Rminus (IZR (Int_part r2)) (IZR (Int_part r1))) 
 in H1;Generalize (Rlt_compatibility 
   (Rminus (IZR (Int_part r1)) (IZR (Int_part r2))) 
   (Rplus (Rminus r1 r2) (Rminus (IZR (Int_part r2)) (IZR (Int_part r1)))) R0 H1);
 Intro;Clear H1;
 Rewrite (Rplus_sym (Rminus r1 r2)
  (Rminus (IZR (Int_part r2)) (IZR (Int_part r1)))) in H0;
 Rewrite <-(Rplus_assoc (Rminus (IZR (Int_part r1)) (IZR (Int_part r2)))
  (Rminus (IZR (Int_part r2)) (IZR (Int_part r1))) (Rminus r1 r2)) in H0;
 Rewrite <-(Ropp_distr2 (IZR (Int_part r1)) (IZR (Int_part r2))) in H0;
 Rewrite (Rplus_Ropp_r (Rminus (IZR (Int_part r1)) (IZR (Int_part r2)))) in H0;
 Elim (Rplus_ne (Rminus r1 r2));Intros a b;Rewrite b in H0;Clear a b;
 Rewrite <-(Rplus_Ropp_l R1) in H0;
 Rewrite <-(Rplus_assoc (Rminus (IZR (Int_part r1)) (IZR (Int_part r2)))
  (Ropp R1) R1) in H0;
 Fold (Rminus (Rminus (IZR (Int_part r1)) (IZR (Int_part r2))) R1) in H0;
 Rewrite (Z_R_minus (Int_part r1) (Int_part r2)) in H0;
 Rewrite (Z_R_minus (Int_part r1) (Int_part r2)) in H;
 Cut R1==(IZR `1`);Auto with zarith real.
Intro;Rewrite H1 in H;Rewrite H1 in H0;Clear H1;
 Rewrite (Z_R_minus `(Int_part r1)-(Int_part r2)` `1`) in H;
 Rewrite (Z_R_minus `(Int_part r1)-(Int_part r2)` `1`) in H0;
 Rewrite <-(plus_IZR `(Int_part r1)-(Int_part r2)-1` `1`) in H0;
 Generalize (Rlt_le (IZR `(Int_part r1)-(Int_part r2)-1`) (Rminus r1 r2) H);
 Intro;Clear H;
 Generalize (up_tech  (Rminus r1 r2) `(Int_part r1)-(Int_part r2)-1`
  H1 H0);Intros;Clear H0 H1;Unfold 1 Int_part;Omega.
Qed.

(**********)
Lemma Rminus_fp1:(r1,r2:R)(Rge (frac_part r1) (frac_part r2))->
  (frac_part (Rminus r1 r2))==(Rminus (frac_part r1) (frac_part r2)).
Intros;Unfold frac_part;
 Generalize (Rminus_Int_part1 r1 r2 H);Intro;Rewrite -> H0;
 Rewrite <- (Z_R_minus (Int_part r1) (Int_part r2));Unfold Rminus;
 Rewrite -> (Ropp_distr1 (IZR (Int_part r1)) (Ropp (IZR (Int_part r2))));
 Rewrite -> (Ropp_distr1 r2 (Ropp (IZR (Int_part r2))));
 Rewrite -> (Ropp_Ropp (IZR (Int_part r2)));
 Rewrite -> (Rplus_assoc r1 (Ropp r2)
             (Rplus (Ropp (IZR (Int_part r1))) (IZR (Int_part r2))));
 Rewrite -> (Rplus_assoc r1 (Ropp (IZR (Int_part r1)))
             (Rplus (Ropp r2) (IZR (Int_part r2))));
 Rewrite <- (Rplus_assoc (Ropp r2) (Ropp (IZR (Int_part r1)))
             (IZR (Int_part r2)));
 Rewrite <- (Rplus_assoc (Ropp (IZR (Int_part r1))) (Ropp r2)
             (IZR (Int_part r2)));
 Rewrite -> (Rplus_sym (Ropp r2) (Ropp (IZR (Int_part r1))));Auto with zarith real.
Qed.

(**********)
Lemma Rminus_fp2:(r1,r2:R)(Rlt (frac_part r1) (frac_part r2))->
  (frac_part (Rminus r1 r2))==
  (Rplus (Rminus (frac_part r1) (frac_part r2)) R1).
Intros;Unfold frac_part;Generalize (Rminus_Int_part2 r1 r2 H);Intro;
 Rewrite -> H0;
 Rewrite <- (Z_R_minus (Zminus (Int_part r1) (Int_part r2)) `1`);
 Rewrite <- (Z_R_minus (Int_part r1) (Int_part r2));Unfold Rminus;
 Rewrite -> (Ropp_distr1 (Rplus (IZR (Int_part r1)) (Ropp (IZR (Int_part r2))))
             (Ropp (IZR `1`)));
 Rewrite -> (Ropp_distr1 r2 (Ropp (IZR (Int_part r2))));
 Rewrite -> (Ropp_Ropp (IZR `1`));
 Rewrite -> (Ropp_Ropp (IZR (Int_part r2)));
 Rewrite -> (Ropp_distr1 (IZR (Int_part r1)));
 Rewrite -> (Ropp_Ropp (IZR (Int_part r2)));Simpl;
 Rewrite <- (Rplus_assoc (Rplus r1 (Ropp r2))
             (Rplus (Ropp (IZR (Int_part r1))) (IZR (Int_part r2))) R1);
 Rewrite -> (Rplus_assoc r1 (Ropp r2)
             (Rplus (Ropp (IZR (Int_part r1))) (IZR (Int_part r2))));
 Rewrite -> (Rplus_assoc r1 (Ropp (IZR (Int_part r1)))
             (Rplus (Ropp r2) (IZR (Int_part r2)))); 
 Rewrite <- (Rplus_assoc (Ropp r2) (Ropp (IZR (Int_part r1)))
             (IZR (Int_part r2)));
 Rewrite <- (Rplus_assoc (Ropp (IZR (Int_part r1))) (Ropp r2)
             (IZR (Int_part r2)));
 Rewrite -> (Rplus_sym (Ropp r2) (Ropp (IZR (Int_part r1))));Auto with zarith real.
Qed.

(**********)
Lemma plus_Int_part1:(r1,r2:R)(Rge (Rplus (frac_part r1) (frac_part r2)) R1)->
  (Int_part (Rplus r1 r2))=(Zplus (Zplus (Int_part r1) (Int_part r2)) `1`).
Intros;
 Generalize (Rle_sym2 R1 (Rplus (frac_part r1) (frac_part r2)) H);
 Intro;Clear H;Elim (base_fp r1);Elim (base_fp r2);Intros;Clear H H2;
 Generalize (Rlt_compatibility (frac_part r2) (frac_part r1) R1 H3);
 Intro;Clear H3;
 Generalize (Rlt_compatibility R1 (frac_part r2) R1 H1);Intro;Clear H1;
 Rewrite (Rplus_sym R1 (frac_part r2)) in H2;
 Generalize (Rlt_trans (Rplus (frac_part r2) (frac_part r1))
  (Rplus (frac_part r2) R1) (Rplus R1 R1) H H2);Intro;Clear H H2;
 Rewrite (Rplus_sym (frac_part r2) (frac_part r1)) in H1;
 Unfold frac_part in H0 H1;Unfold Rminus in H0 H1;
 Rewrite (Rplus_assoc r1 (Ropp (IZR (Int_part r1))) 
  (Rplus r2 (Ropp (IZR (Int_part r2))))) in H1;
 Rewrite (Rplus_sym r2 (Ropp (IZR (Int_part r2)))) in H1;
 Rewrite <-(Rplus_assoc (Ropp (IZR (Int_part r1))) (Ropp (IZR (Int_part r2)))
  r2) in H1;
 Rewrite (Rplus_sym 
  (Rplus (Ropp (IZR (Int_part r1))) (Ropp (IZR (Int_part r2)))) r2) in H1;
 Rewrite <-(Rplus_assoc r1 r2 
  (Rplus (Ropp (IZR (Int_part r1))) (Ropp (IZR (Int_part r2))))) in H1;
 Rewrite <-(Ropp_distr1 (IZR (Int_part r1)) (IZR (Int_part r2))) in H1;
 Rewrite (Rplus_assoc r1 (Ropp (IZR (Int_part r1))) 
  (Rplus r2 (Ropp (IZR (Int_part r2))))) in H0;
 Rewrite (Rplus_sym r2 (Ropp (IZR (Int_part r2)))) in H0;
 Rewrite <-(Rplus_assoc (Ropp (IZR (Int_part r1))) (Ropp (IZR (Int_part r2)))
  r2) in H0;
 Rewrite (Rplus_sym 
  (Rplus (Ropp (IZR (Int_part r1))) (Ropp (IZR (Int_part r2)))) r2) in H0;
 Rewrite <-(Rplus_assoc r1 r2 
  (Rplus (Ropp (IZR (Int_part r1))) (Ropp (IZR (Int_part r2))))) in H0;
 Rewrite <-(Ropp_distr1 (IZR (Int_part r1)) (IZR (Int_part r2))) in H0;
 Generalize (Rle_compatibility (Rplus (IZR (Int_part r1)) (IZR (Int_part r2)))
  R1 (Rplus (Rplus r1 r2)
           (Ropp (Rplus (IZR (Int_part r1)) (IZR (Int_part r2))))) H0);Intro;
 Clear H0;
 Generalize (Rlt_compatibility (Rplus (IZR (Int_part r1)) (IZR (Int_part r2)))
  (Rplus (Rplus r1 r2)
   (Ropp (Rplus (IZR (Int_part r1)) (IZR (Int_part r2))))) (Rplus R1 R1) H1);
 Intro;Clear H1;
 Rewrite (Rplus_sym (Rplus r1 r2) 
  (Ropp (Rplus (IZR (Int_part r1)) (IZR (Int_part r2))))) in H;
 Rewrite <-(Rplus_assoc (Rplus (IZR (Int_part r1)) (IZR (Int_part r2)))
  (Ropp (Rplus (IZR (Int_part r1)) (IZR (Int_part r2)))) (Rplus r1 r2)) in H;
 Rewrite (Rplus_Ropp_r (Rplus (IZR (Int_part r1)) (IZR (Int_part r2)))) in H;
 Elim (Rplus_ne (Rplus r1 r2));Intros a b;Rewrite b in H;Clear a b;
 Rewrite (Rplus_sym (Rplus r1 r2) 
  (Ropp (Rplus (IZR (Int_part r1)) (IZR (Int_part r2))))) in H0;
 Rewrite <-(Rplus_assoc (Rplus (IZR (Int_part r1)) (IZR (Int_part r2)))
  (Ropp (Rplus (IZR (Int_part r1)) (IZR (Int_part r2)))) (Rplus r1 r2)) in H0;
 Rewrite (Rplus_Ropp_r (Rplus (IZR (Int_part r1)) (IZR (Int_part r2)))) in H0;
 Elim (Rplus_ne (Rplus r1 r2));Intros a b;Rewrite b in H0;Clear a b;
 Rewrite <-(Rplus_assoc (Rplus (IZR (Int_part r1)) (IZR (Int_part r2))) R1 R1) in 
 H0;Cut R1==(IZR `1`);Auto with zarith real.
Intro;Rewrite H1 in H0;Rewrite H1 in H;Clear H1;
 Rewrite <-(plus_IZR (Int_part r1) (Int_part r2)) in H; 
 Rewrite <-(plus_IZR (Int_part r1) (Int_part r2)) in H0;
 Rewrite <-(plus_IZR `(Int_part r1)+(Int_part r2)` `1`) in H;
 Rewrite <-(plus_IZR `(Int_part r1)+(Int_part r2)` `1`) in H0;
 Rewrite <-(plus_IZR `(Int_part r1)+(Int_part r2)+1` `1`) in H0;
 Generalize (up_tech (Rplus r1 r2) `(Int_part r1)+(Int_part r2)+1` H H0);Intro;
 Clear H H0;Unfold 1 Int_part;Omega.
Qed.

(**********)
Lemma plus_Int_part2:(r1,r2:R)(Rlt (Rplus (frac_part r1) (frac_part r2)) R1)->
  (Int_part (Rplus r1 r2))=(Zplus (Int_part r1) (Int_part r2)).
Intros;Elim (base_fp r1);Elim (base_fp r2);Intros;Clear H1 H3;
 Generalize (Rle_sym2 R0 (frac_part r2) H0);Intro;Clear H0;
 Generalize (Rle_sym2 R0 (frac_part r1) H2);Intro;Clear H2;
 Generalize (Rle_compatibility (frac_part r1) R0 (frac_part r2) H1);
 Intro;Clear H1;Elim (Rplus_ne (frac_part r1));Intros a b;
 Rewrite a in H2;Clear a b;Generalize (Rle_trans R0 (frac_part r1)
  (Rplus (frac_part r1) (frac_part r2)) H0 H2);Intro;Clear H0 H2;
 Unfold frac_part in H H1;Unfold Rminus in H H1;
 Rewrite (Rplus_assoc r1 (Ropp (IZR (Int_part r1))) 
  (Rplus r2 (Ropp (IZR (Int_part r2))))) in H1;
 Rewrite (Rplus_sym r2 (Ropp (IZR (Int_part r2)))) in H1;
 Rewrite <-(Rplus_assoc (Ropp (IZR (Int_part r1))) (Ropp (IZR (Int_part r2)))
  r2) in H1;
 Rewrite (Rplus_sym 
  (Rplus (Ropp (IZR (Int_part r1))) (Ropp (IZR (Int_part r2)))) r2) in H1;
 Rewrite <-(Rplus_assoc r1 r2 
  (Rplus (Ropp (IZR (Int_part r1))) (Ropp (IZR (Int_part r2))))) in H1;
 Rewrite <-(Ropp_distr1 (IZR (Int_part r1)) (IZR (Int_part r2))) in H1;
 Rewrite (Rplus_assoc r1 (Ropp (IZR (Int_part r1))) 
  (Rplus r2 (Ropp (IZR (Int_part r2))))) in H;
 Rewrite (Rplus_sym r2 (Ropp (IZR (Int_part r2)))) in H;
 Rewrite <-(Rplus_assoc (Ropp (IZR (Int_part r1))) (Ropp (IZR (Int_part r2)))
  r2) in H;
 Rewrite (Rplus_sym 
  (Rplus (Ropp (IZR (Int_part r1))) (Ropp (IZR (Int_part r2)))) r2) in H;
 Rewrite <-(Rplus_assoc r1 r2 
  (Rplus (Ropp (IZR (Int_part r1))) (Ropp (IZR (Int_part r2))))) in H;
 Rewrite <-(Ropp_distr1 (IZR (Int_part r1)) (IZR (Int_part r2))) in H;
 Generalize (Rle_compatibility (Rplus (IZR (Int_part r1)) (IZR (Int_part r2)))
  R0 (Rplus (Rplus r1 r2)
           (Ropp (Rplus (IZR (Int_part r1)) (IZR (Int_part r2))))) H1);Intro;
 Clear H1;
 Generalize (Rlt_compatibility (Rplus (IZR (Int_part r1)) (IZR (Int_part r2)))
  (Rplus (Rplus r1 r2)
   (Ropp (Rplus (IZR (Int_part r1)) (IZR (Int_part r2))))) R1 H);
 Intro;Clear H;
 Rewrite (Rplus_sym (Rplus r1 r2) 
  (Ropp (Rplus (IZR (Int_part r1)) (IZR (Int_part r2))))) in H1;
 Rewrite <-(Rplus_assoc (Rplus (IZR (Int_part r1)) (IZR (Int_part r2)))
  (Ropp (Rplus (IZR (Int_part r1)) (IZR (Int_part r2)))) (Rplus r1 r2)) in H1;
 Rewrite (Rplus_Ropp_r (Rplus (IZR (Int_part r1)) (IZR (Int_part r2)))) in H1;
 Elim (Rplus_ne (Rplus r1 r2));Intros a b;Rewrite b in H1;Clear a b;
 Rewrite (Rplus_sym (Rplus r1 r2) 
  (Ropp (Rplus (IZR (Int_part r1)) (IZR (Int_part r2))))) in H0;
 Rewrite <-(Rplus_assoc (Rplus (IZR (Int_part r1)) (IZR (Int_part r2)))
  (Ropp (Rplus (IZR (Int_part r1)) (IZR (Int_part r2)))) (Rplus r1 r2)) in H0;
 Rewrite (Rplus_Ropp_r (Rplus (IZR (Int_part r1)) (IZR (Int_part r2)))) in H0;
 Elim (Rplus_ne (Rplus (IZR (Int_part r1)) (IZR (Int_part r2))));Intros a b;
 Rewrite a in H0;Clear a b;Elim (Rplus_ne (Rplus r1 r2));Intros a b;
 Rewrite b in H0;Clear a b;Cut R1==(IZR `1`);Auto with zarith real.
Intro;Rewrite H in H1;Clear H;
 Rewrite <-(plus_IZR (Int_part r1) (Int_part r2)) in H0;
 Rewrite <-(plus_IZR (Int_part r1) (Int_part r2)) in H1;
 Rewrite <-(plus_IZR `(Int_part r1)+(Int_part r2)` `1`) in H1;
 Generalize (up_tech (Rplus r1 r2) `(Int_part r1)+(Int_part r2)` H0 H1);Intro;
 Clear H0 H1;Unfold 1 Int_part;Omega.
Qed.

(**********)
Lemma plus_frac_part1:(r1,r2:R)
  (Rge (Rplus (frac_part r1) (frac_part r2)) R1)->
                (frac_part (Rplus r1 r2))==
                (Rminus (Rplus (frac_part r1) (frac_part r2)) R1).
Intros;Unfold frac_part;
 Generalize (plus_Int_part1 r1 r2 H);Intro;Rewrite H0;
 Rewrite (plus_IZR `(Int_part r1)+(Int_part r2)` `1`);
 Rewrite (plus_IZR (Int_part r1) (Int_part r2));Simpl;Unfold 3 4 Rminus;
 Rewrite (Rplus_assoc r1 (Ropp (IZR (Int_part r1))) 
  (Rplus r2 (Ropp (IZR (Int_part r2)))));
 Rewrite (Rplus_sym r2 (Ropp (IZR (Int_part r2))));
 Rewrite <-(Rplus_assoc (Ropp (IZR (Int_part r1))) (Ropp (IZR (Int_part r2)))
   r2);
 Rewrite (Rplus_sym 
  (Rplus (Ropp (IZR (Int_part r1))) (Ropp (IZR (Int_part r2)))) r2);
 Rewrite <-(Rplus_assoc r1 r2 
  (Rplus (Ropp (IZR (Int_part r1))) (Ropp (IZR (Int_part r2)))));
 Rewrite <-(Ropp_distr1 (IZR (Int_part r1)) (IZR (Int_part r2)));
 Unfold Rminus;
 Rewrite (Rplus_assoc (Rplus r1 r2) 
  (Ropp (Rplus (IZR (Int_part r1)) (IZR (Int_part r2))))
  (Ropp R1));
 Rewrite <-(Ropp_distr1 (Rplus (IZR (Int_part r1)) (IZR (Int_part r2))) R1);
 Trivial with zarith real.
Qed.

(**********)
Lemma plus_frac_part2:(r1,r2:R)
  (Rlt (Rplus (frac_part r1) (frac_part r2)) R1)->
(frac_part (Rplus r1 r2))==(Rplus (frac_part r1) (frac_part r2)).
Intros;Unfold frac_part;
 Generalize (plus_Int_part2 r1 r2 H);Intro;Rewrite H0;
 Rewrite (plus_IZR (Int_part r1) (Int_part r2));Unfold 2 3 Rminus;
 Rewrite (Rplus_assoc r1 (Ropp (IZR (Int_part r1))) 
  (Rplus r2 (Ropp (IZR (Int_part r2)))));
 Rewrite (Rplus_sym r2 (Ropp (IZR (Int_part r2))));
 Rewrite <-(Rplus_assoc (Ropp (IZR (Int_part r1))) (Ropp (IZR (Int_part r2)))
  r2);
 Rewrite (Rplus_sym 
  (Rplus (Ropp (IZR (Int_part r1))) (Ropp (IZR (Int_part r2)))) r2);
 Rewrite <-(Rplus_assoc r1 r2 
  (Rplus (Ropp (IZR (Int_part r1))) (Ropp (IZR (Int_part r2)))));
 Rewrite <-(Ropp_distr1 (IZR (Int_part r1)) (IZR (Int_part r2)));Unfold Rminus;
 Trivial with zarith real.
Qed.
