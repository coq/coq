Require Import Raxioms.
Require Import Rdefinitions.
Require Import Ring Field.

Open Local Scope R_scope.

Lemma RTheory : ring_theory 0 1 Rplus Rmult Rminus Ropp (eq (A:=R)).
Proof.
constructor.
 intro; apply Rplus_0_l.
 exact Rplus_comm.
 symmetry  in |- *; apply Rplus_assoc.
 intro; apply Rmult_1_l.
 exact Rmult_comm.
 symmetry  in |- *; apply Rmult_assoc.
 intros m n p.
   rewrite Rmult_comm in |- *.
   rewrite (Rmult_comm n p) in |- *.
   rewrite (Rmult_comm m p) in |- *.
   apply Rmult_plus_distr_l.
 reflexivity.
 exact Rplus_opp_r.
Qed.

Lemma Rfield : field_theory 0 1 Rplus Rmult Rminus Ropp Rdiv Rinv (eq(A:=R)).
Proof.
constructor.
 exact RTheory.
 exact R1_neq_R0.
 reflexivity.
 exact Rinv_l.
Qed.

Lemma Rlt_n_Sn : forall x, x < x + 1.
Proof.
intro.
elim archimed with x; intros.
destruct H0.
 apply Rlt_trans with (IZR (up x)); trivial.
    replace (IZR (up x)) with (x + (IZR (up x) - x))%R.
  apply Rplus_lt_compat_l; trivial.
  unfold Rminus in |- *.
    rewrite (Rplus_comm (IZR (up x)) (- x)) in |- *.
    rewrite <- Rplus_assoc in |- *.
    rewrite Rplus_opp_r in |- *.
    apply Rplus_0_l.
 elim H0.
   unfold Rminus in |- *.
   rewrite (Rplus_comm (IZR (up x)) (- x)) in |- *.
   rewrite <- Rplus_assoc in |- *.
   rewrite Rplus_opp_r in |- *.
   rewrite Rplus_0_l in |- *; trivial.
Qed.

Notation Rset := (Eqsth R).
Notation Rext := (Eq_ext Rplus Rmult Ropp).

Lemma Rlt_0_2 : 0 < 2.
apply Rlt_trans with (0 + 1).
 apply Rlt_n_Sn.
 rewrite Rplus_comm in |- *.
   apply Rplus_lt_compat_l.
    replace 1 with (0 + 1).
  apply Rlt_n_Sn.
  apply Rplus_0_l.
Qed.

Lemma Rgen_phiPOS : forall x, InitialRing.gen_phiPOS1 1 Rplus Rmult x > 0.
unfold Rgt in |- *.
induction x; simpl in |- *; intros.
 apply Rlt_trans with (1 + 0).
  rewrite Rplus_comm in |- *.
    apply Rlt_n_Sn.
  apply Rplus_lt_compat_l.
    rewrite <- (Rmul_0_l Rset Rext RTheory 2) in |- *.
    rewrite Rmult_comm in |- *.
    apply Rmult_lt_compat_l.
   apply Rlt_0_2.
   trivial.
 rewrite <- (Rmul_0_l Rset Rext RTheory 2) in |- *.
   rewrite Rmult_comm in |- *.
   apply Rmult_lt_compat_l.
  apply Rlt_0_2.
  trivial.
  replace 1 with (0 + 1).
  apply Rlt_n_Sn.
  apply Rplus_0_l.
Qed.


Lemma Rgen_phiPOS_not_0 :
  forall x, InitialRing.gen_phiPOS1 1 Rplus Rmult x <> 0.
red in |- *; intros.
specialize (Rgen_phiPOS x).
rewrite H in |- *; intro.
apply (Rlt_asym 0 0); trivial.
Qed.

Lemma Zeq_bool_complete : forall x y, 
  InitialRing.gen_phiZ 0%R 1%R Rplus Rmult Ropp x =
  InitialRing.gen_phiZ 0%R 1%R Rplus Rmult Ropp y ->
  Zeq_bool x y = true.
Proof gen_phiZ_complete Rset Rext Rfield Rgen_phiPOS_not_0.

Add Field RField : Rfield (infinite Zeq_bool_complete).
