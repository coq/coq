
(*************************************************************)
(*      This file is distributed under the terms of the      *)
(*      GNU Lesser General Public License Version 2.1        *)
(*************************************************************)
(*    Benjamin.Gregoire@inria.fr Laurent.Thery@inria.fr      *)
(*************************************************************)

(**********************************************************************
     QBAux.v

     Auxillary functions & Theorems for Q
 **********************************************************************)

Require Import ZAux.
Require Import QArith.
Require Import Qcanon.

 Theorem Qred_opp: forall q, 
   (Qred (-q) = - (Qred q))%Q.
 intros (x, y); unfold Qred; simpl.
 rewrite Zggcd_opp; case Zggcd; intros p1 (p2, p3); simpl.
 unfold Qopp; auto.
 Qed.

 Theorem Qcompare_red: forall x y,
  Qcompare x y = Qcompare (Qred x) (Qred y).
 intros x y; apply Qcompare_comp; apply Qeq_sym; apply Qred_correct.
 Qed.



 Theorem Qpower_decomp: forall p x y,
  Qpower_positive (x #y) p == x ^ Zpos p # (Z2P ((Zpos y) ^ Zpos p)).
 Proof.
 intros p; elim p; clear p.
   intros p Hrec x y.
      unfold Qmult; simpl; rewrite Hrec.
   rewrite xI_succ_xO; rewrite <- Pplus_diag; rewrite Pplus_one_succ_l.
   repeat rewrite Zpower_pos_is_exp.
   red; unfold Qmult, Qnum, Qden, Zpower.
   repeat rewrite Zpos_mult_morphism.
   repeat rewrite Z2P_correct.
   2: apply ZAux.Zpower_pos_pos; red; auto.
   2: repeat apply Zmult_lt_0_compat; auto;
      apply ZAux.Zpower_pos_pos; red; auto.
   repeat rewrite ZAux.Zpower_pos_1_r; ring.

   intros p Hrec x y.
      unfold Qmult; simpl; rewrite Hrec.
   rewrite <- Pplus_diag.
   repeat rewrite Zpower_pos_is_exp.
   red; unfold Qmult, Qnum, Qden, Zpower.
   repeat rewrite Zpos_mult_morphism.
   repeat rewrite Z2P_correct; try ring.
   apply ZAux.Zpower_pos_pos; red; auto.
   repeat apply Zmult_lt_0_compat; auto;
      apply ZAux.Zpower_pos_pos; red; auto.
 intros x y.
 unfold Qmult; simpl.
 red; simpl; rewrite ZAux.Zpower_pos_1_r; 
   rewrite Zpos_mult_morphism; ring.
 Qed.


 Theorem Qc_decomp: forall (x y: Qc),
    (Qred x = x -> Qred y = y -> (x:Q) = y)-> x = y.
  intros (q, Hq) (q', Hq'); simpl; intros H.
  assert (H1 := H Hq Hq').
  subst q'.
  assert (Hq = Hq'). 
  apply Eqdep_dec.eq_proofs_unicity; auto; intros.
  repeat decide equality.
  congruence.
 Qed.
