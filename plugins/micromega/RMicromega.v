(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
(*                                                                      *)
(* Micromega: A reflexive tactic using the Positivstellensatz           *)
(*                                                                      *)
(*  Frédéric Besson (Irisa/Inria) 2006-2008                             *)
(*                                                                      *)
(************************************************************************)

Require Import OrderedRing.
Require Import RingMicromega.
Require Import Refl.
Require Import Raxioms Rfunctions RIneq Rpow_def DiscrR.
Require Import QArith.
Require Import Qfield.
Require Import Qreals.
Require Import DeclConstant.

Require Setoid.
(*Declare ML Module "micromega_plugin".*)

Definition Rsrt : ring_theory R0 R1 Rplus Rmult Rminus Ropp (@eq R).
Proof.
  constructor.
  exact Rplus_0_l.
  exact Rplus_comm.
  intros. rewrite Rplus_assoc. auto.
  exact Rmult_1_l.
  exact Rmult_comm.
  intros ; rewrite Rmult_assoc ; auto.
  intros. rewrite Rmult_comm. rewrite Rmult_plus_distr_l.
   rewrite (Rmult_comm z).    rewrite (Rmult_comm z). auto.
  reflexivity.
  exact Rplus_opp_r.
Qed.

Open Scope R_scope.

Lemma Rsor : SOR R0 R1 Rplus Rmult Rminus Ropp (@eq R)  Rle Rlt.
Proof.
  constructor; intros ; subst ; try (intuition (subst; try ring ; auto with real)).
  constructor.
  constructor.
  unfold RelationClasses.Symmetric. auto.
  unfold RelationClasses.Transitive. intros. subst. reflexivity.
  apply Rsrt.
  eapply Rle_trans ; eauto.
  apply (Rlt_irrefl m) ; auto.
  apply Rnot_le_lt. auto with real.
  destruct (total_order_T n m) as [ [H1 | H1] | H1] ; auto.
  now apply Rmult_lt_0_compat.
Qed.

Lemma Rinv_1 : forall x, x * / 1 = x.
Proof.
  intro.
  rewrite Rinv_1.
  apply Rmult_1_r.
Qed.

Lemma Qeq_true : forall x y, Qeq_bool x y = true -> Q2R x = Q2R y.
Proof.
  intros.
  now apply Qeq_eqR, Qeq_bool_eq.
Qed.

Lemma Qeq_false : forall x y, Qeq_bool x y = false -> Q2R x <> Q2R y.
Proof.
  intros.
  apply Qeq_bool_neq in H.
  contradict H.
  now apply eqR_Qeq.
Qed.

Lemma Qle_true : forall x y : Q, Qle_bool x y = true -> Q2R x <= Q2R y.
Proof.
  intros.
  now apply Qle_Rle, Qle_bool_imp_le.
Qed.

Lemma Q2R_0 : Q2R 0 = 0.
Proof.
  apply Rmult_0_l.
Qed.

Lemma Q2R_1 : Q2R 1 = 1.
Proof.
  compute. apply Rinv_1.
Qed.

Lemma Q2R_inv_ext : forall x,
  Q2R (/ x) = (if Qeq_bool x 0 then 0 else / Q2R x).
Proof.
  intros.
  case_eq (Qeq_bool x 0).
  intros.
  apply Qeq_bool_eq in H.
  destruct x ; simpl.
  unfold Qeq in H.
  simpl in H.
  rewrite Zmult_1_r in H.
  rewrite H.
  apply Rmult_0_l.
  intros.
  now apply Q2R_inv, Qeq_bool_neq.
Qed.

Notation to_nat := N.to_nat.

Lemma QSORaddon :
  @SORaddon R
  R0 R1 Rplus Rmult Rminus Ropp  (@eq R)  Rle (* ring elements *)
  Q 0%Q 1%Q Qplus Qmult Qminus Qopp (* coefficients *)
  Qeq_bool Qle_bool
  Q2R nat to_nat pow.
Proof.
  constructor.
  constructor ; intros ; try reflexivity.
  apply Q2R_0.
  apply Q2R_1.
  apply Q2R_plus.
  apply Q2R_minus.
  apply Q2R_mult.
  apply Q2R_opp.
  apply Qeq_true ; auto.
  apply R_power_theory.
  apply Qeq_false.
  apply Qle_true.
Qed.

(* Syntactic ring coefficients. *)

Inductive Rcst :=
  | C0
  | C1
  | CQ (r : Q)
  | CZ (r : Z)
  | CPlus (r1 r2 : Rcst)
  | CMinus (r1  r2 : Rcst)
  | CMult (r1 r2 : Rcst)
  | CPow  (r1 : Rcst) (z:Z+nat)
  | CInv  (r : Rcst)
  | COpp  (r : Rcst).



Definition z_of_exp (z : Z + nat) :=
  match z with
  | inl z => z
  | inr n => Z.of_nat n
  end.

Fixpoint Q_of_Rcst (r : Rcst) : Q :=
  match r with
    | C0 => 0 # 1
    | C1 => 1 # 1
    | CZ z => z # 1
    | CQ q => q
    | CPlus r1 r2 => Qplus (Q_of_Rcst r1) (Q_of_Rcst r2)
    | CMinus r1 r2 => Qminus (Q_of_Rcst r1) (Q_of_Rcst r2)
    | CMult r1 r2  => Qmult (Q_of_Rcst r1) (Q_of_Rcst r2)
    | CPow  r1 z   => Qpower (Q_of_Rcst r1) (z_of_exp z)
    | CInv r       => Qinv (Q_of_Rcst r)
    | COpp r       => Qopp (Q_of_Rcst r)
  end.


Definition is_neg (z: Z+nat) :=
  match z with
  | inl (Zneg _) => true
  |  _           => false
  end.

Lemma is_neg_true : forall z, is_neg z = true -> (z_of_exp z < 0)%Z.
Proof.
  destruct z ; simpl ; try congruence.
  destruct z ; try congruence.
  intros.
  reflexivity.
Qed.

Lemma is_neg_false : forall z, is_neg z = false -> (z_of_exp z >= 0)%Z.
Proof.
  destruct z ; simpl ; try congruence.
  destruct z ; try congruence.
  compute. congruence.
  compute. congruence.
  generalize (Zle_0_nat n). auto with zarith.
Qed.

Definition CInvR0 (r : Rcst) := Qeq_bool (Q_of_Rcst r) (0 # 1).

Definition CPowR0 (z : Z) (r : Rcst) :=
  Z.ltb z Z0 && Qeq_bool (Q_of_Rcst r) (0 # 1).

Fixpoint R_of_Rcst (r : Rcst) : R :=
  match r with
    | C0 => R0
    | C1 => R1
    | CZ z => IZR z
    | CQ q => Q2R q
    | CPlus r1 r2  => (R_of_Rcst r1) + (R_of_Rcst r2)
    | CMinus r1 r2 => (R_of_Rcst r1) - (R_of_Rcst r2)
    | CMult r1 r2  => (R_of_Rcst r1) * (R_of_Rcst r2)
    | CPow r1 z    =>
      match z with
      | inl z =>
        if CPowR0 z r1
        then R0
        else  powerRZ (R_of_Rcst r1) z
      | inr n => pow (R_of_Rcst r1) n
      end
    | CInv r       => 
      if CInvR0 r then R0
      else Rinv (R_of_Rcst r)
    | COpp r       => - (R_of_Rcst r)
  end.

Add Morphism Q2R with signature Qeq ==> @eq R as Q2R_m.
  exact Qeq_eqR.
Qed.

Lemma Q2R_pow_pos : forall q p,
    Q2R (pow_pos Qmult q p) = pow_pos Rmult (Q2R q) p.
Proof.
  induction p ; simpl;auto;
    rewrite <- IHp;
    repeat rewrite Q2R_mult;
    reflexivity.
Qed.

Lemma Q2R_pow_N : forall q n,
  Q2R (pow_N 1%Q Qmult q n) = pow_N 1 Rmult (Q2R q) n.
Proof.
  destruct n ; simpl.
  - apply Q2R_1.
  - apply Q2R_pow_pos.
Qed.

Lemma Qmult_integral : forall q r, q * r ==  0 -> q == 0 \/ r == 0.
Proof.
  intros.
  destruct (Qeq_dec q 0)%Q.
  - left ; apply q0.
  - apply Qmult_integral_l in H ; tauto.
Qed.

Lemma Qpower_positive_eq_zero : forall q p,
    Qpower_positive q p == 0 -> q == 0.
Proof.
  unfold Qpower_positive.
  induction p ; simpl; intros;
    repeat match goal with
    | H : _ * _ == 0 |- _ =>
      apply Qmult_integral in H; destruct H
    end; tauto.
Qed.

Lemma Qpower_positive_zero : forall p,
    Qpower_positive 0 p == 0%Q.
Proof.
  induction p ; simpl;
    try rewrite IHp ; reflexivity.
Qed.


Lemma Q2RpowerRZ :
  forall q z
         (DEF : not (q == 0)%Q \/ (z >= Z0)%Z),
    Q2R (q ^ z) = powerRZ (Q2R q) z.
Proof.
  intros.
  destruct Qpower_theory.
  destruct R_power_theory.
  unfold Qpower, powerRZ.
  destruct z.
  - apply Q2R_1.
  -
    change (Qpower_positive q p)
          with (Qpower q (Zpos p)).
    rewrite <- N2Z.inj_pos.
    rewrite <- positive_N_nat.
    rewrite rpow_pow_N.
    rewrite rpow_pow_N0.
    apply Q2R_pow_N.
  -
    rewrite  Q2R_inv.
    unfold Qpower_positive.
    rewrite <- positive_N_nat.
    rewrite rpow_pow_N0.
    unfold pow_N.
    rewrite Q2R_pow_pos.
    auto.
    intro.
    apply Qpower_positive_eq_zero in H.
    destruct DEF ; auto with arith.
Qed.

Lemma Qpower0 : forall z, (z <> 0)%Z -> (0 ^ z == 0)%Q.
Proof.
  unfold Qpower.
  destruct z;intros.
  - congruence.
  - apply Qpower_positive_zero.
  - rewrite Qpower_positive_zero.
    reflexivity.
Qed.


Lemma Q_of_RcstR : forall c, Q2R (Q_of_Rcst c) = R_of_Rcst c.
Proof.
  induction c ; simpl ; try (rewrite <- IHc1 ; rewrite <- IHc2).
  - apply Q2R_0.
  - apply Q2R_1.
  - reflexivity.
  - unfold Q2R. simpl. rewrite Rinv_1. reflexivity.
  - apply Q2R_plus.
  - apply Q2R_minus.
  - apply Q2R_mult.
  - destruct z.
    destruct (CPowR0 z c) eqn:C; unfold CPowR0 in C.
    +
      rewrite andb_true_iff in C.
      destruct C as (C1 & C2).
      rewrite Z.ltb_lt in C1.
      apply Qeq_bool_eq in C2.
      rewrite C2.
      simpl.
      rewrite Qpower0 by auto with zarith.
      apply Q2R_0.
    + rewrite Q2RpowerRZ.
      rewrite IHc.
      reflexivity.
      rewrite andb_false_iff in C.
      destruct C.
      simpl. apply Z.ltb_ge in H.
      auto with zarith.
      left ; apply Qeq_bool_neq; auto.
    + simpl.
      rewrite <- IHc.
      destruct Qpower_theory.
      rewrite <- nat_N_Z.
      rewrite rpow_pow_N.
      destruct R_power_theory.
      rewrite <- (Nnat.Nat2N.id n) at 2.
      rewrite rpow_pow_N0.
      apply Q2R_pow_N.
  - rewrite <- IHc.
    unfold CInvR0.
    apply Q2R_inv_ext.
  - rewrite <- IHc.
    apply Q2R_opp.
Qed.

Require Import EnvRing.

Definition INZ (n:N) : R :=
  match n with
    | N0 => IZR 0%Z
    | Npos p => IZR (Zpos p)
  end.

Definition Reval_expr := eval_pexpr  Rplus Rmult Rminus Ropp R_of_Rcst N.to_nat pow.


Definition Reval_op2 (o:Op2) : R -> R -> Prop :=
    match o with
      | OpEq =>  @eq R
      | OpNEq => fun x y  => ~ x = y
      | OpLe => Rle
      | OpGe => Rge
      | OpLt => Rlt
      | OpGt => Rgt
    end.


Definition Reval_formula (e: PolEnv R) (ff : Formula Rcst) :=
  let (lhs,o,rhs) := ff in Reval_op2 o (Reval_expr e lhs) (Reval_expr e rhs).


Definition Reval_formula' :=
  eval_sformula  Rplus Rmult Rminus Ropp (@eq R) Rle Rlt N.to_nat pow R_of_Rcst.

Definition QReval_formula := 
  eval_formula  Rplus Rmult Rminus Ropp (@eq R) Rle Rlt Q2R N.to_nat pow .

Lemma Reval_formula_compat : forall env f, Reval_formula env f <-> Reval_formula' env f.
Proof.
  intros.
  unfold Reval_formula.
  destruct f.
  unfold Reval_formula'.
  unfold Reval_expr.
  split ; destruct Fop ; simpl ; auto.
  apply Rge_le.
  apply Rle_ge.
Qed.

Definition Qeval_nformula :=
  eval_nformula 0 Rplus Rmult  (@eq R) Rle Rlt Q2R.


Lemma Reval_nformula_dec : forall env d, (Qeval_nformula env d) \/ ~ (Qeval_nformula env d).
Proof.
  exact (fun env d =>eval_nformula_dec Rsor Q2R env d).
Qed.

Definition RWitness := Psatz Q.

Definition RWeakChecker := check_normalised_formulas 0%Q 1%Q Qplus Qmult  Qeq_bool Qle_bool.

Require Import List.

Lemma RWeakChecker_sound :   forall (l : list (NFormula Q)) (cm : RWitness),
  RWeakChecker l cm = true ->
  forall env, make_impl (Qeval_nformula env) l False.
Proof.
  intros l cm H.
  intro.
  unfold Qeval_nformula.
  apply (checker_nf_sound Rsor QSORaddon l cm).
  unfold RWeakChecker in H.
  exact H.
Qed.

Require Import Coq.micromega.Tauto.

Definition Rnormalise := @cnf_normalise Q 0%Q 1%Q Qplus Qmult Qminus Qopp Qeq_bool.
Definition Rnegate := @cnf_negate Q 0%Q 1%Q Qplus Qmult Qminus Qopp Qeq_bool.

Definition runsat := check_inconsistent 0%Q Qeq_bool Qle_bool.

Definition rdeduce := nformula_plus_nformula 0%Q Qplus Qeq_bool.

Definition RTautoChecker (f : BFormula (Formula Rcst)) (w: list RWitness)  : bool :=
  @tauto_checker (Formula Q) (NFormula Q)
  unit runsat rdeduce
  (Rnormalise unit) (Rnegate unit)
  RWitness (fun cl => RWeakChecker (List.map fst cl)) (map_bformula (map_Formula Q_of_Rcst)  f) w.

Lemma RTautoChecker_sound : forall f w, RTautoChecker f w = true -> forall env, eval_bf  (Reval_formula env)  f.
Proof.
  intros f w.
  unfold RTautoChecker.
  intros TC env.
  apply tauto_checker_sound with (eval:=QReval_formula) (eval':=    Qeval_nformula) (env := env) in TC.
  - change (eval_f (fun x : Prop => x) (QReval_formula env))
      with
        (eval_bf  (QReval_formula env)) in TC.
    rewrite eval_bf_map in TC.
    unfold eval_bf in TC.
    rewrite eval_f_morph with (ev':= Reval_formula env) in TC ; auto.
  intro.
  unfold QReval_formula.
  rewrite <- eval_formulaSC  with (phiS := R_of_Rcst).
  rewrite Reval_formula_compat.
  tauto.
  intro. rewrite Q_of_RcstR. reflexivity.
  -
  apply Reval_nformula_dec.
  - destruct t.
  apply (check_inconsistent_sound Rsor QSORaddon) ; auto.
  - unfold rdeduce. apply (nformula_plus_nformula_correct Rsor QSORaddon).
  - now apply (cnf_normalise_correct Rsor QSORaddon).
  - intros. now eapply (cnf_negate_correct Rsor QSORaddon); eauto.
  - intros t w0.
    unfold eval_tt.
    intros.
    rewrite make_impl_map with (eval := Qeval_nformula env0).
    eapply RWeakChecker_sound; eauto.
    tauto.
Qed.



(* Local Variables: *)
(* coding: utf-8 *)
(* End: *)
