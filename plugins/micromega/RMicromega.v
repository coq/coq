(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
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
Require Import Raxioms RIneq Rpow_def DiscrR.
Require Import QArith.
Require Import Qfield.
Require Import Qreals.

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

Notation IQR := Q2R (only parsing).

Lemma Rinv_1 : forall x, x * / 1 = x.
Proof.
  intro.
  rewrite Rinv_1.
  apply Rmult_1_r.
Qed.

Lemma Qeq_true : forall x y, Qeq_bool x y = true -> IQR x = IQR y.
Proof.
  intros.
  now apply Qeq_eqR, Qeq_bool_eq.
Qed.

Lemma Qeq_false : forall x y, Qeq_bool x y = false -> IQR x <> IQR y.
Proof.
  intros.
  apply Qeq_bool_neq in H.
  contradict H.
  now apply eqR_Qeq.
Qed.

Lemma Qle_true : forall x y : Q, Qle_bool x y = true -> IQR x <= IQR y.
Proof.
  intros.
  now apply Qle_Rle, Qle_bool_imp_le.
Qed.

Lemma IQR_0 : IQR 0 = 0.
Proof.
  apply Rmult_0_l.
Qed.

Lemma IQR_1 : IQR 1 = 1.
Proof.
  compute. apply Rinv_1.
Qed.

Lemma IQR_inv_ext : forall x, 
  IQR (/ x) = (if Qeq_bool x 0 then 0 else / IQR x).
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
  IQR nat to_nat pow.
Proof.
  constructor.
  constructor ; intros ; try reflexivity.
  apply IQR_0.
  apply IQR_1.
  apply Q2R_plus.
  apply Q2R_minus.
  apply Q2R_mult.
  apply Q2R_opp.
  apply Qeq_true ; auto.
  apply R_power_theory.
  apply Qeq_false.
  apply Qle_true.
Qed.


(* Syntactic ring coefficients. 
   For computing, we use Q. *)
Inductive Rcst :=
| C0
| C1
| CQ (r : Q)
| CZ (r : Z)
| CPlus (r1 r2 : Rcst)
| CMinus (r1  r2 : Rcst)
| CMult (r1 r2 : Rcst)
| CInv  (r : Rcst)
| COpp  (r : Rcst).


Fixpoint Q_of_Rcst (r : Rcst) : Q :=
  match r with
    | C0 => 0 # 1
    | C1 => 1 # 1
    | CZ z => z # 1
    | CQ q => q
    | CPlus r1 r2 => Qplus (Q_of_Rcst r1) (Q_of_Rcst r2)
    | CMinus r1 r2 => Qminus (Q_of_Rcst r1) (Q_of_Rcst r2)
    | CMult r1 r2  => Qmult (Q_of_Rcst r1) (Q_of_Rcst r2)
    | CInv r        => Qinv (Q_of_Rcst r)
    | COpp r       => Qopp (Q_of_Rcst r)
  end.


Fixpoint R_of_Rcst (r : Rcst) : R :=
  match r with
    | C0 => R0
    | C1 => R1
    | CZ z => IZR z
    | CQ q => IQR q
    | CPlus r1 r2  => (R_of_Rcst r1) + (R_of_Rcst r2)
    | CMinus r1 r2 => (R_of_Rcst r1) - (R_of_Rcst r2)
    | CMult r1 r2  => (R_of_Rcst r1) * (R_of_Rcst r2)
    | CInv r       => 
      if Qeq_bool (Q_of_Rcst r) (0 # 1)
        then R0 
        else Rinv (R_of_Rcst r)
      | COpp r       => - (R_of_Rcst r)
  end.

Lemma Q_of_RcstR : forall c, IQR (Q_of_Rcst c) = R_of_Rcst c.
Proof.
    induction c ; simpl ; try (rewrite <- IHc1 ; rewrite <- IHc2).
    apply IQR_0. 
    apply IQR_1. 
    reflexivity.
    unfold IQR. simpl. rewrite Rinv_1. reflexivity.
    apply Q2R_plus.
    apply Q2R_minus.
    apply Q2R_mult.
    rewrite <- IHc.
    apply IQR_inv_ext.
    rewrite <- IHc.
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
  eval_formula  Rplus Rmult Rminus Ropp (@eq R) Rle Rlt IQR N.to_nat pow .

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
  eval_nformula 0 Rplus Rmult  (@eq R) Rle Rlt IQR.


Lemma Reval_nformula_dec : forall env d, (Qeval_nformula env d) \/ ~ (Qeval_nformula env d).
Proof.
  exact (fun env d =>eval_nformula_dec Rsor IQR env d).
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
  runsat rdeduce
  Rnormalise Rnegate
  RWitness RWeakChecker (map_bformula (map_Formula Q_of_Rcst)  f) w.

Lemma RTautoChecker_sound : forall f w, RTautoChecker f w = true -> forall env, eval_f  (Reval_formula env)  f.
Proof.
  intros f w.
  unfold RTautoChecker.
  intros TC env.
  apply (tauto_checker_sound  QReval_formula Qeval_nformula) with (env := env) in TC.
  rewrite eval_f_map in TC.
  rewrite eval_f_morph with (ev':= Reval_formula env) in TC ; auto.
  intro.
  unfold QReval_formula.
  rewrite <- eval_formulaSC  with (phiS := R_of_Rcst).
  rewrite Reval_formula_compat.
  tauto.
  intro. rewrite Q_of_RcstR. reflexivity.
  apply Reval_nformula_dec.
  destruct t.
  apply (check_inconsistent_sound Rsor QSORaddon) ; auto.
  unfold rdeduce. apply (nformula_plus_nformula_correct Rsor QSORaddon).
  now apply (cnf_normalise_correct Rsor QSORaddon).  
  intros. now apply (cnf_negate_correct Rsor QSORaddon).
  intros t w0.
  apply RWeakChecker_sound.
Qed.



(* Local Variables: *)
(* coding: utf-8 *)
(* End: *)
