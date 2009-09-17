(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
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

Add Ring Rring : Rsrt.
Open Scope R_scope.

Lemma Rmult_neutral : forall x:R , 0 * x = 0.
Proof.
  intro ; ring.
Qed.


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
  intros.
  rewrite <- (Rmult_neutral m).
  apply (Rmult_lt_compat_r) ; auto.
Qed.

Require ZMicromega.
(* R with coeffs in Z *)

Lemma RZSORaddon :
  SORaddon R0 R1 Rplus Rmult Rminus Ropp  (@eq R)  Rle (* ring elements *)
  0%Z 1%Z Zplus Zmult Zminus Zopp (* coefficients *)
  Zeq_bool Zle_bool
  IZR Nnat.nat_of_N pow.
Proof.
  constructor.
  constructor ; intros ; try reflexivity.
  apply plus_IZR.
  symmetry. apply Z_R_minus.
  apply mult_IZR.
  apply Ropp_Ropp_IZR.
  apply IZR_eq.
  apply Zeq_bool_eq ; auto.
  apply R_power_theory.
  intros x y.
  intro.
  apply IZR_neq.
  apply Zeq_bool_neq ; auto.
  intros. apply IZR_le.  apply Zle_bool_imp_le. auto.
Qed.


Require Import EnvRing.

Definition INZ (n:N) : R :=
  match n with
    | N0 => IZR 0%Z
    | Npos p => IZR (Zpos p)
  end.

Definition Reval_expr := eval_pexpr  Rplus Rmult Rminus Ropp IZR Nnat.nat_of_N pow.


Definition Reval_op2 (o:Op2) : R -> R -> Prop :=
    match o with
      | OpEq =>  @eq R
      | OpNEq => fun x y  => ~ x = y
      | OpLe => Rle
      | OpGe => Rge
      | OpLt => Rlt
      | OpGt => Rgt
    end.


Definition Reval_formula (e: PolEnv R) (ff : Formula Z) :=
  let (lhs,o,rhs) := ff in Reval_op2 o (Reval_expr e lhs) (Reval_expr e rhs).

Definition Reval_formula' :=
  eval_formula  Rplus Rmult Rminus Ropp (@eq R) Rle Rlt IZR Nnat.nat_of_N pow.

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

Definition Reval_nformula :=
  eval_nformula 0 Rplus Rmult  (@eq R) Rle Rlt IZR.


Lemma Reval_nformula_dec : forall env d, (Reval_nformula env d) \/ ~ (Reval_nformula env d).
Proof.
  exact (fun env d =>eval_nformula_dec Rsor IZR env d).
Qed.

Definition RWitness := Psatz Z.

Definition RWeakChecker := check_normalised_formulas 0%Z 1%Z Zplus Zmult  Zeq_bool Zle_bool.

Require Import List.

Lemma RWeakChecker_sound :   forall (l : list (NFormula Z)) (cm : RWitness),
  RWeakChecker l cm = true ->
  forall env, make_impl (Reval_nformula env) l False.
Proof.
  intros l cm H.
  intro.
  unfold Reval_nformula.
  apply (checker_nf_sound Rsor RZSORaddon l cm).
  unfold RWeakChecker in H.
  exact H.
Qed.

Require Import Tauto.

Definition Rnormalise := @cnf_normalise Z 0%Z 1%Z Zplus Zmult Zminus Zopp Zeq_bool.
Definition Rnegate := @cnf_negate Z 0%Z 1%Z Zplus Zmult Zminus Zopp Zeq_bool.

Definition RTautoChecker (f : BFormula (Formula Z)) (w: list RWitness)  : bool :=
  @tauto_checker (Formula Z) (NFormula Z)
  Rnormalise Rnegate
  RWitness RWeakChecker f w.

Lemma RTautoChecker_sound : forall f w, RTautoChecker f w = true -> forall env, eval_f  (Reval_formula env)  f.
Proof.
  intros f w.
  unfold RTautoChecker.
  apply (tauto_checker_sound  Reval_formula Reval_nformula).
  apply Reval_nformula_dec.
  intros. rewrite Reval_formula_compat.
  unfold Reval_formula'. now apply (cnf_normalise_correct Rsor RZSORaddon).
  intros. rewrite Reval_formula_compat. unfold Reval_formula. now apply (cnf_negate_correct Rsor RZSORaddon).
  intros t w0.
  apply RWeakChecker_sound.
Qed.


(* Local Variables: *)
(* coding: utf-8 *)
(* End: *)
