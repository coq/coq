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
Require Import QArith.
Require Import Qring.

(* Qsrt has been removed from the library ? *)
Definition Qsrt : ring_theory 0 1 Qplus Qmult Qminus Qopp Qeq.
Proof.
  constructor.
  exact Qplus_0_l.
  exact Qplus_comm.
  exact Qplus_assoc.
  exact Qmult_1_l.
  exact Qmult_comm.
  exact Qmult_assoc.
  exact Qmult_plus_distr_l.
  reflexivity.
  exact Qplus_opp_r.
Qed.


Add Ring Qring : Qsrt.

Lemma Qmult_neutral : forall x , 0 * x == 0.
Proof.
  intros.
  compute.
  reflexivity.
Qed.

(* Is there any qarith database ? *)

Lemma Qsor : SOR 0 1 Qplus Qmult Qminus Qopp Qeq  Qle Qlt.
Proof.
  constructor; intros ; subst ; try (intuition (subst; auto  with qarith)).
  apply Q_Setoid.
  rewrite H ; rewrite H0 ; reflexivity.
  rewrite H ; rewrite H0 ; reflexivity.
  rewrite H ; auto ; reflexivity.
  rewrite <- H ; rewrite <- H0 ; auto.
  rewrite H ; rewrite H0 ; auto.
  rewrite <- H ; rewrite <- H0 ; auto.
  rewrite H ; rewrite  H0 ; auto.
  apply Qsrt.
  apply Qle_refl.
  apply Qle_antisym ; auto.
  eapply Qle_trans ; eauto.
  apply Qlt_le_weak ; auto.
  apply (Qlt_not_eq n m H H0) ; auto.
  destruct (Qle_lt_or_eq _ _ H0) ; auto.
  tauto.
  destruct(Q_dec n m) as [[H1 |H1] | H1 ] ; tauto.
  apply (Qplus_le_compat  p p n m  (Qle_refl p) H).
  generalize (Qmult_lt_compat_r 0 n m H0 H).
  rewrite Qmult_neutral.
  auto.
  compute in H.
  discriminate.
Qed.

Definition Qeq_bool (p q : Q) : bool := Zeq_bool (Qnum p * ' Qden q)%Z  (Qnum q * ' Qden p)%Z.

Definition Qle_bool (x y : Q) : bool := Zle_bool (Qnum x * ' Qden y)%Z (Qnum y * ' Qden x)%Z.

Require ZMicromega.

Lemma Qeq_bool_ok : forall x y, Qeq_bool x y = true -> x == y.
Proof.
  intros.
  unfold Qeq_bool in H.
  unfold Qeq.
  apply (Zeqb_ok  _ _ H).
Qed.


Lemma Qeq_bool_neq : forall x y, Qeq_bool x y = false -> ~ x == y.
Proof.
  unfold Qeq_bool,Qeq.
  red ; intros ; subst.
  rewrite H0 in H.
  apply  (ZMicromega.Zeq_bool_neq _ _ H).
  reflexivity.
Qed.

Lemma Qle_bool_imp_le : forall x y : Q, Qle_bool x y = true -> x <= y.
Proof.
  unfold Qle_bool, Qle.
  intros.
  apply Zle_bool_imp_le ; auto.
Qed.
  



Lemma QSORaddon :
  SORaddon 0 1 Qplus Qmult Qminus Qopp  Qeq  Qle (* ring elements *)
  0 1 Qplus Qmult Qminus Qopp (* coefficients *)
  Qeq_bool Qle_bool
  (fun x => x) (fun x => x) (pow_N 1 Qmult).
Proof.
  constructor.
  constructor ; intros ; try reflexivity.
  apply Qeq_bool_ok ; auto.
  constructor.
  reflexivity.
  intros x y.
  apply Qeq_bool_neq ; auto.
  apply Qle_bool_imp_le.
Qed.


(*Definition Zeval_expr :=  eval_pexpr 0 Zplus Zmult Zminus Zopp  (fun x => x) (fun x => Z_of_N x) (Zpower).*)
Require Import EnvRing.

Fixpoint Qeval_expr (env: PolEnv Q) (e: PExpr Q) : Q :=
  match e with
    | PEc c =>  c
    | PEX j =>  env j
    | PEadd pe1 pe2 => (Qeval_expr env pe1) + (Qeval_expr env pe2)
    | PEsub pe1 pe2 => (Qeval_expr env pe1) - (Qeval_expr env pe2)
    | PEmul pe1 pe2 => (Qeval_expr env pe1) * (Qeval_expr env pe2)
    | PEopp pe1 => - (Qeval_expr env pe1)
    | PEpow pe1 n => Qpower (Qeval_expr env pe1)  (Z_of_N n)
  end.

Lemma Qeval_expr_simpl : forall env e,
  Qeval_expr env e = 
  match e with
    | PEc c =>  c
    | PEX j =>  env j
    | PEadd pe1 pe2 => (Qeval_expr env pe1) + (Qeval_expr env pe2)
    | PEsub pe1 pe2 => (Qeval_expr env pe1) - (Qeval_expr env pe2)
    | PEmul pe1 pe2 => (Qeval_expr env pe1) * (Qeval_expr env pe2)
    | PEopp pe1 => - (Qeval_expr env pe1)
    | PEpow pe1 n => Qpower (Qeval_expr env pe1)  (Z_of_N n)
  end.
Proof.
  destruct e ; reflexivity.
Qed.

Definition Qeval_expr' := eval_pexpr  Qplus Qmult Qminus Qopp (fun x => x) (fun x => x) (pow_N 1 Qmult).

Lemma QNpower : forall r n, r ^ Z_of_N n = pow_N 1 Qmult r n.
Proof.
  destruct n ; reflexivity.
Qed.


Lemma Qeval_expr_compat : forall env e, Qeval_expr env e = Qeval_expr' env e.
Proof.
  induction e ; simpl ; subst ; try congruence.
  rewrite IHe.
  apply QNpower.
Qed.

Definition Qeval_op2 (o : Op2) : Q -> Q -> Prop :=
match o with
| OpEq =>  Qeq
| OpNEq => fun x y  => ~ x == y
| OpLe => Qle
| OpGe => Qge
| OpLt => Qlt
| OpGt => Qgt
end.

Definition Qeval_formula (e:PolEnv Q) (ff : Formula Q) :=
  let (lhs,o,rhs) := ff in Qeval_op2 o (Qeval_expr e lhs) (Qeval_expr e rhs).

Definition Qeval_formula' :=
  eval_formula  Qplus Qmult Qminus Qopp Qeq Qle Qlt (fun x => x) (fun x => x) (pow_N 1 Qmult).

Lemma Qeval_formula_compat : forall env f, Qeval_formula env f <-> Qeval_formula' env f.
Proof.
  intros.
  unfold Qeval_formula.
  destruct f.
  repeat rewrite Qeval_expr_compat.
  unfold Qeval_formula'.
  unfold Qeval_expr'.
  split ; destruct Fop ; simpl; auto.
Qed.



Definition Qeval_nformula :=
  eval_nformula 0 Qplus Qmult Qminus Qopp Qeq Qle Qlt (fun x => x) (fun x => x) (pow_N 1 Qmult).

Definition Qeval_op1 (o : Op1) : Q -> Prop :=
match o with
| Equal => fun x : Q => x == 0
| NonEqual => fun x : Q => ~ x == 0
| Strict => fun x : Q => 0 < x
| NonStrict => fun x : Q => 0 <= x
end.

Lemma Qeval_nformula_simpl : forall env f, Qeval_nformula env f = (let (p, op) := f in Qeval_op1 op (Qeval_expr env p)).
Proof.
  intros.
  destruct f.
  rewrite Qeval_expr_compat.
  reflexivity.
Qed.
  
Lemma Qeval_nformula_dec : forall env d, (Qeval_nformula env d) \/ ~ (Qeval_nformula env d).
Proof.
  exact (fun env d =>eval_nformula_dec Qsor (fun x => x) (fun x => x) (pow_N 1 Qmult) env d).
Qed.

Definition QWitness := ConeMember Q.

Definition QWeakChecker := check_normalised_formulas 0 1 Qplus Qmult Qminus Qopp Qeq_bool Qle_bool.

Require Import List.

Lemma QWeakChecker_sound :   forall (l : list (NFormula Q)) (cm : QWitness),
  QWeakChecker l cm = true ->
  forall env, make_impl (Qeval_nformula env) l False.
Proof.
  intros l cm H.
  intro.
  unfold Qeval_nformula.
  apply (checker_nf_sound Qsor QSORaddon l cm).
  unfold QWeakChecker in H.
  exact H.
Qed.

Require Import Tauto.

Definition QTautoChecker (f : BFormula (Formula Q)) (w: list QWitness)  : bool :=
  @tauto_checker (Formula Q) (NFormula Q) (@cnf_normalise Q) (@cnf_negate Q)  QWitness QWeakChecker f w.

Lemma QTautoChecker_sound : forall f w, QTautoChecker f w = true -> forall env, eval_f  (Qeval_formula env)  f.
Proof.
  intros f w.
  unfold QTautoChecker.
  apply (tauto_checker_sound  Qeval_formula Qeval_nformula).
  apply Qeval_nformula_dec.
  intros. rewrite Qeval_formula_compat. unfold Qeval_formula'. now apply (cnf_normalise_correct Qsor).
  intros. rewrite Qeval_formula_compat. unfold Qeval_formula'. now apply (cnf_negate_correct Qsor).
  intros t w0.
  apply QWeakChecker_sound.
Qed.


