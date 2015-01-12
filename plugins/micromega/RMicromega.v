(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
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
Require Import QArith.
Require Import Qfield.


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

Definition IQR := fun x : Q => (IZR (Qnum x) * / IZR (' Qden x))%R.


Lemma Rinv_elim : forall x y z, 
  y <> 0 -> (z * y = x <->   x * / y = z).
Proof.
  intros.
  split ; intros.
  subst.
  rewrite Rmult_assoc.
  rewrite Rinv_r; auto.
  ring.
  subst.
  rewrite Rmult_assoc.
  rewrite (Rmult_comm (/ y)).
  rewrite Rinv_r ; auto.
  ring.
Qed.  

Ltac INR_nat_of_P :=
  match goal with
    | H : context[INR (Pos.to_nat ?X)] |- _ =>
      revert H ; 
      let HH := fresh in
        assert (HH := pos_INR_nat_of_P X) ; revert HH ; generalize (INR (Pos.to_nat X))
    | |- context[INR (Pos.to_nat ?X)] =>
      let HH := fresh in
        assert (HH := pos_INR_nat_of_P X) ; revert HH ; generalize (INR (Pos.to_nat X))
  end.

Ltac add_eq expr val := set (temp := expr) ; 
  generalize (eq_refl temp) ;
    unfold temp at 1 ; generalize temp ; intro val ; clear temp.

Ltac Rinv_elim :=
  match goal with
    | |- context[?x * / ?y] => 
      let z := fresh "v" in 
      add_eq (x * / y) z  ;
      let H := fresh in intro H ; rewrite <- Rinv_elim in H
  end.

Lemma Rlt_neq : forall r , 0 < r -> r <> 0.
Proof.
  red. intros.
  subst.
  apply (Rlt_irrefl 0 H).  
Qed.


Lemma Rinv_1 : forall x, x * / 1 = x.
Proof.
  intro.
  Rinv_elim.
  subst ; ring.
  apply R1_neq_R0.
Qed.

Lemma Qeq_true : forall x y,  
  Qeq_bool x y = true -> 
   IQR x = IQR y.
Proof.
  unfold IQR.
  simpl.
  intros.
  apply Qeq_bool_eq in H.
  unfold Qeq in H.
  assert (IZR (Qnum x * ' Qden y) = IZR (Qnum y * ' Qden x))%Z.
     rewrite H. reflexivity.
  repeat rewrite mult_IZR in H0.
  simpl in H0.
  revert H0.
  repeat INR_nat_of_P.
  intros.
  apply Rinv_elim in H2 ; [| apply Rlt_neq ; auto].
  rewrite <- H2.
  field.
  split ; apply Rlt_neq ; auto.
Qed.

Lemma Qeq_false : forall x y, Qeq_bool x y = false -> IQR x <> IQR y.
Proof.
  intros.
  apply Qeq_bool_neq  in H.
  intro. apply H.   clear H.
  unfold Qeq,IQR in *.
  simpl in *.
  revert H0.
  repeat Rinv_elim.
  intros.
  subst.
  assert (IZR (Qnum x * ' Qden y)%Z = IZR (Qnum y * ' Qden x)%Z).
  repeat rewrite mult_IZR.  
  simpl.
  rewrite <- H0. rewrite <- H.
  ring.
  apply eq_IZR ; auto.
  INR_nat_of_P; intros; apply Rlt_neq ; auto. 
  INR_nat_of_P; intros ; apply Rlt_neq ; auto. 
Qed.

  

Lemma Qle_true : forall x y : Q, Qle_bool x y = true -> IQR x <= IQR y.
Proof.
  intros.
  apply Qle_bool_imp_le in H.
  unfold Qle in H.
  unfold IQR.
  simpl in *.
  apply IZR_le in H.
  repeat rewrite mult_IZR in H.
  simpl in H.
  repeat INR_nat_of_P; intros.
  assert (Hr := Rlt_neq r H).
  assert (Hr0 := Rlt_neq r0 H0).
  replace (IZR (Qnum x) * / r) with ((IZR (Qnum x) * r0) * (/r * /r0)).
  replace (IZR (Qnum y) * / r0) with ((IZR (Qnum y) * r) * (/r * /r0)).
  apply Rmult_le_compat_r ; auto.
  apply Rmult_le_pos.
  unfold Rle. left. apply Rinv_0_lt_compat ; auto.
  unfold Rle. left. apply Rinv_0_lt_compat ; auto.
  field ; intuition.
  field ; intuition.
Qed.



Lemma IQR_0 : IQR 0 = 0.
Proof.
  compute. apply Rinv_1.
Qed.

Lemma IQR_1 : IQR 1 = 1.
Proof.
  compute. apply Rinv_1.
Qed.

Lemma IQR_plus : forall x y, IQR (x + y) = IQR x + IQR y.
Proof.
  intros.
  unfold IQR.
  simpl in *.
  rewrite plus_IZR in *.
  rewrite mult_IZR in *.
  simpl.  
  rewrite Pos2Nat.inj_mul.
  rewrite mult_INR.
  rewrite mult_IZR.
  simpl.
  repeat INR_nat_of_P.
  intros. field. 
  split ; apply Rlt_neq ; auto.
Qed.

Lemma IQR_opp : forall x, IQR (- x) = - IQR x.
Proof.
  intros.
  unfold IQR.
  simpl.
  rewrite opp_IZR.
  ring.  
Qed.

Lemma IQR_minus : forall x y, IQR (x - y) = IQR x - IQR y.
Proof.
  intros.
  unfold Qminus.
  rewrite IQR_plus.
  rewrite IQR_opp.
  ring.
Qed.


Lemma IQR_mult : forall x y, IQR (x * y) = IQR x * IQR y.
Proof.
  unfold IQR ; intros.
  simpl.
  repeat rewrite mult_IZR.
  rewrite Pos2Nat.inj_mul.
  rewrite mult_INR.
  repeat INR_nat_of_P.
  intros. field ; split ; apply Rlt_neq ; auto.
Qed.

Lemma IQR_inv_lt : forall x, (0 < x)%Q -> 
  IQR (/ x) =  / IQR x.
Proof.
  unfold IQR ; simpl.
  intros.
  unfold Qlt in H.
  revert H.
  simpl.
  intros.
  unfold Qinv.
  destruct x.
  destruct Qnum ; simpl in *.
  exfalso. auto with zarith.
  clear H.
  repeat INR_nat_of_P.
  intros.
  assert (HH := Rlt_neq _ H).
  assert (HH0 := Rlt_neq _ H0).
  rewrite Rinv_mult_distr ; auto.
  rewrite Rinv_involutive ; auto.
  ring.
  apply Rinv_0_lt_compat in H0.
  apply Rlt_neq ; auto.
  simpl in H.
  exfalso.
  rewrite Pos.mul_comm  in H.
  compute in H.
  discriminate.
Qed.

Lemma Qinv_opp : forall x, (- (/ x) = / ( -x))%Q.
Proof.
  destruct x ; destruct Qnum ; reflexivity.
Qed.

Lemma Qopp_involutive_strong : forall x, (- - x = x)%Q.
Proof.
  intros.
  destruct x.
  unfold Qopp.
  simpl.
  rewrite Z.opp_involutive.
  reflexivity.
Qed.

Lemma Ropp_0 : forall r , - r = 0 -> r = 0.
Proof.
  intros.
  rewrite <- (Ropp_involutive r).
  apply Ropp_eq_0_compat ; auto.
Qed.

Lemma IQR_x_0 : forall x, IQR x = 0 -> x == 0%Q.
Proof.
  destruct x ; simpl.
  unfold IQR.
  simpl.
  INR_nat_of_P.
  intros.
  apply Rmult_integral in H0.  
  destruct H0.
  apply eq_IZR_R0 in H0.
  subst.
  reflexivity.
  exfalso.
  apply Rinv_0_lt_compat in H.
  rewrite <- H0 in H.
  apply Rlt_irrefl in H. auto.
Qed.
  

Lemma IQR_inv_gt : forall x, (0 > x)%Q -> 
  IQR (/ x) =  / IQR x.
Proof.
  intros.
  rewrite <- (Qopp_involutive_strong x).
  rewrite <- Qinv_opp.
  rewrite IQR_opp.
  rewrite IQR_inv_lt.
  repeat rewrite IQR_opp.
  rewrite Ropp_inv_permute.
  auto.
  intro.
  apply Ropp_0 in H0.
  apply IQR_x_0 in H0.
  rewrite H0 in H.
  compute in H. discriminate.
  unfold Qlt in *.
  destruct x ; simpl in *.
  auto with zarith.
Qed.

Lemma IQR_inv : forall x, ~ x ==  0 -> 
  IQR (/ x) =  / IQR x.
Proof.
  intros.
  assert ( 0 > x \/ 0 < x)%Q.
   destruct x ; unfold Qlt, Qeq in * ; simpl in *.
   rewrite Z.mul_1_r in *.
   destruct Qnum ; simpl in * ; intuition auto.
   right. reflexivity.
   left ; reflexivity.
  destruct H0.
  apply IQR_inv_gt ; auto.
  apply IQR_inv_lt ; auto.
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
  replace Qnum with 0%Z.
  compute. rewrite Rinv_1.
  reflexivity.
  rewrite <- H. ring.
  intros.
  apply IQR_inv.
  intro.
  rewrite <- Qeq_bool_iff in H0.
  congruence.
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
  apply IQR_plus.
  apply IQR_minus.
  apply IQR_mult.
  apply IQR_opp.
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
    apply IQR_plus.
    apply IQR_minus.
    apply IQR_mult.
    rewrite <- IHc.
    apply IQR_inv_ext.
    rewrite <- IHc.
    apply IQR_opp.
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

Require Import Tauto.

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
