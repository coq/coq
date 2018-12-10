(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import QArith Qabs.
Require Import ConstructiveCauchyReals.
Require Import ConstructiveCauchyRealsMult.
Require Import ConstructiveRcomplete.
Require Export ConstructiveAbs.

(**
   The classical Cauchy real numbers. Those are the constructive Cauchy
   real numbers together with the 2 classical logical axioms
   sig_forall_dec and sig_not_dec. Because the type CReal is the same,
   any theorem proved constructively (without axioms) is a fortiori proved
   for those classical reals.

   The 2 classical axioms give us a total order and a total division
   operation, which are simpler to use than the linear order and partial
   division (that requires a proof that the denominator is not zero).
   In particular, the total division enables the field tactic.
   However on CReal we do not have the Leibniz equality when 2 rational
   Cauchy sequences converge towards each other. CReal remains a setoid.
   To get Leiniz equality, one can use the classical Dedekind reals,
   cf file ClassicalDedekindReals.v. Those use another classical axiom
   (functional extensionality) and require extra proofs of quotients to
   transport constructive theorems.
*)

(* The limited principle of omniscience *)
Axiom sig_forall_dec
  : forall (P : nat -> Prop),
    (forall n, {P n} + {~P n})
    -> {n | ~P n} + {forall n, P n}.

Axiom sig_not_dec : forall P : Prop, { ~~P } + { ~P }.

Local Open Scope CReal_scope.

Lemma total_order_T : forall r1 r2:CReal, (r1 < r2) + (r1 == r2) + (r2 < r1).
Proof.
  intros. destruct (CRealLt_lpo_dec r1 r2 sig_forall_dec).
  - left. left. exact c.
  - destruct (CRealLt_lpo_dec r2 r1 sig_forall_dec).
    + right. exact c.
    + left. right. split; assumption.
Qed.

Lemma CReal_eq_appart_dec : forall x y : CReal,
    (x == y) + (x # y).
Proof.
  intros. destruct (total_order_T x y). destruct s.
  - right. left. exact c.
  - left. exact c.
  - right. right. exact c.
Qed.

Definition CReal_inv_total (x : CReal) : CReal
  := match CReal_eq_appart_dec x 0 with
     | inl _ => 0 (* / 0 is undefined, we take 0 arbitrarily *)
     | inr r => CReal_inv x r
     end.

Notation "// x" := (CReal_inv_total x) (at level 35, right associativity) : CReal_scope.

Add Parametric Morphism : CReal_inv_total
    with signature CRealEq ==> CRealEq
      as CReal_inv_total_morph.
Proof.
  intros. unfold CReal_inv_total.
  destruct (CReal_eq_appart_dec x 0), (CReal_eq_appart_dec y 0).
  reflexivity. exfalso. rewrite c in H. destruct H. destruct c0; contradiction.
  rewrite c0 in H. destruct H. destruct c; contradiction.
  apply Rinv_eq_compat, H.
Qed.

Lemma CReal_isField : field_theory 0 1
                                 CReal_plus CReal_mult
                                 CReal_minus CReal_opp
                                 (fun x y : CReal => x * (// y))
                                 CReal_inv_total CRealEq.
Proof.
  split.
  - exact CReal_isRing.
  - intros [H H0]. apply H0, CRealLt_0_1.
  - reflexivity.
  - intros. unfold CReal_inv_total.
    destruct (CReal_eq_appart_dec p 0). contradiction.
    apply CReal_inv_l.
Qed.

Add Field RField : CReal_isField.
