(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
(*                      Evgeny Makarov, INRIA, 2007                     *)
(************************************************************************)

Require Import NZAxioms.

Module Type NZBaseProp (Import NZ : NZDomainSig').

Include BackportEq NZ NZ. (** eq_refl, eq_sym, eq_trans *)

Lemma eq_sym_iff : forall x y, x==y <-> y==x.
Proof.
intros; split; symmetry; auto.
Qed.

(* TODO: how register ~= (which is just a notation) as a Symmetric relation,
    hence allowing "symmetry" tac ? *)

Theorem neq_sym : forall n m, n ~= m -> m ~= n.
Proof.
intros n m H1 H2; symmetry in H2; false_hyp H2 H1.
Qed.

Theorem eq_stepl : forall x y z, x == y -> x == z -> z == y.
Proof.
intros x y z H1 H2; now rewrite <- H1.
Qed.

Declare Left Step eq_stepl.
(* The right step lemma is just the transitivity of eq *)
Declare Right Step (@Equivalence_Transitive _ _ eq_equiv).

Theorem succ_inj : forall n1 n2, S n1 == S n2 -> n1 == n2.
Proof.
intros n1 n2 H.
apply pred_wd in H. now do 2 rewrite pred_succ in H.
Qed.

(* The following theorem is useful as an equivalence for proving
bidirectional induction steps *)
Theorem succ_inj_wd : forall n1 n2, S n1 == S n2 <-> n1 == n2.
Proof.
intros; split.
apply succ_inj.
intros. now f_equiv.
Qed.

Theorem succ_inj_wd_neg : forall n m, S n ~= S m <-> n ~= m.
Proof.
intros; now rewrite succ_inj_wd.
Qed.

(* We cannot prove that the predecessor is injective, nor that it is
left-inverse to the successor at this point *)

Section CentralInduction.

Variable A : t -> Prop.
Hypothesis A_wd : Proper (eq==>iff) A.

Theorem central_induction :
  forall z, A z ->
    (forall n, A n <-> A (S n)) ->
      forall n, A n.
Proof.
intros z Base Step; revert Base; pattern z; apply bi_induction.
solve_proper.
intro; now apply bi_induction.
intro; pose proof (Step n); tauto.
Qed.

End CentralInduction.

Tactic Notation "nzinduct" ident(n) :=
  induction_maker n ltac:(apply bi_induction).

Tactic Notation "nzinduct" ident(n) constr(u) :=
  induction_maker n ltac:(apply central_induction with (z := u)).

End NZBaseProp.

