(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
(*                      Evgeny Makarov, INRIA, 2007                     *)
(************************************************************************)

(**
* Basic lemmas about modules implementing [NZDomainSig']

This file defines the functor type [NZBaseProp] which adds the following
lemmas:
- [eq_refl], [eq_sym], [eq_trans]
- [eq_sym_iff], [neq_sym], [eq_stepl]
- [succ_inj], [succ_inj_wd], [succ_inj_wd_neg]
- [central_induction] and the tactic notation [nzinduct]

The functor type [NZBaseProp] is meant to be [Include]d in a module implementing
[NZDomainSig'].
*)

From Stdlib.Numbers.NatInt Require Import NZAxioms.

Module Type NZBaseProp (Import NZ : NZDomainSig').

(** This functor from [Stdlib.Structures.Equalities] gives
    [eq_refl], [eq_sym] and [eq_trans]. *)
Include BackportEq NZ NZ.

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

(** We add entries in the [stepl] and [stepr] databases. *)

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
- apply succ_inj.
- intros. now f_equiv.
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
- solve_proper.
- intro; now apply bi_induction.
- intro n; pose proof (Step n); tauto.
Qed.

End CentralInduction.

Tactic Notation "nzinduct" ident(n) :=
  induction_maker n ltac:(apply bi_induction).

Tactic Notation "nzinduct" ident(n) constr(u) :=
  induction_maker n ltac:(apply (fun A A_wd => central_induction A A_wd u)).

End NZBaseProp.
