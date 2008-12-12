(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*                      Evgeny Makarov, INRIA, 2007                     *)
(************************************************************************)

(*i $Id$ i*)

Require Export NumPrelude.

Module Type ZDomainSignature.

Parameter Inline Z : Set.
Parameter Inline Zeq : Z -> Z -> Prop.
Parameter Inline e : Z -> Z -> bool.

Axiom eq_equiv_e : forall x y : Z, Zeq x y <-> e x y.
Axiom eq_equiv : equiv Z Zeq.

Add Relation Z Zeq
 reflexivity proved by (proj1 eq_equiv)
 symmetry proved by (proj2 (proj2 eq_equiv))
 transitivity proved by (proj1 (proj2 eq_equiv))
as eq_rel.

Delimit Scope IntScope with Int.
Bind Scope IntScope with Z.
Notation "x == y" := (Zeq x y) (at level 70) : IntScope.
Notation "x # y" := (~ Zeq x y) (at level 70) : IntScope.

End ZDomainSignature.

Module ZDomainProperties (Import ZDomainModule : ZDomainSignature).
Open Local Scope IntScope.

Add Morphism e with signature Zeq ==> Zeq ==> eq_bool as e_wd.
Proof.
intros x x' Exx' y y' Eyy'.
case_eq (e x y); case_eq (e x' y'); intros H1 H2; trivial.
assert (x == y); [apply <- eq_equiv_e; now rewrite H2 |
assert (x' == y'); [rewrite <- Exx'; now rewrite <- Eyy' |
rewrite <- H1; assert (H3 : e x' y'); [now apply -> eq_equiv_e | now inversion H3]]].
assert (x' == y'); [apply <- eq_equiv_e; now rewrite H1 |
assert (x == y); [rewrite Exx'; now rewrite Eyy' |
rewrite <- H2; assert (H3 : e x y); [now apply -> eq_equiv_e | now inversion H3]]].
Qed.

Theorem neq_sym : forall n m, n # m -> m # n.
Proof.
intros n m H1 H2; symmetry in H2; false_hyp H2 H1.
Qed.

Theorem ZE_stepl : forall x y z : Z, x == y -> x == z -> z == y.
Proof.
intros x y z H1 H2; now rewrite <- H1.
Qed.

Declare Left Step ZE_stepl.

(* The right step lemma is just transitivity of Zeq *)
Declare Right Step (proj1 (proj2 eq_equiv)).

End ZDomainProperties.


