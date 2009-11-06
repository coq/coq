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

Require Import Bool.
Require Export NumPrelude.

Module Type ZDomainSignature.

Parameter Inline Z : Set.
Parameter Inline Zeq : Z -> Z -> Prop.
Parameter Inline Zeqb : Z -> Z -> bool.

Axiom eqb_equiv_eq : forall x y : Z, Zeqb x y = true <-> Zeq x y.
Instance eq_equiv : Equivalence Zeq.

Delimit Scope IntScope with Int.
Bind Scope IntScope with Z.
Notation "x == y" := (Zeq x y) (at level 70) : IntScope.
Notation "x # y" := (~ Zeq x y) (at level 70) : IntScope.

End ZDomainSignature.

Module ZDomainProperties (Import ZDomainModule : ZDomainSignature).
Open Local Scope IntScope.

Instance Zeqb_wd : Proper (Zeq ==> Zeq ==> eq) Zeqb.
Proof.
intros x x' Exx' y y' Eyy'.
apply eq_true_iff_eq.
rewrite 2 eqb_equiv_eq, Exx', Eyy'; auto with *.
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
Declare Right Step (@Equivalence_Transitive _ _ eq_equiv).

End ZDomainProperties.


