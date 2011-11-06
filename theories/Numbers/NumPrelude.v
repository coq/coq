(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2011     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*                      Evgeny Makarov, INRIA, 2007                     *)
(************************************************************************)

(*i $Id$ i*)

Require Export Setoid Morphisms.

Set Implicit Arguments.
(*
Contents:
- Coercion from bool to Prop
- Extension of the tactics stepl and stepr
- Extentional properties of predicates, relations and functions
  (well-definedness and equality)
- Relations on cartesian product
- Miscellaneous
*)

(** Coercion from bool to Prop *)

(*Definition eq_bool := (@eq bool).*)

(*Inductive eq_true : bool -> Prop := is_eq_true : eq_true true.*)
(* This has been added to theories/Datatypes.v *)
(*Coercion eq_true : bool >-> Sortclass.*)

(*Theorem eq_true_unfold_pos : forall b : bool, b <-> b = true.
Proof.
intro b; split; intro H. now inversion H. now rewrite H.
Qed.

Theorem eq_true_unfold_neg : forall b : bool, ~ b <-> b = false.
Proof.
intros b; destruct b; simpl; rewrite eq_true_unfold_pos.
split; intro H; [elim (H (refl_equal true)) | discriminate H].
split; intro H; [reflexivity | discriminate].
Qed.

Theorem eq_true_or : forall b1 b2 : bool, b1 || b2 <-> b1 \/ b2.
Proof.
destruct b1; destruct b2; simpl; tauto.
Qed.

Theorem eq_true_and : forall b1 b2 : bool, b1 && b2 <-> b1 /\ b2.
Proof.
destruct b1; destruct b2; simpl; tauto.
Qed.

Theorem eq_true_neg : forall b : bool, negb b <-> ~ b.
Proof.
destruct b; simpl; rewrite eq_true_unfold_pos; rewrite eq_true_unfold_neg;
split; now intro.
Qed.

Theorem eq_true_iff : forall b1 b2 : bool, b1 = b2 <-> (b1 <-> b2).
Proof.
intros b1 b2; split; intro H.
now rewrite H.
destruct b1; destruct b2; simpl; try reflexivity.
apply -> eq_true_unfold_neg. rewrite H. now intro.
symmetry; apply -> eq_true_unfold_neg. rewrite <- H; now intro.
Qed.*)

(** Extension of the tactics stepl and stepr to make them
applicable to hypotheses *)

Tactic Notation "stepl" constr(t1') "in" hyp(H) :=
match (type of H) with
| ?R ?t1 ?t2 =>
  let H1 := fresh in
  cut (R t1' t2); [clear H; intro H | stepl t1; [assumption |]]
| _ => fail 1 ": the hypothesis" H "does not have the form (R t1 t2)"
end.

Tactic Notation "stepl" constr(t1') "in" hyp(H) "by" tactic(r) := stepl t1' in H; [| r].

Tactic Notation "stepr" constr(t2') "in" hyp(H) :=
match (type of H) with
| ?R ?t1 ?t2 =>
  let H1 := fresh in
  cut (R t1 t2'); [clear H; intro H | stepr t2; [assumption |]]
| _ => fail 1 ": the hypothesis" H "does not have the form (R t1 t2)"
end.

Tactic Notation "stepr" constr(t2') "in" hyp(H) "by" tactic(r) := stepr t2' in H; [| r].

(** Predicates, relations, functions *)

Definition predicate (A : Type) := A -> Prop.

Instance well_founded_wd A :
 Proper (@relation_equivalence A ==> iff) (@well_founded A).
Proof.
intros R1 R2 H.
split; intros WF a; induction (WF a) as [x _ WF']; constructor;
intros y Ryx; apply WF'; destruct (H y x); auto.
Qed.

(** [solve_predicate_wd] solves the goal [Proper (?==>iff) P]
    for P consisting of morphisms and quantifiers *)

Ltac solve_predicate_wd :=
let x := fresh "x" in
let y := fresh "y" in
let H := fresh "H" in
  intros x y H; setoid_rewrite H; reflexivity.

(** [solve_relation_wd] solves the goal [Proper (?==>?==>iff) R]
    for R consisting of morphisms and quantifiers *)

Ltac solve_relation_wd :=
let x1 := fresh "x" in
let y1 := fresh "y" in
let H1 := fresh "H" in
let x2 := fresh "x" in
let y2 := fresh "y" in
let H2 := fresh "H" in
  intros x1 y1 H1 x2 y2 H2;
  rewrite H1; setoid_rewrite H2; reflexivity.

(* The following tactic uses solve_predicate_wd to solve the goals
relating to well-defidedness that are produced by applying induction.
We declare it to take the tactic that applies the induction theorem
and not the induction theorem itself because the tactic may, for
example, supply additional arguments, as does NZinduct_center in
NZBase.v *)

Ltac induction_maker n t :=
  try intros until n;
  pattern n; t; clear n;
  [solve_predicate_wd | ..].

