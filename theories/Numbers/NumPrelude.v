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

Require Export Setoid.
(*Require Export Bool.*)
(* Standard library. Export, not Import, because if a file
importing the current file wants to use. e.g.,
Theorem eq_true_or : forall b1 b2 : bool, b1 || b2 <-> b1 \/ b2,
then it needs to know about bool and have a notation ||. *)
Require Export QRewrite.

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

(** Extentional properties of predicates, relations and functions *)

Definition predicate (A : Type) := A -> Prop.

Section ExtensionalProperties.

Variables A B C : Type.
Variable Aeq : relation A.
Variable Beq : relation B.
Variable Ceq : relation C.

(* "wd" stands for "well-defined" *)

Definition fun_wd (f : A -> B) := forall x y : A, Aeq x y -> Beq (f x) (f y).

Definition fun2_wd (f : A -> B -> C) :=
  forall x x' : A, Aeq x x' -> forall y y' : B, Beq y y' -> Ceq (f x y) (f x' y').

Definition fun_eq : relation (A -> B) :=
  fun f f' => forall x x' : A, Aeq x x' -> Beq (f x) (f' x').

(* Note that reflexivity of fun_eq means that every function
is well-defined w.r.t. Aeq and Beq, i.e.,
forall x x' : A, Aeq x x' -> Beq (f x) (f x') *)

Definition fun2_eq (f f' : A -> B -> C) :=
  forall x x' : A, Aeq x x' -> forall y y' : B, Beq y y' -> Ceq (f x y) (f' x' y').

End ExtensionalProperties.

(* The following definitions instantiate Beq or Ceq to iff; therefore, they
have to be outside the ExtensionalProperties section *)

Definition predicate_wd (A : Type) (Aeq : relation A) := fun_wd Aeq iff.

Definition relation_wd (A B : Type) (Aeq : relation A) (Beq : relation B) :=
  fun2_wd Aeq Beq iff.

Definition relations_eq (A B : Type) (R1 R2 : A -> B -> Prop) :=
  forall (x : A) (y : B), R1 x y <-> R2 x y.

Theorem relations_eq_equiv :
  forall (A B : Type), equiv (A -> B -> Prop) (@relations_eq A B).
Proof.
intros A B; unfold equiv. split; [| split];
unfold reflexive, symmetric, transitive, relations_eq.
reflexivity.
intros R1 R2 R3 H1 H2 x y; rewrite H1; apply H2.
now symmetry.
Qed.

Add Parametric Relation (A B : Type) : (A -> B -> Prop) (@relations_eq A B)
  reflexivity proved by (proj1 (relations_eq_equiv A B))
  symmetry proved by (proj2 (proj2 (relations_eq_equiv A B)))
  transitivity proved by (proj1 (proj2 (relations_eq_equiv A B)))
as relations_eq_rel.

Add Parametric Morphism (A : Type) : (@well_founded A) with signature (@relations_eq A A) ==> iff as well_founded_wd.
Proof.
unfold relations_eq, well_founded; intros R1 R2 H;
split; intros H1 a; induction (H1 a) as [x H2 H3]; constructor;
intros y H4; apply H3; [now apply <- H | now apply -> H].
Qed.

(* solve_predicate_wd solves the goal [predicate_wd P] for P consisting of
morhisms and quatifiers *)

Ltac solve_predicate_wd :=
unfold predicate_wd;
let x := fresh "x" in
let y := fresh "y" in
let H := fresh "H" in
  intros x y H; qiff x y H.

(* solve_relation_wd solves the goal [relation_wd R] for R consisting of
morhisms and quatifiers *)

Ltac solve_relation_wd :=
unfold relation_wd, fun2_wd;
let x1 := fresh "x" in
let y1 := fresh "y" in
let H1 := fresh "H" in
let x2 := fresh "x" in
let y2 := fresh "y" in
let H2 := fresh "H" in
  intros x1 y1 H1 x2 y2 H2;
  qsetoid_rewrite H1;
  qiff x2 y2 H2.

(* The tactic solve_relation_wd is not very efficient because qsetoid_rewrite
uses qiff to take the formula apart in order to make it quantifier-free,
and then qiff is called again and takes the formula apart for the second
time. It is better to analyze the formula once and generalize qiff to take
a list of equalities that it has to rewrite. *)

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

(** Relations on cartesian product. Used in MiscFunct for defining
functions whose domain is a product of sets by primitive recursion *)

Section RelationOnProduct.

Variables A B : Set.
Variable Aeq : relation A.
Variable Beq : relation B.

Hypothesis EA_equiv : equiv A Aeq.
Hypothesis EB_equiv : equiv B Beq.

Definition prod_rel : relation (A * B) :=
  fun p1 p2 => Aeq (fst p1) (fst p2) /\ Beq (snd p1) (snd p2).

Lemma prod_rel_refl : reflexive (A * B) prod_rel.
Proof.
unfold reflexive, prod_rel.
destruct x; split; [apply (proj1 EA_equiv) | apply (proj1 EB_equiv)]; simpl.
Qed.

Lemma prod_rel_symm : symmetric (A * B) prod_rel.
Proof.
unfold symmetric, prod_rel.
destruct x; destruct y;
split; [apply (proj2 (proj2 EA_equiv)) | apply (proj2 (proj2 EB_equiv))]; simpl in *; tauto.
Qed.

Lemma prod_rel_trans : transitive (A * B) prod_rel.
Proof.
unfold transitive, prod_rel.
destruct x; destruct y; destruct z; simpl.
intros; split; [apply (proj1 (proj2 EA_equiv)) with (y := a0) |
apply (proj1 (proj2 EB_equiv)) with (y := b0)]; tauto.
Qed.

Theorem prod_rel_equiv : equiv (A * B) prod_rel.
Proof.
unfold equiv; split; [exact prod_rel_refl | split; [exact prod_rel_trans | exact prod_rel_symm]].
Qed.

End RelationOnProduct.

Implicit Arguments prod_rel [A B].
Implicit Arguments prod_rel_equiv [A B].

(** Miscellaneous *)

(*Definition comp_bool (x y : comparison) : bool :=
match x, y with
| Lt, Lt => true
| Eq, Eq => true
| Gt, Gt => true
| _, _   => false
end.

Theorem comp_bool_correct : forall x y : comparison,
  comp_bool x y <-> x = y.
Proof.
destruct x; destruct y; simpl; split; now intro.
Qed.*)

Lemma eq_equiv : forall A : Set, equiv A (@eq A).
Proof.
intro A; unfold equiv, reflexive, symmetric, transitive.
repeat split; [exact (@trans_eq A) | exact (@sym_eq A)].
(* It is interesting how the tactic split proves reflexivity *)
Qed.

(*Add Relation (fun A : Set => A) LE_Set
 reflexivity proved by (fun A : Set => (proj1 (eq_equiv A)))
 symmetry proved by (fun A : Set => (proj2 (proj2 (eq_equiv A))))
 transitivity proved by (fun A : Set => (proj1 (proj2 (eq_equiv A))))
as EA_rel.*)
