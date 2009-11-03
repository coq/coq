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

Require Export Setoid Morphisms RelationPairs.

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

Definition fun_wd (f : A -> B) := Proper (Aeq==>Beq) f.

Definition fun2_wd (f : A -> B -> C) := Proper (Aeq==>Beq==>Ceq) f.

Definition fun_eq : relation (A -> B) := (Aeq==>Beq)%signature.

(* Note that reflexivity of fun_eq means that every function
is well-defined w.r.t. Aeq and Beq, i.e.,
forall x x' : A, Aeq x x' -> Beq (f x) (f x') *)

Definition fun2_eq (f f' : A -> B -> C) := (Aeq==>Beq==>Ceq)%signature f f'.

End ExtensionalProperties.

(* The following definitions instantiate Beq or Ceq to iff; therefore, they
have to be outside the ExtensionalProperties section *)

Definition predicate_wd (A : Type) (Aeq : relation A) := Proper (Aeq==>iff).

Definition relation_wd (A B : Type) (Aeq : relation A) (Beq : relation B) :=
  Proper (Aeq==>Beq==>iff).

Definition relations_eq (A B : Type) (R1 R2 : A -> B -> Prop) :=
  forall (x : A) (y : B), R1 x y <-> R2 x y.

Instance relation_eq_equiv A B : Equivalence (@relations_eq A B).
Proof.
intros A B; split;
unfold Reflexive, Symmetric, Transitive, relations_eq.
reflexivity.
now symmetry.
intros R1 R2 R3 H1 H2 x y; rewrite H1; apply H2.
Qed.

Instance well_founded_wd A : Proper (@relations_eq A A ==> iff) (@well_founded A).
Proof.
unfold relations_eq, well_founded; intros A R1 R2 H.
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
  intros x y H; setoid_rewrite H; reflexivity.

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

(** Relations on cartesian product. Used in MiscFunct for defining
functions whose domain is a product of sets by primitive recursion *)

Section RelationOnProduct.

Variables A B : Set.
Variable Aeq : relation A.
Variable Beq : relation B.

Definition prod_rel : relation (A * B) := (Aeq * Beq)%signature.

Instance prod_rel_equiv `(Equivalence _ Aeq, Equivalence _ Beq) :
 Equivalence prod_rel.

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


