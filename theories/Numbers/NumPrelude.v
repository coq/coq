Require Export Setoid.
Require Export Bool.
(* Standard library. Export, not Import, because if a file
importing the current file wants to use. e.g.,
Theorem eq_true_or : forall b1 b2 : bool, b1 || b2 <-> b1 \/ b2,
then it needs to know about bool and have a notation ||. *)
Require Export QRewrite.

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

Definition eq_bool := (@eq bool).

(*Inductive eq_true : bool -> Prop := is_eq_true : eq_true true.*)
(* This has been added to theories/Datatypes.v *)
Coercion eq_true : bool >-> Sortclass.

Theorem eq_true_unfold_pos : forall b : bool, b <-> b = true.
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
Qed.

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
Variable EA : relation A.
Variable EB : relation B.
Variable EC : relation C.

(* "wd" stands for "well-defined" *)

Definition fun_wd (f : A -> B) := forall x y : A, EA x y -> EB (f x) (f y).

Definition fun2_wd (f : A -> B -> C) :=
  forall x x' : A, EA x x' -> forall y y' : B, EB y y' -> EC (f x y) (f x' y').

Definition eq_fun : relation (A -> B) :=
  fun f f' => forall x x' : A, EA x x' -> EB (f x) (f' x').

(* Note that reflexivity of eq_fun means that every function
is well-defined w.r.t. EA and EB, i.e.,
forall x x' : A, EA x x' -> EB (f x) (f x') *)

Definition eq_fun2 (f f' : A -> B -> C) :=
  forall x x' : A, EA x x' -> forall y y' : B, EB y y' -> EC (f x y) (f' x' y').

End ExtensionalProperties.

Implicit Arguments fun_wd [A B].
Implicit Arguments fun2_wd [A B C].
Implicit Arguments eq_fun [A B].
Implicit Arguments eq_fun2 [A B C].

Definition predicate_wd (A : Type) (EA : relation A) := fun_wd EA iff.

Definition rel_wd (A B : Type) (EA : relation A) (EB : relation B) :=
  fun2_wd EA EB iff.

Implicit Arguments predicate_wd [A].
Implicit Arguments rel_wd [A B].

Ltac solve_predicate_wd :=
unfold predicate_wd;
let x := fresh "x" in
let y := fresh "y" in
let H := fresh "H" in
  intros x y H; qiff x y H.

Ltac solve_rel_wd :=
unfold rel_wd, fun2_wd;
let x1 := fresh "x" in
let y1 := fresh "y" in
let H1 := fresh "H" in
let x2 := fresh "x" in
let y2 := fresh "y" in
let H2 := fresh "H" in
  intros x1 y1 H1 x2 y2 H2;
  qsetoid_rewrite H1;
  qiff x2 y2 H2.
(* The tactic solve_rel_wd is not very efficient because qsetoid_rewrite
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
Variable EA : relation A.
Variable EB : relation B.

Hypothesis EA_equiv : equiv A EA.
Hypothesis EB_equiv : equiv B EB.

Definition prod_rel : relation (A * B) :=
  fun p1 p2 => EA (fst p1) (fst p2) /\ EB (snd p1) (snd p2).

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

Theorem neg_false : forall P : Prop, ~ P <-> (P <-> False).
Proof.
intro P; unfold not; split; intro H; [split; intro H1;
[apply H; assumption | elim H1] | apply (proj1 H)].
Qed.

(* This tactic replaces P in the goal with False.
The goal ~ P should be solvable by "apply H". *)
Ltac rewrite_false P H :=
setoid_replace P with False using relation iff;
[| apply -> neg_false; apply H].

Ltac rewrite_true P H :=
setoid_replace P with True using relation iff;
[| split; intro; [constructor | apply H]].

(*Ltac symmetry Eq :=
lazymatch Eq with
| ?E ?t1 ?t2 => setoid_replace (E t1 t2) with (E t2 t1) using relation iff;
  [| split; intro; symmetry; assumption]
| _ => fail Eq "does not have the form (E t1 t2)"
end.*)
(* This does not work because there already is a tactic "symmetry".
Declaring "symmetry" a tactic notation does not work because it conflicts
with "symmetry in": it thinks that "in" is a term. *)

Theorem and_cancel_l : forall A B C : Prop,
  (B -> A) -> (C -> A ) -> ((A /\ B <-> A /\ C) <-> (B <-> C)).
Proof.
intros; tauto.
Qed.

Theorem and_cancel_r : forall A B C : Prop,
  (B -> A) -> (C -> A ) -> ((B /\ A <-> C /\ A) <-> (B <-> C)).
Proof.
intros; tauto.
Qed.

Theorem or_cancel_l : forall A B C : Prop,
  (B -> ~A) -> (C -> ~ A) -> ((A \/ B <-> A \/ C) <-> (B <-> C)).
Proof.
intros; tauto.
Qed.

Theorem or_cancel_r : forall A B C : Prop,
  (B -> ~A) -> (C -> ~ A) -> ((B \/ A <-> C \/ A) <-> (B <-> C)).
Proof.
intros; tauto.
Qed.

Theorem or_iff_compat_l : forall A B C : Prop,
  (B <-> C) -> (A \/ B <-> A \/ C).
Proof.
intros; tauto.
Qed.

Theorem or_iff_compat_r : forall A B C : Prop,
  (B <-> C) -> (B \/ A <-> C \/ A).
Proof.
intros; tauto.
Qed.

Lemma iff_stepl : forall A B C : Prop, (A <-> B) -> (A <-> C) -> (C <-> B).
Proof.
intros; tauto.
Qed.

Declare Left Step iff_stepl.
Declare Right Step iff_trans.

Definition comp_bool (x y : comparison) : bool :=
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
Qed.

Definition LE_Set : forall A : Set, relation A := (@eq).

Lemma eq_equiv : forall A : Set, equiv A (LE_Set A).
Proof.
intro A; unfold equiv, LE_Set, reflexive, symmetric, transitive.
repeat split; [exact (@trans_eq A) | exact (@sym_eq A)].
(* It is interesting how the tactic split proves reflexivity *)
Qed.

Add Relation (fun A : Set => A) LE_Set
 reflexivity proved by (fun A : Set => (proj1 (eq_equiv A)))
 symmetry proved by (fun A : Set => (proj2 (proj2 (eq_equiv A))))
 transitivity proved by (fun A : Set => (proj1 (proj2 (eq_equiv A))))
as EA_rel.

(*
 Local Variables:
 tags-file-name: "~/coq/trunk/theories/Numbers/TAGS"
 End:
*)
