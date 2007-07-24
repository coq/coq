Require Export Setoid.
Require Import Bool.

(*
Contents:
- Coercion from bool to Prop
- An attempt to extend setoid rewrite to formulas with quantifiers
- Extentional properties of predicates, relations and functions
  (well-definedness and equality)
- Relations on cartesian product
- Some boolean functions on nat
- Miscellaneous
*)

(** Coercion from bool to Prop *)

Definition eq_bool := (@eq bool).

Inductive eq_true : bool -> Prop := is_eq_true : eq_true true.
Coercion eq_true : bool >-> Sortclass.

Theorem eq_true_unfold : forall b : bool, b <-> b = true.
Proof.
intro b; split; intro H.
now inversion H.
now rewrite H.
Qed.

Theorem eq_true_neg : forall x : bool, ~ x -> x = false.
Proof.
intros x H; destruct x; [elim (H is_eq_true) | reflexivity].
Qed.

(** An attempt to extend setoid rewrite to formulas with quantifiers *)

(* The following algorithm was explained to me by Bruno Barras.

In the future, we need to prove that some predicates are
well-defined w.r.t. a setoid relation, i.e., we need to prove theorems
of the form "forall x y, x == y -> (P x <-> P y)". The reason is that it
makes sense to do induction only on predicates that satisfy this
property. Ideally, such goal should be proved by saying "intros x y H;
rewrite H; reflexivity".

Now, such predicates P may contain quantifiers besides setoid
morphisms. However, the tactic "rewrite" (which in this case stands
for "setoid_rewrite") currently cannot handle universal quantifiers as
well as lambda abstractions, which are part of the existential
quantifier notation (recall that "exists x, P" stands for "ex (fun x
=> p)").

Therefore, to prove that P x <-> P y, we proceed as follows. Suppose
that P x is C[forall z, Q[x,z]] where C is a context, i.e., a term
with a hole. We assume that the hole of C does not occur inside
another quantifier, i.e., that forall z, Q[x,z] is a top-level
quantifier in P. The notation Q[x,z] means that the term Q contains
free occurrences of variables x and z. We prove that forall z, Q[x,z]
<-> forall z, Q[y,z]. To do this, we show that forall z, Q[x,z] <->
Q[y,z]. After performing "intro z", this goal is handled recursively,
until no more quantifiers are left in Q.

After we obtain the goal

H : x == y
H1 : forall z, Q[x,z] <-> forall z, Q[y,z]
=================================
C[forall z, Q[x,z]] <-> C[forall z, Q[y,z]]

we say "rewrite H1". Repeating this for other quantifier subformulas
in P, we make them all identical in P x and P y. After that, saying
"rewrite H" solves the goal.

To implement this algorithm, we need the following theorems:

Theorem forall_morphism :
  forall (A : Set) (P Q : A -> Prop),
    (forall x : A, P x <-> Q x) -> ((forall x : A, P x) <-> (forall x : A, Q x)).

Theorem exists_morphism :
  forall (A : Set) (P Q : A -> Prop),
    (forall x : A, P x <-> Q x) -> (ex P <-> ex Q)

Below, we obtain them by registering the universal and existential
quantifiers as setoid morphisms, though they can be proved without any
reference to setoids. Ideally, registering quantifiers as morphisms
should take care of setoid rewriting in the presence of quantifiers,
but as described above, this is currently not so, and we have to
handle quantifiers manually.

The job of deriving P x <-> P y from x == y is done by the tactic
qmorphism x y below. *)

Section Quantifiers.

Variable A : Set.

Definition predicate := A -> Prop.

Definition equiv_predicate : relation predicate :=
  fun (P1 P2 : predicate) => forall x : A, P1 x <-> P2 x.

Theorem equiv_predicate_refl : reflexive predicate equiv_predicate.
Proof.
unfold reflexive, equiv_predicate. reflexivity.
Qed.

Theorem equiv_predicate_symm : symmetric predicate equiv_predicate.
Proof.
firstorder.
Qed.

Theorem equiv_predicate_trans : transitive predicate equiv_predicate.
Proof.
firstorder.
Qed.

Add Relation predicate equiv_predicate
  reflexivity proved by equiv_predicate_refl
  symmetry proved by equiv_predicate_symm
  transitivity proved by equiv_predicate_trans
as equiv_predicate_rel.

Add Morphism (@ex A)
  with signature equiv_predicate ==> iff
  as exists_morphism.
Proof.
firstorder.
Qed.

Add Morphism (fun P : predicate => forall x : A, P x)
  with signature equiv_predicate ==> iff
  as forall_morphism.
Proof.
firstorder.
Qed.

End Quantifiers.

(* replace x by y in t *)
Ltac repl x y t :=
match t with
| context C [x] => let t' := (context C [y]) in repl x y t'
| _ => t
end.

Ltac qmorphism x y :=
lazymatch goal with
| |- ?P <-> ?P => reflexivity
| |- context [ex ?P] =>
  match P with
  | context [x] =>
    let P' := repl x y P in
      setoid_replace (ex P) with (ex P') using relation iff;
      [qmorphism x y |
       apply exists_morphism; unfold equiv_predicate; intros; qmorphism x y]
  end
| |- context [forall z, @?P z] =>
  match P with
  | context [x] =>
    let P' := repl x y P in
      setoid_replace (forall z, P z) with (forall z, P' z) using relation iff;
      [qmorphism x y |
       apply forall_morphism; unfold equiv_predicate; intros; qmorphism x y]
  end
| _ => setoid_replace x with y; [reflexivity | assumption]
end.

(** Extentional properties of predicates, relations and functions *)

Section ExtensionalProperties.

Variables A B C : Set.
Variable EA : relation A.
Variable EB : relation B.
Variable EC : relation C.

(* "wd" stands for "well-defined" *)

Definition fun_wd (f : A -> B) := forall x y : A, EA x y -> EB (f x) (f y).

Definition fun2_wd (f : A -> B -> C) :=
  forall x x' : A, EA x x' -> forall y y' : B, EB y y' -> EC (f x y) (f x' y').

Definition pred_wd (P : predicate A) :=
  forall x y, EA x y -> (P x <-> P y).

Definition rel_wd (R : relation A) :=
  forall x x', EA x x' -> forall y y', EA y y' -> (R x y <-> R x' y').

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
Implicit Arguments pred_wd [A].
Implicit Arguments rel_wd [A].

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

(** Some boolean functions on nat. Their analogs are available in the
standard library; however, we provide simpler definitions. Used in
defining  implementations of natural numbers. *)

Fixpoint eq_nat_bool (x y : nat) {struct x} : bool :=
match x, y with
| 0, 0 => true
| S x', S y' => eq_nat_bool x' y'
| _, _ => false
end.

Theorem eq_nat_bool_implies_eq : forall x y, eq_nat_bool x y -> x = y.
Proof.
induction x; destruct y; simpl; intro H; try (reflexivity || inversion H).
apply IHx in H; now rewrite H.
Qed.

Theorem eq_nat_bool_refl : forall x, eq_nat_bool x x.
Proof.
induction x; now simpl.
Qed.

Theorem eq_nat_correct : forall x y, eq_nat_bool x y <-> x = y.
Proof.
intros; split.
now apply eq_nat_bool_implies_eq.
intro H; rewrite H; apply eq_nat_bool_refl.
Qed.

(* The boolean less function can be defined as
fun n m => proj1_sig (nat_lt_ge_bool n m)
using the standard library.
However, this definitionseems too complex. First, there are many
functions involved: nat_lt_ge_bool is defined (in Coq.Arith.Bool_nat)
using bool_of_sumbool and
lt_ge_dec : forall x y : nat, {x < y} + {x >= y},
where the latter function is defined using sumbool_not and
le_lt_dec : forall n m : nat, {n <= m} + {m < n}.
Second, this definition is not the most efficient, especially since
le_lt_dec is proved using tactics, not by giving the explicit proof term. *)

Fixpoint lt_bool (n m : nat) {struct n} : bool :=
match n, m with
| 0, S _ => true
| S n', S m' => lt_bool n' m'
| _, 0 => false
end.

Fixpoint le_bool (n m : nat) {struct n} : bool :=
match n, m with
| 0, _ => true
| S n', S m' => le_bool n' m'
| S _, 0 => false
end.

(* The following properties are used both in Peano.v and in MPeano.v *)

Lemma le_lt_bool : forall x y, le_bool x y = (lt_bool x y) || (eq_nat_bool x y).
Proof.
induction x as [| x IH]; destruct y; simpl; (reflexivity || apply IH).
Qed.

Theorem le_lt : forall x y, le_bool x y <-> lt_bool x y \/ x = y.
Proof.
intros x y. rewrite le_lt_bool.
setoid_replace (eq_true (lt_bool x y || eq_nat_bool x y)) with
  (lt_bool x y = true \/ eq_nat_bool x y = true) using relation iff.
do 2 rewrite <- eq_true_unfold. now rewrite eq_nat_correct.
rewrite eq_true_unfold. split; [apply orb_prop | apply orb_true_intro].
Qed. (* Can be simplified *)

Theorem lt_bool_0 : forall x, ~ (lt_bool x 0).
Proof.
destruct x as [|x]; simpl; now intro.
Qed.

Theorem lt_bool_S : forall x y, lt_bool x (S y) <-> le_bool x y.
Proof.
assert (A : forall x y, lt_bool x (S y) <-> lt_bool x y \/ x = y).
induction x as [| x IH]; destruct y as [| y]; simpl.
split; [now right | now intro].
split; [now left | now intro].
split; [intro H; false_hyp H lt_bool_0 |
intro H; destruct H as [H | H]; now auto].
assert (H : x = y <-> S x = S y); [split; auto|].
rewrite <- H; apply IH.
intros; rewrite le_lt; apply A.
Qed.

(** Miscellaneous *)

Definition less_than (x : comparison) : bool :=
match x with Lt => true | _ => false end.

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
