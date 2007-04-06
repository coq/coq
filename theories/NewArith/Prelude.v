Require Export Setoid.

(*
Contents:
- Coercion from bool to Prop
- A couple of useful tactics
- An attempt to extend setoid rewrite to formulas with quantifiers
- Extentional properties of predicates, relations and functions
  (well-definedness and equality)
- Relations on cartesian product
- Some boolean functions on nat
- Tactics for applying equivalences (iff)
- Miscellaneous
*)

(** Coercion from bool to Prop *)

Definition eq_bool := (@eq bool).

Inductive eq_true : bool -> Prop := is_eq_true : eq_true true.
Coercion eq_true : bool >-> Sortclass.

Theorem neg_eq_true : forall x : bool, ~ x -> x = false.
Proof.
intros x H; destruct x; [elim (H is_eq_true) | reflexivity].
Qed.

(** A couple of useful tactics *)

(** A useful complement to absurd_hyp. Here t : ~ A where H : A. *)
(*Ltac false_hyp H t :=
absurd_hyp H; [apply t | assumption].*)

(** This tactic is taken from Coq'Art book, p. 160 *)
(*Ltac caseEq f :=
  generalize (refl_equal f); pattern f at -1; destruct f.*)

(** A tactic simpler than auto which is useful for ending proofs *)
Tactic Notation "now" tactic(t) :=
t;
match goal with
| H : False |- _ => elim H
| H : eq_true false |- _ => inversion H
| |- eq_true true => apply is_eq_true
| _ => solve [trivial | reflexivity | symmetry; trivial | discriminate]
end.

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

(* The following properties are used both in Peano.v and in MPeano.v *)

Theorem lt_bool_0 : forall x, ~ (lt_bool x 0).
Proof.
destruct x as [|x]; simpl; now intro.
Qed.

Theorem lt_bool_S : forall x y, lt_bool x (S y) <-> lt_bool x y \/ x = y.
Proof.
induction x as [| x IH]; destruct y as [| y]; simpl.
split; [now right | now intro].
split; [now left | now intro].
split; [intro H; false_hyp H lt_bool_0 |
intro H; destruct H as [H | H]; now auto].
assert (H : x = y <-> S x = S y); [split; auto|].
rewrite <- H; apply IH.
Qed.

(** Tactics for applying equivalences.

The following code provides tactics "apply -> t", "apply <- t",
"apply -> t in H" and "apply <- t in H". Here t is a term whose type
consists of nested dependent and nondependent products with an
equivalence A <-> B as the conclusion. The tactics with "->" in their
names apply A -> B while those with "<-" in the name apply B -> A. *)

(* The idea of the tactics is to first provide a term in the context
whose type is the implication (in one of the directions), and then
apply it. The first idea is to produce a statement "forall ..., A ->
B" (call this type T) and then do "assert (H : T)" for a fresh H.
Thus, T can be proved from the original equivalence and then used to
perform the application. However, currently in Ltac it is difficult
to produce such T from the original formula.

Therefore, we first pose the original equivalence as H. If the type of
H is a dependent product, we create an existential variable and apply
H to this variable. If the type of H has the form C -> D, then we do a
cut on C. Once we eliminate all products, we split (i.e., destruct)
the conjunction into two parts and apply the relevant one. *)

(*Ltac find_equiv H :=
let T := type of H in
lazymatch T with
| ?A -> ?B =>
  let H1 := fresh in
  let H2 := fresh in
  cut A;
  [intro H1; pose proof (H H1) as H2; clear H H1;
   rename H2 into H; find_equiv H |
   clear H]
| forall x : ?t, _ =>
  let a := fresh "a" with
      H1 := fresh "H" in
    evar (a : t); pose proof (H a) as H1; unfold a in H1;
    clear a; clear H; rename H1 into H; find_equiv H
| ?A <-> ?B => idtac
| _ => fail "The given statement does not seem to end with an equivalence"
end.

Ltac bapply lemma todo :=
let H := fresh in
  pose proof lemma as H;
  find_equiv H; [todo H; clear H | .. ].

Tactic Notation "apply" "->" constr(lemma) :=
bapply lemma ltac:(fun H => destruct H as [H _]; apply H).

Tactic Notation "apply" "<-" constr(lemma) :=
bapply lemma ltac:(fun H => destruct H as [_ H]; apply H).

Tactic Notation "apply" "->" constr(lemma) "in" ident(J) :=
bapply lemma ltac:(fun H => destruct H as [H _]; apply H in J).

Tactic Notation "apply" "<-" constr(lemma) "in" ident(J) :=
bapply lemma ltac:(fun H => destruct H as [_ H]; apply H in J).
*)
(** Miscellaneous *)

Definition less_than (x : comparison) : bool :=
match x with Lt => true | _ => false end.

Lemma eq_equiv : forall A : Type, equiv A (@eq A).
Proof.
intro A; unfold equiv, reflexive, symmetric, transitive.
repeat split; [exact (@trans_eq A) | exact (@sym_eq A)].
(* It is interesting how the tactic split proves reflexivity *)
Qed.
