
Set Warnings "-deprecated".

Module Backtrack.
  Class A (T : Type).
  (* Global Hint Mode A + : typeclass_instances. *)
  Class B (T T' : Type) := b : T'.
  (* Global Hint Mode B - + : typeclass_instances. *)

  Instance anat : A nat := {}.
  Instance abool : A bool := {}.
  Instance bnatnat : B nat nat := { b := 0 }.

  Definition foo {T'} {T} {a : A T'} {b : B T' T} : T := b.

  (* This relies on backtracking: we first solve
      A ? with abool (most recent decl), the find out that B bool _
      is not solvable and backtrack, find anat and finally solve B.
  *)
  Definition test := (foo : nat).

  (* This forces a different resolution path, where A ? is stuck at first,
    then we solve B's constraint, and we come back to A nat which is solvable.
  *)
  Global Hint Mode A + : typeclass_instances.

  Definition test' := (foo : nat).

End Backtrack.


Module Minimized.
  Class Insert (K V M : Type) : Prop.
  Global Hint Mode Insert - - + : typeclass_instances.
  Class Lookup (K A M : Type) : Prop.
  Global Hint Mode Lookup - - ! : typeclass_instances.

  Class Union (A : Type) : Prop.
  Global Hint Mode Union ! : typeclass_instances.
  Class FMap (K : Type) (M : Type -> Type) : Prop.

  Section Foo.
  Context K M `{FMap K M}.
  Context {A B : Type}.
  Axiom fi : forall {A} {hi : Insert K A (M A)}, A -> A.
  Axiom fu : forall {A} {hu : Union (M A)}, A.

  Section OrderOne.
  Context {i : Union (M A)}.
  Context {i' : Union (M B)}.
  Context {fi' : Insert K B (M B)}.

  (** Succees because Union has mode !, so (M _) is enough to trigger
      i', and then fi'. Union should probably be using + to avoid ambiguities.
    *)
  Definition test := (fi fu).
  End OrderOne.

  (* We check here that typeclass resolution backtracks correctly when reporting
     errors and does not follow modes too eagerly. *)
  Section OrderTwo.
  Context {i' : Union (M B)}.
  Context {fi' : Insert K B (M B)}.
  Context {i : Union (M A)}.

  (** Here we get two constraints, first is [Insert K ?A (M ?A)], second is [Union (M ?A)].
      The first is stuck so we proceed on the second one, which has two solutions.
      The i / M A is chosen first, but it has no insert instance,
      so we backtrack on this first solution to find i', even if i respected the mode
      of Union (just !). *)
  Definition test' := (fi fu).
  End OrderTwo.
  End Foo.
End Minimized.

Module Minimized'.
  Class Insert (K V M : Type) : Prop.
  Global Hint Mode Insert - - + : typeclass_instances.
  Class Lookup (K A M : Type) : Prop.
  Global Hint Mode Lookup - - + : typeclass_instances.

  Class Union (A : Type) : Prop.
  Global Hint Mode Union + : typeclass_instances.
  Class FMap (K : Type) (M : Type -> Type) : Prop.

  Section Foo.
  Context K M `{FMap K M}.
  Context {A B : Type}.
  Axiom fi : forall {A} {hi : Insert K A (M A)}, A -> A.
  Axiom fu : forall {A} {hu : Union (M A)}, A.
  Axiom fu' : forall {A} {hu : Union (M A)}, A -> A.
  Axiom fi' : forall {A} {hi : Insert K A (M A)}, A.

  Section OrderOne.
  Context {i : Union (M A)}.
  Context {i' : Union (M B)}.
  Context {fi' : Insert K B (M B)}.

  (** Fail because Union has now mode +, so (M _) is not enough to trigger
      i' and fi'. So we get a general type error
    *)
  Fail Definition test := (fi fu).

  (** Here we get the precise missing Insert instance when A is chosen: *)

  Fail Definition test' : A := (fi fu).

  (** Of course the unambiguous querry works *)
  Definition test : B := (fi fu).

  End OrderOne.

  Section OrderTwo.
  Context {i' : Union (M B)}.
  Context {fi' : Insert K B (M B)}.
  Context {i : Union (M A)}.

  (** Here this fails because this is entirely ambiguous: it cannot decide
      even on the A type. *)
  Fail Definition test := (fi fu).
  Definition test' : B := (fi fu).

  (** Here we get the precise missing instance when A is chosen: *)
  Fail Definition test'' : A := (fi fu).

  End OrderTwo.

  (** There can still be internal backtracking: here
      we check that if the union instance depends on another
      class we get the right behavior.*)
  Section OrderThree.
  Class Choose (b : bool).
  Context {ifalse : Choose false -> Union (M B)}.
  Context {itrue : Choose true -> Union (M B)}.
  Context {ib : Insert K B (M B)}.
  Context {i : Choose false -> Union (M A)}.

  (** Here this fails because this is entirely ambiguous: it cannot decide
      even on the A type. *)
  Fail Type (fi fu).

  (** Here we commit to B, but neither ifalse nor itrue applies, so
      Union (M B) is reported as unsolvable.
    *)
  Fail Type (fi fu : B).

  Context {ct : Choose false}.
  (** Here we can find ifalse to get Union (M B), after backtracking
      on the failing application of itrue (which last declared instance)
  *)
  Type (fi fu : B).

  End OrderThree.
  End Foo.


End Minimized'.

From Stdlib Require Export Morphisms RelationClasses List Bool Setoid Peano Utf8.
From Stdlib Require Import Permutation.
Export ListNotations.
From Stdlib.Program Require Export Basics Syntax.

Module Import base.
Global Generalizable All Variables.
Obligation Tactic := idtac.

(** Throughout this development we use [stdpp_scope] for all general purpose
notations that do not belong to a more specific scope. *)
Declare Scope stdpp_scope.
Delimit Scope stdpp_scope with stdpp.
Global Open Scope stdpp_scope.

Class Union A := union: A → A → A.
Global Hint Mode Union ! : typeclass_instances.
Instance: Params (@union) 2 := {}.
Infix "∪" := union (at level 50, left associativity) : stdpp_scope.

Class ElemOf A B := elem_of: A → B → Prop.
Global Hint Mode ElemOf - ! : typeclass_instances.
Instance: Params (@elem_of) 3 := {}.
Infix "∈" := elem_of (at level 70) : stdpp_scope.

Class FMap (M : Type → Type) := fmap : ∀ {A B}, (A → B) → M A → M B.
Global Arguments fmap {_ _ _ _} _ !_ / : assert.
Instance: Params (@fmap) 4 := {}.
Infix "<$>" := fmap (at level 61, left associativity) : stdpp_scope.

(** * Operations on maps *)
(** In this section we define operational type classes for the operations
on maps. In the file [fin_maps] we will axiomatize finite maps.
The function look up [m !! k] should yield the element at key [k] in [m]. *)
Class Lookup (K A M : Type) := lookup: K → M → option A.
Global Hint Mode Lookup - - ! : typeclass_instances.
Instance: Params (@lookup) 4 := {}.
Notation "m !! i" := (lookup i m) (at level 20) : stdpp_scope.
Global Arguments lookup _ _ _ _ !_ !_ / : simpl nomatch, assert.

(** The function insert [<[k:=a]>m] should update the element at key [k] with
value [a] in [m]. *)
Class Insert (K A M : Type) := insert: K → A → M → M.
Global Hint Mode Insert - - ! : typeclass_instances.
Instance: Params (@insert) 5 := {}.
Notation "<[ k := a ]>" := (insert k a)
  (at level 5, right associativity, format "<[ k := a ]>") : stdpp_scope.
Global Arguments insert _ _ _ _ !_ _ !_ / : simpl nomatch, assert.

(** The function delete [delete k m] should delete the value at key [k] in
[m]. If the key [k] is not a member of [m], the original map should be
returned. *)
Class Delete (K M : Type) := delete: K → M → M.
Global Hint Mode Delete - ! : typeclass_instances.
Instance: Params (@delete) 4 := {}.
Global Arguments delete _ _ _ !_ !_ / : simpl nomatch, assert.

(** The function [partial_alter f k m] should update the value at key [k] using the
function [f], which is called with the original value at key [k] or [None]
if [k] is not a member of [m]. The value at [k] should be deleted if [f]
yields [None]. *)
Class PartialAlter (K A M : Type) :=
  partial_alter: (option A → option A) → K → M → M.
Global Hint Mode PartialAlter - - ! : typeclass_instances.
Instance: Params (@partial_alter) 4 := {}.
Global Arguments partial_alter _ _ _ _ _ !_ !_ / : simpl nomatch, assert.

(** The function [merge f m1 m2] should merge the maps [m1] and [m2] by
constructing a new map whose value at key [k] is [f (m1 !! k) (m2 !! k)].*)
Class Merge (M : Type → Type) :=
  merge: ∀ {A B C}, (option A → option B → option C) → M A → M B → M C.
Global Hint Mode Merge ! : typeclass_instances.
Instance: Params (@merge) 4 := {}.
Global Arguments merge _ _ _ _ _ _ !_ !_ / : simpl nomatch, assert.

(** The function [union_with f m1 m2] is supposed to yield the union of [m1]
and [m2] using the function [f] to combine values of members that are in
both [m1] and [m2]. *)
Class UnionWith (A M : Type) :=
  union_with: (A → A → option A) → M → M → M.
Global Hint Mode UnionWith - ! : typeclass_instances.
Instance: Params (@union_with) 3 := {}.
Global Arguments union_with {_ _ _} _ !_ !_ / : simpl nomatch, assert.

(** We redefine the standard library's [In] and [NoDup] using type classes. *)
Inductive elem_of_list {A} : ElemOf A (list A) :=
  | elem_of_list_here (x : A) l : x ∈ x :: l
  | elem_of_list_further (x y : A) l : x ∈ l → x ∈ y :: l.
Existing Instance elem_of_list.

End base.

(** * Monadic operations *)
Global Instance option_fmap: FMap option := @option_map.

Global Instance option_union_with {A} : UnionWith A (option A) := λ f mx my,
  match mx, my with
  | Some x, Some y => f x y
  | Some x, None => Some x
  | None, Some y => Some y
  | None, None => None
  end.
Global Instance option_union {A} : Union (option A) := union_with (λ x _, Some x).

Unset Default Proof Using.

Class FinMapToList K A M := map_to_list: M → list (K * A).
Global Hint Mode FinMapToList ! - - : typeclass_instances.
Global Hint Mode FinMapToList - - ! : typeclass_instances.

Class FinMap K M `{FMap M, ∀ A, Lookup K A (M A), ∀ A, Empty (M A), ∀ A,
    PartialAlter K A (M A), OMap M, Merge M, ∀ A, FinMapToList K A (M A),
    EqDecision K} := {
  map_eq {A} (m1 m2 : M A) : (∀ i, m1 !! i = m2 !! i) → m1 = m2;
  lookup_partial_alter {A} f (m : M A) i :
    partial_alter f i m !! i = f (m !! i);
  lookup_partial_alter_ne {A} f (m : M A) i j :
    i ≠ j → partial_alter f i m !! j = m !! j;
  lookup_fmap {A B} (f : A → B) (m : M A) i : (f <$> m) !! i = f <$> m !! i;
  NoDup_map_to_list {A} (m : M A) : NoDup (map_to_list m);
  elem_of_map_to_list {A} (m : M A) i x :
    (i,x) ∈ map_to_list m ↔ m !! i = Some x;
  lookup_merge {A B C} (f : option A → option B → option C)
      `{!DiagNone f} (m1 : M A) (m2 : M B) i :
    merge f m1 m2 !! i = f (m1 !! i) (m2 !! i)
}.

(** * Derived operations *)
(** All of the following functions are defined in a generic way for arbitrary
finite map implementations. These generic implementations do not cause a
significant performance loss, which justifies including them in the finite map
interface as primitive operations. *)
Global Instance map_insert `{PartialAlter K A M} : Insert K A M :=
  λ i x, partial_alter (λ _, Some x) i.
Global Instance map_delete `{PartialAlter K A M} : Delete K M :=
  partial_alter (λ _, None).

Global Instance map_union_with `{Merge M} {A} : UnionWith A (M A) :=
  λ f, merge (union_with f).
Global Instance map_union `{Merge M} {A} : Union (M A) := union_with (λ x _, Some x).

(** * Theorems *)
Section theorems.
  Context `{FinMap K M}.

  (** Just the Insert instance is missing, as we've commited on (M A) *)
  Fail Lemma union_delete_insert {A} (m1 m2 : M A) i x :
    m1 !! i = Some x →
    delete i m1 ∪ <[i:=i]> m2 = m1 ∪ m2.

  Lemma union_delete_insert {A} (m1 m2 : M A) i x :
    m1 !! i = Some x →
    delete i m1 ∪ <[i:=x]> m2 = m1 ∪ m2.
  Proof. Abort.

End theorems.
