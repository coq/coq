(* Check that hints are correctly applied up to η-expansion. *)

Module Unary.

Class Test {A : Type} (R : A -> Prop) : Prop := {}.

Axiom A : Type.

Definition foo {R : A -> Prop} {HR : @Test A (fun x => R x)} : @Test A R := _.
Definition bar {R : A -> Prop} {HR : @Test A R} : @Test A (fun x => R x) := _.

Axiom R₀ : A -> Prop.

Definition foo₀ {HR : @Test A (fun x => R₀ x)} : @Test A R₀ := _.
Definition bar₀ {HR : @Test A R₀} : @Test A (fun x => R₀ x) := _.

Inductive R₁ : A -> Prop :=.

Definition foo₁ {HR : @Test A (fun x => R₁ x)} : @Test A R₁ := _.
Definition bar₁ {HR : @Test A R₁} : @Test A (fun x => R₁ x) := _.

End Unary.

(* For good measure, check that η-expansion works with functions of arity 2 *)

Module Binary.

Class Test {A B : Type} (R : A -> B -> Prop) : Prop := {}.

Axiom A B : Type.

Definition foo {R : A -> B -> Prop} {HR : @Test A B (fun x y => R x y)} : @Test A B R := _.
Definition bar {R : A -> B -> Prop} {HR : @Test A B R} : @Test A B (fun x y => R x y) := _.

Axiom R₀ : A -> B -> Prop.

Definition foo₀ {HR : @Test A B (fun x y => R₀ x y)} : @Test A B R₀ := _.
Definition bar₀ {HR : @Test A B R₀} : @Test A B (fun x y => R₀ x y) := _.

Inductive R₁ : A -> B -> Prop :=.

Definition foo₁ {HR : @Test A B (fun x y => R₁ x y)} : @Test A B R₁ := _.
Definition bar₁ {HR : @Test A B R₁} : @Test A B (fun x y => R₁ x y) := _.

End Binary.

(* Check that η-expansion correctly handles holes in patterns *)

Module RelCapture.

Inductive paths {A : Type} (a : A) : A -> Type :=.

Class Contr (A : Type) : Type := {}.

#[export]
Declare Instance myInst {X : Type} (x : X) : Contr {y : X & @paths X x y}.

Definition foo {X : Type} (x : X) : Contr {y' : X & @paths X x y'} := _.

End RelCapture.

Module Collapse.

Class Test {A : Type} (R : A -> Prop) : Prop := {}.

Axiom t : Type -> Type.
Axiom map2 : forall [elt : Type], (elt -> Prop) -> t elt -> Prop.

Definition lift_relation {A} (R : A -> Prop) (defaultA : A) (m1 : t A) : Prop :=
  map2 (fun x1 => R defaultA) m1.

Definition Q : Prop -> Prop := fun H => H.

#[local]
Declare Instance lift0 : forall (A : Type) (default : A) (R : A -> Prop),
   Test (fun x : A => Q (R x)) ->
   Test (fun x : t A => Q (lift_relation R default x)).

Definition foo {A R} {HR : @Test A R} {default} : Test (@lift_relation A R default) := _.

End Collapse.

From Stdlib Require List.

Module FMap.

Import List. Import ListNotations.

Monomorphic Universe i o.
Class FMap (M : Type@{i} -> Type@{o}) :=
  fmap : forall {A:Type@{i}} {B:Type@{o}}, (A -> B) -> M A -> M B.
Global Arguments fmap {_ _ _ _} _ !_ / : assert.
#[local]
Monomorphic Instance fmap_list@{a b} : FMap (fun T => list T) :=
  fun (A : Type@{a}) (B : Type@{b}) f => @map A B f.
Fail Fail Monomorphic Constraint i < list.u0.
Fail Fail Example instance_found := fmap (id) [1;2;3].

End FMap.
