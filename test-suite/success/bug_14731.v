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
