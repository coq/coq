Require Import TestSuite.admit.
Set Primitive Projections.
Axiom admit : forall {T}, T.
Notation "( x ; y )" := (existT _ x y) : fibration_scope.
Open Scope fibration_scope.
Notation "x .1" := (projT1 x) (at level 3) : fibration_scope.
Inductive paths {A : Type} (a : A) : A -> Type := idpath : paths a a where "x = y" := (@paths _ x y) : type_scope.
Set Implicit Arguments.
Delimit Scope category_scope with category.
Record PreCategory := { object :> Type ; morphism : object -> object -> Type }.
Local Open Scope category_scope.
Class IsIsomorphism {C : PreCategory} {s d} (m : morphism C s d) := { morphism_inverse : morphism C d s }.
Class Isomorphic {C : PreCategory} s d := { morphism_isomorphic :> @morphism C s d ; isisomorphism_isomorphic :> IsIsomorphism morphism_isomorphic }.
Coercion morphism_isomorphic : Isomorphic >-> morphism.
Local Infix "<~=~>" := Isomorphic (at level 70, no associativity) : category_scope.
Definition idtoiso (C : PreCategory) (x y : C) (H : x = y) : Isomorphic x y := admit.
Record NotionOfStructure (X : PreCategory) := { structure :> X -> Type }.
Record Smorphism (X : PreCategory) (P : NotionOfStructure X) (xa yb : { x : X & P x }) := { f : morphism X xa.1 yb.1 }.
Definition precategory_of_structures X (P : NotionOfStructure X) : PreCategory.
Proof.
  refine (@Build_PreCategory _ (@Smorphism _ P)).
Defined.
Section sip.
  Variable X : PreCategory.
  Variable P : NotionOfStructure X.

  Let StrX := @precategory_of_structures X P.

  Definition sip_isotoid (xa yb : StrX) (f : xa <~=~> yb) : xa = yb.
    admit.
  Defined.

  Lemma structure_identity_principle_helper (xa yb : StrX)
        (x : xa <~=~> yb) : Smorphism P xa yb.
  Proof.
    refine ((idtoiso (precategory_of_structures P) (sip_isotoid x) : @morphism _ _ _) : morphism _ _ _).
(* Toplevel input, characters 24-95:
Error:
In environment
X : PreCategory
P : NotionOfStructure X
StrX := precategory_of_structures P : PreCategory
xa : object StrX
yb : object StrX
x : xa <~=~> yb
The term "morphism_isomorphic:@morphism (precategory_of_structures P) xa yb"
has type "@morphism (precategory_of_structures P) xa yb"
while it is expected to have type "morphism ?40 ?41 ?42". *)
