Set Universe Polymorphism.
Unset Strict Universe Declaration.
Set Primitive Projections.

Axiom Relation@{u} : Type@{u} -> Type@{u}.
Inductive GraphQuotient {A : Type@{i}} (R : Relation A) : Type@{u} :=
| gq : A -> GraphQuotient R.

Arguments gq {A R} a.

Axiom IsConnMap@{i} : forall {A B : Type@{i}}, (A -> B) -> Type@{i}.

Definition class_of@{i k} {A : Type@{i}} (R : Relation@{i} A) : A -> GraphQuotient@{i k} R := gq.

Axiom issurj_class_of : forall {A : Type} (R : Relation A), IsConnMap (class_of R).

Record Homomorphism {σ} {A B : σ -> Type} : Type := BuildHomomorphism
  { def_hom : forall (s : σ), A s -> B s }.

Arguments Homomorphism {σ}.

Arguments BuildHomomorphism {σ A B} def_hom.

Definition QuotientAlgebra  {σ : Type} (A : σ -> Type) (Φ : forall s, Relation (A s)) (s : σ) : Type :=
  GraphQuotient (Φ s).

Definition def_hom_quotient {σ} {A : σ -> Type} (Φ : forall s, Relation (A s)) (s : σ) (x : A s) :
  (QuotientAlgebra A Φ) s := class_of (Φ s) x.
Definition hom_quotient {σ} {A : σ -> Type} (Φ : forall s, Relation (A s)) : Homomorphism A (QuotientAlgebra A Φ) :=
  BuildHomomorphism (def_hom_quotient Φ).

Lemma surjection_quotient : forall {σ} {A : σ -> Type} (Φ : forall s, Relation (A s)) s, IsConnMap (def_hom (hom_quotient Φ) s).
Proof.
intros σ A Φ s.
apply issurj_class_of.
Qed.
