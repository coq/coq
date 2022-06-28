Set Universe Polymorphism.
Set Printing Universes.
Require Import CMorphisms.
Require Setoid.

Definition Subset@{A P} (A : Type@{A}) := A -> Type@{P}.

Definition Included@{A P} {A : Type@{A}} :
  Subset@{A P} A -> Subset@{A P} A -> Type@{max(A,P)} :=
  fun U V => forall a : A, U a -> V a.

Definition Intersection@{A P Q PQ} {A} :
  Subset@{A P} A -> Subset@{A Q} A -> Subset@{A PQ} A :=
  fun U V a => (U a * V a)%type.

Theorem Intersection_Included_l : forall A (U V : Subset A),
  Included (Intersection U V) U.
Proof.
firstorder.
Qed.

#[export] Instance Included_PreOrder : forall A, PreOrder (@Included A).
Proof.
firstorder.
Qed.

Lemma Intersection_Prop {A} {U : Subset A} :
  Included (Intersection U U) U.
Proof.
rewrite Intersection_Included_l.
Abort.
