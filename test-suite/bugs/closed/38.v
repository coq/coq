Require Import Setoid.

Variable A : Set.

Inductive liste : Set :=
| vide : liste
| c : A -> liste -> liste.

Inductive e : A -> liste -> Prop :=
| ec : forall (x : A) (l : liste), e x (c x l)
| ee : forall (x y : A) (l : liste), e x l -> e x (c y l).

Definition same := fun (l m : liste) => forall (x : A), e x l <-> e x m.

Definition same_refl (x:liste) : (same x x).
  unfold same; split; intros; trivial.
Qed.

Goal forall (x:liste), (same x x).
  intro.
  apply (same_refl x).
Qed.
