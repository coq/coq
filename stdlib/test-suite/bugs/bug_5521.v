From Stdlib Require Export Utf8.
From Stdlib Require Export Program.
From Stdlib Require Export CEquivalence.
From Stdlib Require Export CMorphisms.
From Stdlib Require Setoid.

(* Notation "f ≃ g" := (equiv f g) (at level 79, only parsing). *)

Reserved Infix "~>" (at level 90, right associativity).

Class Category := {
  ob : Type;

  uhom := Type : Type;
  hom : ob -> ob -> uhom where "a ~> b" := (hom a b);

  id {A} : A ~> A;
  compose {A B C} (f: B ~> C) (g : A ~> B) : A ~> C
    where "f ∘ g" := (compose f g);

  id_left  {X Y} (f : X ~> Y) : id ∘ f = f;

  comp_assoc {X Y Z W} (f : Z ~> W) (g : Y ~> Z) (h : X ~> Y) :
    f ∘ (g ∘ h) = (f ∘ g) ∘ h
}.

Class Isomorphism `{C : Category} (X Y : @ob C) : Type := {
  to   :: hom X Y;
  from :  hom Y X

  (* If these two lines are commented out, the rewrite works at the bottom. *)
  ; iso_to_from : compose to from = id
  ; iso_from_to : compose from to = id
}.

#[export] Program Instance isomorphism_equivalence `{C : Category} :
  Equivalence Isomorphism.
Next Obligation.
  repeat intro.
  unshelve econstructor; try exact id;
  rewrite id_left; reflexivity.
Defined.
Next Obligation.
  repeat intro; destruct X.
  unshelve econstructor; auto.
Defined.
Next Obligation.
  repeat intro; destruct X, X0.
  unshelve econstructor;
  first [ exact (compose to1 to0)
        | exact (compose from0 from1)
        | rewrite <- !comp_assoc;
          rewrite (comp_assoc to0);
          rewrite iso_to_from0;
          rewrite id_left; assumption
        | rewrite <- !comp_assoc;
          rewrite (comp_assoc from1);
          rewrite iso_from_to1;
          rewrite id_left; assumption ].
Defined.

Goal forall `{C : Category} {X Y Z : @ob C}
            (f : Isomorphism Y Z)
            (g : Isomorphism X Y),
    Isomorphism X Z.
  intros.
  rewrite g.
Abort.
