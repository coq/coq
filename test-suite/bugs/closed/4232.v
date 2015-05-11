Require Import Setoid Morphisms Vector.

Class Equiv A := equiv : A -> A -> Prop.
Class Setoid A `{Equiv A} := setoid_equiv:> Equivalence (equiv).

Global Declare Instance vec_equiv {A} `{Equiv A} {n}: Equiv (Vector.t A n).
Global Declare Instance vec_setoid A `{Setoid A} n : Setoid (Vector.t A n).

Global Declare Instance tl_proper1 {A} `{Equiv A} n:
  Proper ((equiv) ==> (equiv))
         (@tl A n).

Lemma test:
  forall {A} `{Setoid A} n (xa ya: Vector.t A (S n)),
    (equiv xa ya) -> equiv (tl xa) (tl ya).
Proof.
  intros A R HA n xa ya Heq.
  setoid_rewrite Heq.
  reflexivity.
Qed.
