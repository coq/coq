Set Implicit Arguments.
Generalizable All Variables.

Record Category {obj : Type} :=
  {
    Morphism : obj -> obj -> Type;

    Identity : forall x, Morphism x x;
    Compose : forall s d d', Morphism d d' -> Morphism s d -> Morphism s d';
    LeftIdentity : forall a b (f : Morphism a b), Compose (Identity b) f = f
  }.


Section DiscreteAdjoints.

  Let C := {|
            Morphism := (fun X Y : Type => X -> Y);
            Identity := (fun X : Type => (fun x : X => x));
            Compose := (fun _ _ _ f g => (fun x => f (g x)));
            LeftIdentity := (fun X Y p => @eq_refl _ p : (fun x : X => p x) = p)
          |}.
  Variable ObjectFunctor : C = C.

  Goal True.
  Proof.
    subst C.
    revert ObjectFunctor.
    intro ObjectFunctor.
    simpl in ObjectFunctor.
    revert ObjectFunctor.
  Abort.

End DiscreteAdjoints.
