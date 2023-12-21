Axiom functional_extensionality_dep :
  forall {A : Type} {B : A -> Type} (f g : forall x : A, B x),
    (forall x : A, f x = g x) -> f = g.
