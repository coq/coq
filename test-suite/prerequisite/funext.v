Axiom functional_extensionality_dep :
  forall {A : Type} {B : A -> Type} (f g : forall x : A, B x),
    (forall x : A, f x = g x) -> f = g.

Lemma functional_extensionality {A B} (f g : A -> B) :
  (forall x, f x = g x) -> f = g.
Proof.
  intros ; eauto using @functional_extensionality_dep.
Qed.
