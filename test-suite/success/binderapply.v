Require Import Coq.Init.Tactics FunctionalExtensionality.

Goal forall A f g , (forall a b c d e : A, f a b c d e = g a b c d e :> A) -> f = g.
Proof.
  intros A f g H.
  apply functional_extensionality_dep in H.
  let T := type of H in has_evar T.
  Back 2.
  repeat binder apply @functional_extensionality in H.
  exact H.
Defined.
