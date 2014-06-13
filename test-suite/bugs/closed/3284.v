(* Several bugs:
- wrong env in pose_all_metas_as_evars leading to out of scope instance of evar
- check that metas posed as evars in pose_all_metas_as_evars were
  resolved was not done
*)

Axiom functional_extensionality_dep :
  forall {A : Type} {B : A -> Type} (f g : forall x : A, B x),
    (forall x : A, f x = g x) -> f = g.

Goal forall A B C (f g : forall (x : A) (y : B x), C x y), forall x:A, (forall x y, f x y = g x y) -> True.
Proof.
  intros A B C f g x H.
  Fail apply @functional_extensionality_dep in H.
  Fail apply functional_extensionality_dep in H.
  eapply functional_extensionality_dep in H.
Abort.

Goal forall A B C (f g : forall (x : A) (y : B x), C x y), forall x:A, (forall x y, f x y = g x y) -> True.
Proof.
  intros A B C f g x H.
  specialize (H x).
  apply functional_extensionality_dep in H.
