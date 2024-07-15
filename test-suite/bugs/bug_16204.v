Set Implicit Arguments.
Set Universe Polymorphism.
Unset Universe Checking.

Class IsProp (A : Type) : Prop :=
  irrel (x y : A) : x = y.

Class IsProofIrrel : Prop :=
  proof_irrel (A : Prop) :: IsProp A.

Class IsPropExt : Prop :=
  prop_ext (A B : Prop) (a : A <-> B) : A = B.

Class IsTypeExt : Prop :=
  type_ext (A B : Type) (f : A -> B) (g : B -> A)
  (r : forall x : A, g (f x) = x) (s : forall y : B, f (g y) = y) :
  A = B.

Local Instance anomaly
  `{IsProofIrrel} `{IsTypeExt} : IsPropExt.
Proof.
  intros A B [f g]. eapply (type_ext f g).
  - intros x. apply irrel.
  - intros y. apply irrel.
Qed.
