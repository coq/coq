Require Import TestSuite.admit.
Set Implicit Arguments.
Record foo := { fx : nat }.
Set Primitive Projections.
Record bar := { bx : nat }.
Definition Foo (f : foo) : f = f.
  destruct f as [fx]; destruct fx; admit.
Defined.
Definition Bar (b : bar) : b = b.
  destruct b as [fx]; destruct fx; admit.
Defined.
Goal forall f b, Bar b = Bar b -> Foo f = Foo f.
  intros f b.
  destruct f, b. 
  simpl.
  Fail progress unfold Bar. (* success *)
  Fail progress unfold Foo. (* failed to progress *)
  reflexivity.
Qed.
