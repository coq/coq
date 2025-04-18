Require Export
  Corelib.Classes.CMorphisms.

Definition R (x y : unit) : Type := unit.

Instance :
  Reflexive R.
Proof.
  intros x.
  constructor.
Qed.

Instance :
  Proper (R ==> R ==> flip arrow) R.
Proof.
  intros [] [] _ [] [] _ _.
  constructor.
Qed.

Instance :
  forall x, Proper (R ==> flip arrow) (R x).
Proof.
  intros x.
  partial_application_tactic;
    typeclasses eauto.
Abort.

Instance : Params R 1 := {}.
Instance :
  forall x, Proper (R ==> flip arrow) (R x).
Proof.
  intros x.
  (* should fail in the presence of a params instance *)
  Fail partial_application_tactic.
Abort.
