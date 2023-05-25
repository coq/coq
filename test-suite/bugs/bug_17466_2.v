
Definition UU := Type.

Unset Universe Checking.

Lemma foo {X : UU}  : Prop.
Proof.
  Comments hi.
  pose (egf := fun e : _ =>  e : X).
  revert egf.
  match goal with |- ?g => let _ := type of g in idtac end.
Abort.
