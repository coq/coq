Lemma TrueI : unit -> True.
Proof. easy. Qed.

Create HintDb db.

#[local] Hint Extern 99 => shelve : db.
#[local] Hint Extern 0 (True) => apply TrueI : db.
#[local] Hint Extern 0 (unit) => exact tt : db.

Goal True.
Proof.
  Succeed (solve [unshelve auto with db nocore]).
  Succeed (solve [unshelve typeclasses eauto with db nocore]).
  Succeed (solve [unshelve eauto with db nocore]).
Abort.
