Inductive proc : Type -> Prop :=
| Tick : proc unit
.

Inductive exec :
  forall T, proc T -> T -> Prop :=
| ExecTick :
    exec _ (Tick) tt
.

Lemma foo :
  exec _ Tick tt ->
  True.
Proof.
  intros H.
  remember Tick as p.
  Fail induction H.
Abort.
