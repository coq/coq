#[local] Hint Extern 0 False => idtac+admit : core.

Goal False.
Proof.
  Succeed solve [debug auto].
  Succeed solve [auto].
Abort.
