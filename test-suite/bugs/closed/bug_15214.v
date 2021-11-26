#[local] Hint Extern 0 => fail 1 : foo.

Goal False.
Proof.
eauto with foo.
Abort.
