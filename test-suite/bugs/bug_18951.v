Require Import Derive.

Derive foo : nat in True as bar.
Proof. Admitted. (* Was an anomaly *)
Check foo.
Check bar.

Derive foo' in True as bar'.
Proof.
Fail Admitted. (* Has still evars *)
Unshelve.
3:exact nat.
Fail Admitted.
Abort.
