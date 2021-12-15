Inductive foo := C1 : bar -> foo with bar := C2 : foo -> bar.

Lemma L1 : foo -> True with L2 : bar -> True.
intros; clear L1 L2; abstract (exact I).
intros; exact I.
Qed.
