Module Type A.
Parameter a : nat.
End A.

Module B (mA : A).
Ltac cbv_a := cbv [mA.a].
End B.
