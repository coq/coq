Theorem thm (A:Prop) (H:exists m:nat, True) : True.
destruct H as ([|],?).
assert A.
Show Proof. (* was raising Not_found since 8.7 *)
Abort.
