(* Was #4524 *)
Definition foo (x : Type) : True /\ True.
Proof.
split.
- exact I.
  Show Proof. (* Was not finding an evar name at some time *)
