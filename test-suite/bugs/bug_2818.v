Module M.

Local Ltac t := exact I.
Ltac u := t.

End M.

Goal True.
Proof.
M.u.
Qed.
