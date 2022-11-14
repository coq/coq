Goal True.
Proof.
refine (let ev := (fun (n : nat) => _) in _).
revert ev.
instantiate (1 := nat).
instantiate (1 := n).
constructor.
Qed.
