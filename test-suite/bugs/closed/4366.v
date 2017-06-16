Fixpoint stupid (n : nat) : unit :=
match n with
| 0 => tt
| S n =>
  let () := stupid n in
  let () := stupid n in
  tt
end.

Goal True.
Proof.
pose (v := stupid 24).
Timeout 4 vm_compute in v.
exact I.
Qed.
