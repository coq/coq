Ltac foo :=
match goal with
| [ x : ?T |- _ ] => refine (ltac:(exact x))
end.

Goal nat -> nat.
Proof.
intros n.
foo.
Qed.
