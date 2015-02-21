Module Type S.

Axiom foo : nat.

End S.

Module M : S.

Definition bar := 0.
Definition foo := bar.

End M.

Print All Dependencies M.foo.
