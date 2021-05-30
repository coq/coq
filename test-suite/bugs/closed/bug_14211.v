Axiom SForUp: nat -> nat.

Declare Custom Entry snippet.

Notation "## s " := s (at level 0, s custom snippet at level 100).
Notation "'for' i0 " := (SForUp i0) (in custom snippet at level 0, i0 ident).

(* Another check without a custom entry *)

Check fun i => ## for i.

Notation "'succ' i0 " := (S i0) (at level 0, i0 ident).
Check fun i => S i.
