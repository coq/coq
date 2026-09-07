Set Universe Polymorphism.

Section Foo.

Universes a z b u.
Constraint a < b.
Constraint z <= b.
Constraint b <= u.

Print Universes Subgraph (a z b u).
(* Set <= a, Set <= z, Set < b, Set <= u, a < b, z <= b, b <= u *)

Fail Constraint u <= Set.
(* The above constraint does not fail despite leading to an inconsistent graph. *)

Print Universes Subgraph (a z b u).
(* Set <= a, z = a, b = a, u = a *)

Definition foo := tt.

End Foo.

About foo.
(* Any attempt at using the constant results in a universe error. *)
(* Universe inconsistency. Cannot enforce Var(3) <= Set. *)
