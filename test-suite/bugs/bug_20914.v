Sort s.

Polymorphic Definition foo@{s';u} (A:Univ@{s';u}) (a:A) := a.

(* slightly eta expanded so "s" appears in a sort and in the instance *)
Definition bla A := foo@{s;Set} A.
