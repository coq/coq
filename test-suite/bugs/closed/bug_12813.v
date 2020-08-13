Record test := make_test {
    proj1 : nat ;
    proj2 : nat
  }.

Module M.

Definition test := 1.
Definition proj1 := 2.
Definition proj2 := 2.

Definition test2 := make_test proj1 proj2.

End M.

From Coq Require Extraction.

Extraction Language OCaml.

Extraction TestCompile M.
