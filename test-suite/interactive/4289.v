(* Checking backtracking with modules which used to fail due to an
   hash-consing bug *)

Module Type A.
  Axiom B : nat.
End A.
Module C (a : A).
  Include a.
  Definition c : nat := B.
End C.
Back 4.
Module C (a : A).
  Include a.
  Definition c : nat := B.
