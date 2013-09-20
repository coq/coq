(* Submitted by David Nowak *)

(* Simpler to forbid the definition of n as a global than to write it
   S.n to keep n accessible... *)

Section S.
Variable n : nat.
Fail Inductive P : Set :=
    n : P.
