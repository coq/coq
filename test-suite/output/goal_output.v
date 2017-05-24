(* From
   - https://coq.inria.fr/bugs/show_bug.cgi?id=5529
   - https://coq.inria.fr/bugs/show_bug.cgi?id=5537
 *)

Print Nat.t.
Timeout 1 Print Nat.t.

Lemma toto: False.
Set Printing All.
Show.
Abort.

