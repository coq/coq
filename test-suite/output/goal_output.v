(* From
   - https://coq.inria.fr/bugs/show_bug.cgi?id=5529
   - https://coq.inria.fr/bugs/show_bug.cgi?id=5537
 *)

Print Term Nat.t.
Timeout 1 Print Term Nat.t.

Lemma toto: False.
Set Printing All.
Show.
Abort.

