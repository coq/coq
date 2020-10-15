(* From
   - https://coq.inria.fr/bugs/show_bug.cgi?id=5529
   - https://coq.inria.fr/bugs/show_bug.cgi?id=5537
 *)

Print Nat.t.
Timeout 1 Print Nat.t.

Set Printing All.
Lemma toto: True/\True.
Proof.
split.
Show.
Set Printing Goal Names.
Show.
Unset Printing Goal Names.
assert True.
- idtac.
Show.
Set Printing Goal Names.
Show.
Set Printing Unfocused.
Show.
Unset Printing Goal Names.
Show.
Unset Printing Unfocused.
  auto.
Show.
Set Printing Goal Names.
Show.
Unset Printing Goal Names.
- auto.
Show.
Set Printing Goal Names.
Show.
Unset Printing Goal Names.
Abort.
