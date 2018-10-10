(* Using tactic "change" under binders *)

Definition add2 n := n +2.
Goal (fun n => n) = (fun n => n+2).
change (?n + 2) with (add2 n).
match goal with |- _ = (fun n => add2 n) => idtac end. (* To test the presence of add2 *)
Abort.
