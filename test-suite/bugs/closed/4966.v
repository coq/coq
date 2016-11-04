(* Interpretation of auto as an argument of an ltac function (i.e. as an ident) was wrongly "auto with *" *)

Axiom proof_admitted : False.
Hint Extern 0 => case proof_admitted : unused.
Ltac do_tac tac := tac.

Goal False.
  Set Ltac Profiling.
  Fail solve [ do_tac auto ].
Abort.
