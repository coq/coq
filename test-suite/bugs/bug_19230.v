(* This inductive cannot be template *)
Inductive foo@{u} (A:Type@{u}) : Type@{u+1} := .
Fail Check foo (foo (foo nat)).
