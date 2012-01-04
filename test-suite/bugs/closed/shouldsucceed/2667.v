(* Check that not too many arguments are given to Arguments Scope *)

Inductive stmt : Type := Sskip: stmt | Scall : nat -> stmt.
Bind Scope Cminor with stmt.
Fail Arguments Scope Scall [_ Cminor ]. (* At most 1 argument expected *)
