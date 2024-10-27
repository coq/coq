Require Coq.Program.Tactics.

Module Example1.

Inductive A : Type :=
| C : forall (B := unit) (x : B) , A.

Program Definition f (v : A) : unit :=
  match v with
  | C x => _
  end.

End Example1.

Module Example2.

(* A bit more complex *)

Inductive A : Type :=
| C : forall (B : Type) (C := unit) (x : B * C) (y:=0) , A.

Program Definition f (v : A) : unit :=
  match v with
  | C B (x1,x2) => _
  end.

End Example2.
