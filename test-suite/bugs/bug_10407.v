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

Module Example3.

(* With local parameters and indices *)

Inductive A (n:=0) : let p:=1 in Type :=
| C : forall (B : Type) (C := unit) (x : B * C) (y:=0) , A.

Program Definition f (v : A) : unit :=
  match v with
  | C B (x1,x2) => _
  end.

End Example3.

Require Import JMeq.

Module Example4.

Inductive A (n:=0) : forall n, let p:=n in bool -> Type :=
| C : forall (B : Type) (C := unit) (x : B * C) (y:=0) , A y true.

Program Definition f n b (v : A n b) : unit :=
  match v with
  | C B (x1,x2) => _
  end.

End Example4.
