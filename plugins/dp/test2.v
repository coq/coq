Require Import ZArith.
Require Import Classical.
Require Import List.

Open Scope list_scope.
Open Scope Z_scope.

Dp_debug.
Dp_timeout 3.
Require Export zenon.

Definition neg (z:Z) : Z := match z with
  | Z0 => Z0
  | Zpos p => Zneg p
  | Zneg p => Zpos p
  end.

Goal forall z, neg (neg z) = z.
  Admitted.

Open Scope nat_scope.
Print plus.

Goal forall x, x+0=x.
  induction x; ergo.
  (* simplify resoud le premier, pas le second *)
  Admitted.

Goal 1::2::3::nil = 1::2::(1+2)::nil.
  zenon.
  Admitted.

Definition T := nat.
Parameter fct : T -> nat.
Goal fct O = O.
 Admitted.

Fixpoint even (n:nat) : Prop :=
  match n with
  O => True
  | S O => False
  | S (S p) => even p
  end.

Goal even 4%nat.
  try zenon.
  Admitted.

Definition p (A B:Set) (a:A) (b:B) : list (A*B) := cons (a,b) nil.

Definition head :=
fun (A : Set) (l : list A) =>
match l with
| nil => None (A:=A)
| x :: _ => Some x
end.

Goal forall x, head _ (p _ _ 1 2) = Some x -> fst x = 1.

Admitted.

(*
BUG avec head prédéfini : manque eta-expansion sur A:Set

Goal forall x, head _ (p _ _ 1 2) = Some x -> fst x = 1.

Print value.
Print Some.

zenon.
*)

Inductive IN (A:Set) : A -> list A -> Prop :=
  | IN1 : forall x l, IN A x (x::l)
  | IN2: forall x l, IN A x l -> forall y, IN A x (y::l).
Implicit Arguments IN [A].

Goal forall x, forall (l:list nat), IN x l -> IN x (1%nat::l).
  zenon.
Print In.
