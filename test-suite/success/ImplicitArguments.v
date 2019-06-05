
Axiom foo : forall (x y z t : nat), nat.

Arguments foo {_} _ [z] {t}.
Check (foo 1).
Arguments foo {_} _ [z] [t].
Check (foo 1).

Definition foo1 n [m] := n + m.
Check (foo1 1).

Definition foo2 [n] := n + n.
Check foo2.
Arguments foo2 {n}.
Check foo2.

Inductive vector [A : Type] : nat -> Type :=
| vnil : vector 0
| vcons : A -> forall {n'}, vector n' -> vector (S n').

Check vector.
Arguments vector A : clear implicits.


Definition foo6 (x:=1) : forall {n:nat}, n=n := fun n => eq_refl.

Require Import Coq.Program.Program.

Program Definition head {A : Type} {n : nat} (v : vector A (S n)) : vector A n :=
  match v with
    | vnil => !
    | vcons a v' => v'
  end.

Fixpoint app {A : Type} {n m : nat} (v : vector A n) (w : vector A m) : vector A (n + m) :=
  match v in vector _ n return vector A (n + m) with
    | vnil => w
    | vcons a v' => vcons a (app v' w)
  end.

(* Test sharing information between different hypotheses *)

Parameters (a:_) (b:a=0).

(* These examples were failing due to a lifting wrongly taking let-in into account *)

Definition foo6 (x:=1) : forall {n:nat}, n=n := fun n => eq_refl.

Fixpoint foo7 (x:=1) (n:nat) {p:nat} {struct n} : nat.
Abort.

(* Some example which should succeed with local implicit arguments *)

Inductive A {P:forall m {n}, n=m -> Prop} := C : P 0 eq_refl -> A.
Inductive B (P:forall m {n}, n=m -> Prop) := D : P 0 eq_refl -> B P.
