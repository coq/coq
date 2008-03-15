Inductive vector {A : Type} : nat -> Type :=
| vnil : vector 0
| vcons : A -> forall {n'}, vector n' -> vector (S n').

Require Import Coq.Program.Program.

Program Definition head {A : Type} {n : nat} (v : vector A (S n)) : vector A n :=
  match v with
    | vnil => !
    | vcons a n' v' => v'
  end.

Fixpoint app {A : Type} {n m : nat} (v : vector A n) (w : vector A m) : vector A (n + m) :=
  match v in vector _ n return vector A (n + m) with
    | vnil => w
    | vcons a n' v' => vcons a (app v' w)
  end.
