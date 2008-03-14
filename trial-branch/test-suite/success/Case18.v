(* Check or-patterns *)

Definition g x :=
  match x with ((((1 as x),_) | (_,x)), (_,(2 as y))|(y,_)) => (x,y) end.

Check (refl_equal _ : g ((1,2),(3,4)) = (1,3)).

Check (refl_equal _ : g ((1,4),(3,2)) = (1,2)).

Fixpoint max (n m:nat) {struct m} : nat :=
  match  n, m with
  | S n', S m' => S (max n' m')
  | 0, p | p, 0 => p
  end.

(* Check bug #1477 *)

Inductive I : Set :=
  | A : nat -> nat -> I
  | B : nat -> nat -> I.

Definition foo (x:I) : nat :=
  match x with
    | A a b | B b a => S b
  end.

