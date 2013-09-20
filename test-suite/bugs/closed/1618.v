Inductive A: Set :=
| A1: nat -> A.

Definition A_size (a: A) : nat :=
  match a with
    | A1 n => 0
  end.

Require Import Recdef.

Function n3 (P: A -> Prop) (f: forall n, P (A1 n)) (a: A) {struct a} : P a :=
  match a  return (P a) with
    | A1 n => f n
  end.


Function n1 (P: A -> Prop) (f: forall n, P (A1 n)) (a: A) {measure A_size a} :
P
a :=
  match a return (P a) with
    | A1 n => f n
  end.

