From Stdlib Require Import Program.
From Stdlib Require Import Wf_nat.

Inductive T := MkT.

Definition sizeOf (t : T) : nat
    := match t with
       | MkT => 1
       end.
Parameter vect : nat -> Type.
Program Fixpoint idType (t : T) (n := sizeOf t) (b : vect n) {measure n} : T
    := match t with
       | MkT => MkT
       end.
