(* Testing a regression from 8.5beta1 to 8.5beta2 in evar-evar tactic unification problems *)


Inductive test : nat -> nat -> nat -> nat -> Prop :=
  | test1 : forall m n, test m n m n.

Goal test 1 2 3 4.
erewrite f_equal2 with (f := fun k l => test _ _ k l).
