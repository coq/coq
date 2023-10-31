Inductive foo :=
| F0 : nat -> foo
| F1 : bar -> foo

with bar :=
| B1 : foo -> bar.

Section Def.

(* Putting this variable here breaks simpl below *)

Variable f : nat -> nat.

Fixpoint eval_foo x :=
  match x with
  | F0 n => f n
  | F1 x => eval_bar x
  end

with eval_bar x :=
  match x with
  | B1 x => eval_foo x
  end.

End Def.

Goal forall f x, eval_foo f (F1 x) = eval_bar f x.
Proof.
intros. simpl.
match goal with [ |- eval_bar f x = eval_bar f x ] => idtac end.
trivial.
Qed.
