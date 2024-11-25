Require Import Program.Tactics.

Set Universe Polymorphism.

Module Bug11766.

Program Definition bla@{} : nat := _.
Next Obligation.
  let x := constr:(Type) in exact 0.
Defined. (* was unbound univ *)

Program Definition bla'@{} : nat := _.
Solve Obligations with let x := constr:(Type) in exact 0. (* was unbound univ *)

End Bug11766.

From Corelib Require Import ssreflect.

Module Bug11988.

#[local]
Obligation Tactic := idtac.

Section Foo.

Universe u.

Variable T : Type@{u}.
Variable op : T -> T -> T.
Hypothesis opC : forall x y, op x y = op y x.

Program Definition foo@{} x y : {z : T & z = op x y} :=
  existT _ (op y x) _.

Next Obligation.
move=> /= x y.
by rewrite -[RHS]opC.
Qed. (* should work even though rewrite [RHS] adds a spurious universe *)

End Foo.

End Bug11988.

Module ExampleFrom11902.

Local Unset Universe Polymorphism.

Program Definition foo (X : Type) : Type :=
  let x := X in forall x : x, _.

Next Obligation.
refine nat.
Defined.

End ExampleFrom11902.
