Set Primitive Projections.

CoInductive stream (A : Type) := cons { hd : A; tl : stream A }.

CoFixpoint const {A} (x : A) := cons A x (const x).

Goal forall A x, (@const A x).(tl _) = const x.
Proof.
intros.
simpl.
match goal with [ |- ?x = ?x ] => idtac end.
Abort.
