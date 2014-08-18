Set Primitive Projections.
Set Implicit Arguments.

CoInductive stream A := cons { hd : A; tl : stream A }.

CoFixpoint id {A} (s : stream A) := cons (hd s) (id (tl s)).

Lemma id_spec : forall A (s : stream A), id s = s.
Proof.
intros A s.
Fail change (id s) with (cons (hd (id s)) (tl (id s))).
