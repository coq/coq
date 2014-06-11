Set Primitive Projections.

CoInductive stream A := cons { hd : A; tl : stream A }.

CoFixpoint id {A} (s : stream A) := cons _ (hd s) (id (tl s)).

Lemma id_spec : forall A (s : stream A), id s = s.
Proof.
intros A s.
Fail Timeout 1 change (id s) with (cons _ (hd (id s)) (tl (id s))).
