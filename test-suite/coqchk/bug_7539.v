Set Primitive Projections.

CoInductive Stream : Type := Cons { tl : Stream }.

Fixpoint Str_nth_tl (n:nat) (s:Stream) : Stream :=
  match n with
  | O => s
  | S m => Str_nth_tl m (tl s)
  end.

CoInductive EqSt (s1 s2: Stream) : Prop := eqst {
  eqst_tl : EqSt (tl s1) (tl s2);
}.

Axiom EqSt_reflex : forall (s : Stream), EqSt s s.

CoFixpoint map (s:Stream) : Stream := Cons (map (tl s)).

Lemma Str_nth_tl_map : forall n s, EqSt (Str_nth_tl n (map s)) (map (Str_nth_tl n s)).
Proof.
induction n.
+ intros; apply EqSt_reflex.
+ cbn; intros s; apply IHn.
Qed.

Definition boom : forall s, tl (map s) = map (tl s) := fun s => eq_refl.
