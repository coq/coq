Require Setoid.

Parameter A : Set.

Axiom eq_dec : (a,b :A) {a=b}+{~a=b}.

Inductive set : Set :=
|Empty : set
|Add : A -> set -> set.

Fixpoint In [a:A; s:set] : Prop :=
Cases s of
|Empty => False
|(Add b s') => a=b \/ (In a s')
end.

Definition same [s,t:set] : Prop :=
(a:A) (In a s) <-> (In a t).

Lemma setoid_set : (Setoid_Theory set same).

Unfold same; Split.
Red; Auto.

Red.
Intros.
Elim (H a); Auto.

Intros.
Elim (H a); Elim (H0 a).
Split; Auto.
Save.

Add Setoid set same setoid_set.

Add Morphism In : In_ext.
Unfold same; Intros a s t H; Elim (H a); Auto.
Save.

Lemma add_aux : (s,t:set) (same s t) ->
  (a,b:A)(In a (Add b s)) -> (In a (Add b t)).
Unfold same; Induction 2; Intros.
Rewrite H1.
Simpl; Left; Reflexivity.

Elim (H a).
Intros.
Simpl; Right.
Apply (H2 H1).
Save.

Add Morphism Add : Add_ext.
Split; Apply add_aux.
Assumption.

Rewrite H.
Apply Seq_refl.
Exact setoid_set.
Save.

Fixpoint remove [a:A; s:set] : set :=
Cases s of
|Empty => Empty
|(Add b t) => Cases (eq_dec a b) of
              |(left _) => (remove a t)
              |(right _) => (Add b (remove a t))
              end
end.

Lemma in_rem_not : (a:A)(s:set) ~(In a (remove a (Add a Empty))).

Intros.
Setoid_replace (remove a (Add a Empty)) with Empty.
Unfold same.
Split.
Simpl.
Intro H; Elim H.

Simpl.
Case (eq_dec a a).
Intros e ff; Elim ff.

Intros; Absurd a=a; Trivial.

Auto.
Save.

Parameter P :set -> Prop.
Parameter P_ext : (s,t:set) (same s t) -> (P s) -> (P t).

Add Morphism P : P_extt.
Exact P_ext.
Save.

Lemma test_rewrite : (a:A)(s,t:set)(same s t) -> (P (Add a s)) -> (P (Add a t)).
Intros.
Rewrite <- H.
Rewrite H.
Setoid_rewrite <- H.
Setoid_rewrite H.
Setoid_rewrite <- H.
Trivial.
Save.

