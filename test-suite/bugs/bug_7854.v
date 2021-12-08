Set Primitive Projections.

CoInductive stream (A : Type) := cons {
  hd : A;
  tl : stream A;
}.

CoFixpoint const {A} (x : A) := cons A x (const x).

Check (@eq_refl _ (const tt) <<: tl unit (const tt) = const tt).
