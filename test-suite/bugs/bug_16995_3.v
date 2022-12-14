
Lemma foo : True.
Proof.
  pose (forall (x:Type(*@u*)) (z:(fun y:Type@{_}(*@v*) => tt) x = tt), True).
  (* {u v} |= u <= v, undefined v *)

  assert True by abstract exact I.
  (* {u} |= [], v := u
     v is still in the ustate's ugraph *)

  Monomorphic Axiom bla : Type.
  (* ustate regenerated from global env, v is not in the ustate's ugraph! *)

  pose (eq_refl : P = (forall (x:Type) (z:(fun y:Type => tt) x = tt), True)).
  (* anomaly in univ.repr, universe undefined *)

  exact I.
Qed.
