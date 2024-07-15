Module S.
  #[local] Set Printing Unfolded Projection As Match.
  #[projections(primitive=yes)]
  Record r (u : unit) := { r_car : Type }.

  Axiom u : unit.

  Definition rO : r u -> r u := fun o => {| r_car := option (r_car u o) |}.

  Goal forall o, exists M, M (r_car u o)= r_car u (rO o).
  Proof.
    intros. eexists _.
    Timeout 1 refine (eq_refl _).
  Qed.
End S.

Module T.
  #[local] Set Printing Unfolded Projection As Match.
  #[projections(primitive=yes)]
  Record r (u : unit) := { r_car : Type }.

  Axiom u : unit.
  Axiom v : forall i : nat, r u.

  Goal forall i, exists P, P (v i) = r_car u (v i).
  Proof.
    intros. eexists _.
    (* Unable to unify "r (v i)" with "?P (v i)". *)
    refine (eq_refl _).
  Qed.
End T.
