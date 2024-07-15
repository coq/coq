Module S.
  #[local] Set Printing Unfolded Projection As Match.
  #[projections(primitive=yes)]
  Record state (u : unit) :=
    { p : nat -> nat }.

  Parameter (u : unit).
  Parameter (s1 s2 : state u).

  (* Unifying the compatibility constant with the primitive projection *)
  Goal exists n, ltac:(exact (p u)) s1 n = p _ s1 1.
  Proof.
    eexists _.
    (* Testing both orientations of the unification problem *)
    lazymatch goal with |- ?a = ?b => unify a b end.
    lazymatch goal with |- ?a = ?b => unify b a end.
    Succeed apply eq_refl.
    symmetry.
    apply eq_refl.
  Qed.

  (* Unifying primitive projections with [?h ?a1 .. ?aN] when [N] is bigger than
     the number of parameters plus 1. This must fail. *)
  Axiom H : forall (B : Type) (f : forall (_ : nat) (_ : nat) (_ : nat), B) (x1 y1 x2 y2 x3 y3 : nat),
      @eq B (f x1 x2 x3) (f y1 y2 y3).
  Goal p _ s1 = p _ s2.
  Proof.
    (* [apply H] never succeeds. The test below only makes sure that it does not
       loop endlessly or overflow the stack. *)
    Timeout 1 (first [apply H | idtac]).
  Abort.

  (* Unifying primitive projections with [?h ?a1 .. ?aN] when [N] is exactly the
     number of parameters plus 1. This must succeed. *)
  Goal exists (a : forall u, state u -> nat -> nat) (b : unit) c, a b c = p u s1.
  Proof.
    eexists _, _, _.
    (* Testing both orientations of the unification problem *)
    Succeed apply eq_refl.
    symmetry.
    apply eq_refl.
  Qed.

  (* Unifying primitive projections with [?h ?a1 .. ?aN] when [N] is exactly the
     number of parameters plus 1 plus the number of proper arguments to the
     projection. This must succeed. *)
  Goal exists (a : forall u, state u -> nat -> nat) (b : unit) c d, a b c d = p u s1 0.
  Proof.
    eexists _, _, _, _.
    (* Testing both orientations of the unification problem *)
    Succeed apply eq_refl.
    symmetry.
    apply eq_refl.
  Qed.

  (* Unifying primitive projections with [?h ?a1 .. ?aN] when [N] is less than
     the number of parameters plus 1 plus the number of proper arguments to the
     projection. The head evar [?h] is unified with a partial application of the
     projection. This must succeed. *)
  Goal exists (a : state u -> nat -> nat) (b : state u), a b = p u s1.
  Proof.
    eexists _, _.
    (* Testing both orientations of the unification problem *)
    Succeed apply eq_refl.
    symmetry.
    apply eq_refl.
  Qed.

End S.

Module I.
  #[local] Set Printing Unfolded Projection As Match.
  Record cmra := Cmra { cmra_car : Type }.
  Record ucmra := { ucmra_car : Type }.

  #[projections(primitive=yes)]
  Record ofe (n : nat) := Ofe { ofe_car : Type }.

  Axiom n : nat.

  Definition ucmra_ofeO := fun A : ucmra => @Ofe n (ucmra_car A).

  (* Canonical Structure cmra_ofeO := fun A : cmra => @Ofe n (cmra_car A). *)

  Canonical Structure ucmra_cmraR :=
    fun A : ucmra =>
      Cmra (ucmra_car A).

  Axiom A : ucmra.
  Axiom bla : forall (A : cmra), cmra_car A.
  Goal ofe_car n (ucmra_ofeO A).
  Proof.
    apply @bla.
  Qed.
End I.
