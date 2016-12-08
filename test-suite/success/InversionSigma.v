Section inversion_sigma.
  Local Unset Implicit Arguments.
  Context A (B : A -> Prop) (C C' : forall a, B a -> Prop)
          (D : forall a b, C a b -> Prop) (E : forall a b c, D a b c -> Prop).

  (* Require that, after destructing sigma types and inverting
     equalities, we can subst equalities of variables only, and reduce
     down to [eq_refl = eq_refl]. *)
  Local Ltac test_inversion_sigma :=
    intros;
    repeat match goal with
           | [ H : sig _ |- _ ] => destruct H
           | [ H : sigT _ |- _ ] => destruct H
           | [ H : sig2 _ _ |- _ ] => destruct H
           | [ H : sigT2 _ _ |- _ ] => destruct H
           end; simpl in *;
    inversion_sigma;
    repeat match goal with
           | [ H : ?x = ?y |- _ ] => is_var x; is_var y; subst x; simpl in *
           end;
    match goal with
    | [ |- eq_refl = eq_refl ] => reflexivity
    end.

  Goal forall (x y : { a : A & { b : { b : B a & C a b } & { d : D a (projT1 b) (projT2 b) & E _ _ _ d } } })
              (p : x = y), p = p.
  Proof. test_inversion_sigma. Qed.

  Goal forall (x y : { a : A | { b : { b : B a | C a b } | { d : D a (proj1_sig b) (proj2_sig b) | E _ _ _ d } } })
              (p : x = y), p = p.
  Proof. test_inversion_sigma. Qed.

  Goal forall (x y : { a : { a : A & B a } & C _ (projT2 a) & C' _ (projT2 a) })
              (p : x = y), p = p.
  Proof. test_inversion_sigma. Qed.

  Goal forall (x y : { a : { a : A & B a } | C _ (projT2 a) & C' _ (projT2 a) })
              (p : x = y), p = p.
  Proof. test_inversion_sigma. Qed.
End inversion_sigma.
