Axiom T : nat -> Prop.
Axiom f : forall x, T x.
Arguments f & x.

Fail Check f 3 : T 2.

Lemma test : (f (1 + _) : T 2) = f 2.
Proof.
  match goal with
  | |- (f (1 + 1) = f 2) => idtac
  | |- (f 2 = f 2) => idtac 1; fail 99 (* Issue 11140 *)
  end.
  reflexivity.
Qed.
