
Axiom T:Prop.

Lemma foo
  {x y : T -> Type}
  : True.
Proof.
  Fail match goal with
  | [ H : ?T, H' : ?T |- _ ] => idtac
  end.
Abort.
