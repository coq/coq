Axiom T : nat -> Prop.
Axiom f : forall x, T x.
Arguments f & x.

Lemma test : (f (1 + _) : T 2) = f 2.
match goal with
| |- (f (1 + 1) = f 2) => idtac
| |- (f 2 = f 2) => fail (* Issue 11140 *)
| |- _ => fail
end.
Abort.
