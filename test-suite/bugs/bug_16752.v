Axiom P : SProp.
Axioms a b : P.
Axiom Q : P->Prop.
Axiom q : Q b.
Axiom zog : forall p:P, Q p -> unit.

Lemma foobar : zog a q = tt.
Proof.
  set (u := zog _ q).
  (* should be "u = tt" *)
  match goal with |- u = tt => idtac end.
Abort.
