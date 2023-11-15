Inductive thing : SProp :=.

Fixpoint foobar (x:thing) {struct x} : thing.
Proof.
  Guarded.
  exact x.
  Guarded.
Defined.
