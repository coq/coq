Inductive T : bool -> SProp := .

Goal forall (x:T true) (y:T false), match x return bool with end = match y return bool with end.
Proof.
  intros.
  Fail reflexivity.
Abort.
