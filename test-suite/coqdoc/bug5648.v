Lemma a : True.
Proof.
auto.
Qed.

Variant t :=
| A | Add | G | Goal | L | Lemma | P | Proof .

Definition d x :=
  match x with
  | A => 0
  | Add => 1
  | G => 2
  | Goal => 3
  | L => 4
  | Lemma => 5
  | P => 6
  | Proof => 7
  end.
