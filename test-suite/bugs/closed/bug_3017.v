Class A := {}.
  Class B {T} `(A) := { B_intro : forall t t' : T, t = t' }.
  Lemma foo T (t t' : T) : t = t'.
    erewrite @B_intro.
    reflexivity.
  Abort.
