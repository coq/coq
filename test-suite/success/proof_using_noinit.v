(* -*- coq-prog-args: ("-noinit"); -*- *)

Section A.
Variable A : Prop.
Hypothesis a : A.
Lemma b : A.
Proof using a.
Admitted.
End A.
