(* This requires cumulativity *)

Definition Type2 := Type.
Definition Type1 := Type : Type2.

Lemma lem1 : (True->Type1)->Type2.
Intro H.
Apply H.
Exact I.
Qed.

Lemma lem2 : (A:Type)(P:A->Type)(x:A)((y:A)(x==y)->(P y))->(P x).
Auto.
Qed.

Lemma lem3 : (P:Prop)P.
Intro P ; Pattern P.
Apply lem2.
Abort.
