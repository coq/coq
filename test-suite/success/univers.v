(* This requires cumulativity *)

Definition Type2 := Type.
Definition Type1 := Type : Type2.

Goal (True->Type1)->Type2.
Intro H.
Apply H.

Lemma gg : (A:Type)(P:A->Type)(x:A)((y:A)(x==y)->(P y))->(P x).
Auto.
Qed.

Lemma titi : (P:Prop)P.
Intro P ; Pattern P.
Apply gg.
Qed.
