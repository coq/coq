Goal forall x, x = 0 -> S x = 7 -> x = 22 .
Proof.
replace 0 with 33.
Undo.
intros x H H0.
replace x with 0.
Undo.
replace x with 0 in  |- *.
Undo.
replace x with 1 in *.
Undo.
replace x with 0 in *|- *.
Undo.
replace x with 0 in *|-.
Undo.
replace x with 0 in H0 .
Undo.
replace x with 0 in H0 |- * .
Undo.

replace x with 0 in H,H0 |- * .
Undo.
Admitted.

(* This failed at some point when "replace" started to support arguments
   with evars but "abstract" did not supported any evars even defined ones *)

Class U.
Lemma l (u : U) (f : U -> nat) (H : 0 = f u) : f u = 0.
replace (f _) with 0 by abstract apply H.
reflexivity.
Qed.
