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

