Set Keyed Unification.

Section foo.
Variable f : nat -> nat. 

Definition g := f.

Variable lem : g 0 = 0.

Goal f 0 = 0.
Proof.
  Fail rewrite lem.
Abort.

Declare Equivalent Keys @g @f.
(** Now f and g are considered equivalent heads for subterm selection *)
Goal f 0 = 0.
Proof.
  rewrite lem.
  reflexivity.
Qed.

Print Equivalent Keys.
End foo.
