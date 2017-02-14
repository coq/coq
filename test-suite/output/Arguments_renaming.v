Fail Arguments eq_refl {B y}, [B] y.
Arguments identity A _ _.
Arguments eq_refl A x : assert.
Arguments eq_refl {B y}, [B] y : rename.

Check @eq_refl.
Check (eq_refl (B := nat)).
Print eq_refl.
About eq_refl.

Goal 3 = 3.
apply @eq_refl with (B := nat).
Undo.
apply @eq_refl with (y := 3).
Undo.
pose (y := nat).
apply (@eq_refl y) with (y0 := 3).
Qed.

Section Test1.

Variable A : Type.

Inductive myEq B (x : A) : A -> Prop := myrefl : B -> myEq B x x.

Global Arguments myrefl {C} x _ : rename.
Print myrefl.
About myrefl.

Fixpoint myplus T (t : T) (n m : nat) {struct n} :=
  match n with O => m | S n' => S (myplus T t n' m) end.

Global Arguments myplus {Z} !t !n m : rename.

Print myplus.
About myplus.
Check @myplus.

End Test1.
Print myrefl.
About myrefl.
Check myrefl.

Print myplus.
About myplus.
Check @myplus.

Fail Arguments eq_refl {F g}, [H] k.
Fail Arguments eq_refl {F}, [F] : rename.
Fail Arguments eq_refl {F F}, [F] F : rename.
Fail Arguments eq {F} x [z] : rename.
Fail Arguments eq {F} x z y.
Fail Arguments eq {R} s t.

