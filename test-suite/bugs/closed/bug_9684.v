Set Primitive Projections.

Record foo := mkFoo { proj1 : bool; proj2 : bool }.

Definition x := mkFoo true false.
Definition proj x := proj2 x.

Lemma oops : proj = fun x => proj1 x.
Proof. Fail native_compute; reflexivity. Abort.

(*
Lemma bad : False.
assert (proj1 x = proj x).
  rewrite oops; reflexivity.
discriminate.
Qed.

Print Assumptions bad.
*)
