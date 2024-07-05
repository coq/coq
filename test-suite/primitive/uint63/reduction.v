Require Import PrimInt63.

Open Scope uint63_scope.

Definition div_eucl_plus_one i1 i2 :=
  let (q,r) := diveucl i1 i2 in
  (add q 1, add r 1)%uint63.

Definition rcbn := Eval cbn in div_eucl_plus_one 3 2.
Check (eq_refl : rcbn = (2, 2)).

Definition rcbv := Eval cbv in div_eucl_plus_one 3 2.
Check (eq_refl : rcbv = (2, 2)).

Definition rvmc := Eval vm_compute in div_eucl_plus_one 3 2.
Check (eq_refl : rvmc = (2, 2)).

Definition f n m :=
  match (compare n 42)%uint63 with
  | Lt => add n m
  | _ => mul 2 m
  end.

Goal forall n, (compare n 42)%uint63 = Gt -> f n 256 = 512%uint63.
  intros. unfold f.
  cbn. Undo. cbv. (* Test reductions under match clauses *)
  rewrite H. reflexivity.
Qed.
