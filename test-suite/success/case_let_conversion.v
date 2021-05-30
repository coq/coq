Axiom checker_flags : Set.

Inductive Box (R : Type) : Type := box : Box R.

Inductive typing (H : checker_flags) : Type :=
| type_Rel : typing H -> typing H
| type_Case : let i := tt in Box (typing H) -> typing H.

Definition unbox (P : Type) (b : Box P) := match b with box _ => 0 end.

Definition size (H : checker_flags) (d : typing H) : nat.
Proof.
revert d.
fix size 1.
destruct 1.
- exact (size d).
- exact (unbox _ b).
Defined.

Definition foo (H : checker_flags) (a : typing H) :
  size H (type_Rel H a) = size H a.
Proof.
simpl.
reflexivity.
Qed.

Definition bar (H : checker_flags) (a : typing H) :
  size H (type_Rel H a) = size H a.
Proof.
vm_compute.
reflexivity.
Qed.

Definition qux (H : checker_flags) (a : typing H) :
  size H (type_Rel H a) = size H a.
Proof.
native_compute.
reflexivity.
Qed.
