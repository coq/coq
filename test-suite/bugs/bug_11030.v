Inductive I : let z := 0 in Set := C : I.
Check match C with C => true end.
(* Was failing due to prepare_predicate_from_arsign_tycon not robust to let-in *)

From Stdlib Require Import Arith Program.

Module Bug11586.

Inductive vector (A : Type) : nat -> Type :=
  | nil : vector A O
  | cons : forall {n : nat}, A -> vector A n -> vector A (S n).

Arguments vector A n.
Arguments nil {A}.
Arguments cons {A n} x xs.

(** Program was failing due to a List.rev issue *)

Program Fixpoint nth'' {A : Type} {m : nat}
  (xs : vector A m) (n : {i : nat | i < m}) : A :=
  match xs, n with
  | nil, i => !
  | cons y ys, O => y
  | cons y ys, (S q) => nth'' ys (exist _ q _)
  end.
Next Obligation. Admitted.
Next Obligation. Admitted.

End Bug11586.
