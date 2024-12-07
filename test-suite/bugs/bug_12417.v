Require Import List.
Require Import Recdef.

Notation "A :: B" := (cons A B).
Notation "[]" := nil.
Notation "[[ A ]]" := (A :: nil).

Inductive tm :=
| E: nat -> tm
| L: list tm -> tm.

Definition T := list tm.

Fixpoint max_list (p: nat) (l: list nat) : nat :=
  match l with
  | [] => p
  | n :: l' => max_list (Init.Nat.max n p) l'
  end.

Fixpoint depth (t: tm) : nat :=
  match t with
  | E _ => 0
  | L l => 1 + max_list 0 (map depth l)
  end.

Fixpoint sum_depth (l: T) : nat :=
  match l with
  | [] => 0
  | n :: l' => (depth n) + sum_depth l'
  end.

Fail Function sum_total (l: T) {wf sum_depth l} : nat :=
  match l with
  | [] => 0
  | t :: l' =>
    (match t with
      | E n => n
      | L li => sum_total li
      end) + sum_total l'
  end.
