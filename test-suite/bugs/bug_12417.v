Declare ML Module "rocq-runtime.plugins.funind".

Inductive tm :=
| E: nat -> tm
| L: list tm -> tm.

Definition T := list tm.

Fixpoint max_list (p: nat) (l: list nat) : nat :=
  match l with
  | nil => p
  | cons n l' => max_list (Init.Nat.max n p) l'
  end.

Fixpoint map {A B} (f : A -> B) (l : list A) : list B :=
match l with
| nil => nil
| cons x l => cons (f x) (map f l)
end.

Fixpoint depth (t: tm) : nat :=
  match t with
  | E _ => 0
  | L l => 1 + max_list 0 (map depth l)
  end.

Fixpoint sum_depth (l: T) : nat :=
  match l with
  | nil => 0
  | cons n l' => (depth n) + sum_depth l'
  end.

Fail Function sum_total (l: T) {wf sum_depth l} : nat :=
  match l with
  | nil => 0
  | cons t l' =>
    (match t with
      | E n => n
      | L li => sum_total li
      end) + sum_total l'
  end.
