Set Universe Polymorphism.
Fixpoint type_vector@{i} (n : nat) : Type@{i+1} :=
  match n return Type@{i+1} with O => unit | S m => type_vector m * Type@{i} end.
Definition bar@{i j} (b : bool) : Type@{max(i+1,j+1)} :=
  match b return Type@{max(i+1,j+1)} with
  | true => Type@{i}
  | false => Type@{j}
  end.
Check (fun (b : bool) (x : False) =>
  match x
  return match b with true => unit | false => Set end
  with end).
