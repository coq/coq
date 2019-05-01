Check (fun b : bool => match b with true => Set  | false => unit end).
Check (fun b : bool => match b with true => unit | false => Set  end).
Check (
  let X : Type@{_} := _ in
  let a : X := unit in
  (* already at this point, X := Set *)
  let b : X := Set in 3).
Definition foo (b : bool) : Set :=
  match b return _ with true => unit | false => nat end.
Definition foo' (b : bool) : Set :=
  match b with true => unit | false => nat end.
Definition foo'' (b : bool) : Prop :=
  match b return _ with true => True | false => False end.
Check (nat = Set).
