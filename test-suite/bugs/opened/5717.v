Fail Definition foo@{i} (A : Type@{i}) (l : list A) :=
  match l with
  | nil => nil (* Universe {Top.4} is unbound. *)
  | cons _ t => t
  end.
