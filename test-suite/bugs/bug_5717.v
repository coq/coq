Definition foo@{i} (A : Type@{i}) (l : list A) :=
  match l with
  | nil => nil
  | cons _ t => t
  end.
