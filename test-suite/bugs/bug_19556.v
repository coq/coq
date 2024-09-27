
Section Lists.

  Universe ua.

  Variable A : Type@{ua}.

  Definition tl (l:list A) :=
    match l with
      | nil => nil
      | cons a m => m
    end.

  (* unification used to force the opposite constraint *)
  Constraint list.u0 < ua.

End Lists.
