
Module Type ELEM.
  Parameter A : Set.
  Parameter x : A.
End ELEM.

Module Nat.
    Definition A := nat.
    Definition x := 0.
End Nat.

Module List (X: ELEM).
  Inductive list : Set :=
    | nil : list
    | cons : X.A -> list -> list.

  Definition head (l : list) := match l with
                                | nil => X.x
                                | cons x _ => x
                                end.

  Definition singl (x : X.A) := cons x nil.

  Lemma head_singl : forall x : X.A, head (singl x) = x.
  auto.
  Qed.

End List.

Module N := List Nat.
