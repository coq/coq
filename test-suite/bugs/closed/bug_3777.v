Unset Strict Universe Declaration.
Module WithoutPoly.
  Unset Universe Polymorphism.
  Definition foo (A : Type@{i}) (B : Type@{i}) := A -> B.
  Set Printing Universes.
  Definition bla := ((@foo : Set -> _ -> _) : _ -> Type -> _).
  (* ((fun A : Set => foo A):Set -> Type@{Top.55} -> Type@{Top.55})
:Set -> Type@{Top.55} -> Type@{Top.55}
     : Set -> Type@{Top.55} -> Type@{Top.55}
(*  |= Set <= Top.55
         *) *)
End WithoutPoly.
Module WithPoly.
  Set Universe Polymorphism.
  Definition foo (A : Type@{i}) (B : Type@{i}) := A -> B.
  Set Printing Universes.
  Fail Check ((@foo : Set -> _ -> _) : _ -> Type -> _).
