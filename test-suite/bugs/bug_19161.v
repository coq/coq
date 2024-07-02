Set Universe Polymorphism.
Set Printing Universes.
Section test.
  Universe u.

  (* all 3 should fail or succeed together *)

  Check Type@{u} : Type@{Set+1}.
  Definition a := Type@{u} : Type@{Set+1}.
  Check (fun A  : Type@{Set+1} =>  A) Type@{u}.
End test.
