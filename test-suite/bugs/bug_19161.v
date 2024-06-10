Set Universe Polymorphism.
Set Printing Universes.
Section test.
  Universe u.

  (* all 3 should fail or succeed together *)

  Fail Check Type@{u} : Type@{Set+1}.
  Fail Definition a := Type@{u} : Type@{Set+1}.
  Fail Check (fun A  : Type@{Set+1} =>  A) Type@{u}.
End test.
