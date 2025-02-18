Ltac show H :=
  let T := type of H in
  let s := type of T in
  idtac s.

Module M1.
  Goal True.
  Proof.
  refine (let H := _ in _).
  show H.
  Set Printing Universes.
  show H.
  Set Printing Sort Qualities.
  show H.
  Unset Printing Universes.
  show H.
  Abort.
End M1.

Module M2.
  Set Universe Polymorphism.
  Lemma foo@{s|u|} (A : Type@{s|u}) : True.
  Proof.
  Check A.
  Set Printing Universes.
  Check A.
  Set Printing Sort Qualities.
  Check A.
  Unset Printing Universes.
  Check A.
  Abort.
End M2.
