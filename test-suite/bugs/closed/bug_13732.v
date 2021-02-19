Module Sort.
  Set Printing Universes.

  Implicit Types TT : Type.

  Check fun TT => nat.
End Sort.

Module Ref.
  Set Universe Polymorphism.

  Axiom tele : Type.

  Implicit Types TT : tele.
  Check fun TT => nat.
End Ref.
