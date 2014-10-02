Section foo.
  Variable A : Type.
  Let B := A.

  Hint Unfold B.

  Goal False.
    clear B. autounfold with core.
  Abort.
End foo.
