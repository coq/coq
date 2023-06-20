Module Test0.

Class Junk.

Class Dummy : Type :=
  #[global] something :: Junk.

End Test0.

Section TestSomethingGlobal.
Variable d : Test0.Dummy.
Type _ d : Test0.Junk.
End TestSomethingGlobal.
