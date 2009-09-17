Set Implicit Arguments.
Unset Strict Implicit.

Module M.
  Definition a (s : Set) := s.
  Print a.
End M.

Print M.a.

Module K.
  Definition app (A B : Set) (f : A -> B) (x : A) := f x.
  Module N.
    Definition apap (A B : Set) := app (app (A:=A) (B:=B)).
    Print app.
    Print apap.
  End N.
  Print N.apap.
End K.

Print K.app.
Print K.N.apap.

Module W := K.N.

Print W.apap.
