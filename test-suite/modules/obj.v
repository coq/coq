Set Implicit Arguments.
Unset Strict Implicit.

Module M.
  Definition a (s : Set) := s.
  Print Term a.
End M.

Print Term M.a.

Module K.
  Definition app (A B : Set) (f : A -> B) (x : A) := f x.
  Module N.
    Definition apap (A B : Set) := app (app (A:=A) (B:=B)).
    Print Term app.
    Print Term apap.
  End N.
  Print Term N.apap.
End K.

Print Term K.app.
Print Term K.N.apap.

Module W := K.N.

Print Term W.apap.
