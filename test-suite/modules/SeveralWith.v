Module Type S.
Parameter A : Type.
End S.

Module Type ES.
Parameter A : Type.
Parameter eq : A -> A -> Type.
End ES.

Module Make
  (AX : S)
  (X : ES with Definition A := AX.A with Definition eq := @eq AX.A).
