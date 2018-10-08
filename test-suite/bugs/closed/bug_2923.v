Module Type SIGNATURE1.
  Inductive IndType: Set :=
    | AConstructor.
End SIGNATURE1.

Module Type SIGNATURE2.
  Declare Module M1: SIGNATURE1.
End SIGNATURE2.

Module M2 (Module M1_: SIGNATURE1) : SIGNATURE2.
  Module M1 := M1_.
End M2.
