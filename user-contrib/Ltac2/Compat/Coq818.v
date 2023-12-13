Local Set Warnings "-masking-absolute-name".

Require Ltac2.Array.

Module Export Ltac2.
  Module Array.
    Export Ltac2.Array.
    Ltac2 empty () := empty.
  End Array.
End Ltac2.
