Section S.
  Variable A : Type.
  Fail Primitive int : let x := A in Set := #int63_type.
  Fail Primitive add := #int63_add.
End S.

(* [Primitive] should be forbidden in sections, otherwise its type after cooking
will be incorrect:

Check int.

*)
