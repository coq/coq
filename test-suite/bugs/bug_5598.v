(* Checking when discharge of an existing class is possible *)
Section foo.
  Context {T} (a : T) (b : T).
  Let k := eq_refl a.
  Existing Class eq.
  Fail Global Existing Instance k.
  Existing Instance k.
End foo.
