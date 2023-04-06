
Module Qualification.
  (* test that field mismatch errors print the qualified fields *)

  Module Type EasyT. Definition x := O. End EasyT.
  Module EasyM. Definition x := S O. End EasyM.

  Fail Module Easytest <: EasyT := EasyM.

  Module Type A. Module B. Module C. Definition x := O. End C. End B. End A.
  Module Type A'. Module B. Module C. Definition x := S O. End C. End B. End A'.
  Module Av. Include A'. End Av.

  Fail Module test <: A := Av.
  (* was Error: Signature components for field C do not match: the body of definitions differs. *)

  Module Type FT (X:A). End FT.
  Module F (X:A'). End F.

  Fail Module Ftest <: FT := F.

  Module Type FXT.
    Module F (X:A). End F.
  End FXT.

  Module FX.
    Module F (X:A'). End F.
  End FX.

  Fail Module FXtest <: FXT := FX.
End Qualification.

Module PrintBound.
  (* printing an inductive from a bound module in an error from the
   command where the bound module is introduced *)
  Module Type E. End E.

  Module Type T. Inductive t : Prop := . Parameter v : t -> t. End T.

  Module Type FE(A:E). Inductive t : Prop :=. Parameter v : t -> Prop. End FE.

  Module Type FT(A:T). End FT.

  Module VE. End VE.

  Fail Module F (A1:FE VE) (A2:FT A1).
End PrintBound.
