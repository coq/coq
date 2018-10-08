(* Checking Print Assumptions relatively to a bound module *)

Module Type Typ.
  Parameter Inline(10) t : Type.
End Typ.
Module  Terms_mod (SetVars : Typ).
Print Assumptions SetVars.t.
End Terms_mod.
