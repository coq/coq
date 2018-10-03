(* Check that constraints on definitions are preserved by discharging *)

Section A.
  Definition Type2 := Type.
  Definition Type1 : Type2 := Type.
End A.

Fail Definition Inconsistency : Type1 := Type2.
