(* Check that constraints on definitions are preserved by discharging *)

Section A.
  Definition Type2 := Type.
  Definition Type1 := Type : Type2.
End A.

Definition Inconsistency := Type2 : Type1.
