(* Check that constraints on locals are preserved by discharging *)

Definition Type2 := Type.

Section A.
  Local Type1 := Type : Type2.
  Definition Type1' := Type1.
End A.

Definition Inconsistency := Type2 : Type1'.
