(* Check that constraints on locals are preserved by discharging *)

Definition Type2 := Type.

Section A.
  Let Type1 : Type2 := Type.
  Definition Type1' := Type1.
End A.

Fail Definition Inconsistency : Type1' := Type2.
