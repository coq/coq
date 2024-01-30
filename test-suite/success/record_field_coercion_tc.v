Module RecordNothing.
Class B.
Record A := { ab : B }.
Parameter a : A.
Fail Check a : B.  (* no coercion *)
Existing Class A.
Existing Instance a.
Fail Type _ : B.  (* no typeclass instance *)
End RecordNothing.

Module RecordCoercion.
Class B.
Record A := { ab :> B }.
Parameter a : A.
Check a : B.  (* coercion *)
Existing Class A.
Existing Instance a.
Fail Type _ : B.  (* no typeclass instance *)
End RecordCoercion.

Module RecordTC.
Class B.
Record A := { ab :: B }.
Parameter a : A.
Fail Check a : B.  (* no coercion *)
Existing Class A.
Existing Instance a.
Type _ : B.  (* typeclass instance *)
End RecordTC.

Module RecordCoercionTC.
Class B.
Record A := { ab ::> B }.
Parameter a : A.
Check a : B.  (* coercion *)
Existing Class A.
Existing Instance a.
Type _ : B.  (* typeclass instance *)
End RecordCoercionTC.

Module ClassNothing.
Class B.
Class A := { ab : B }.
Parameter a : A.
Fail Check a : B.  (* no coercion *)
Existing Instance a.
Fail Type _ : B.  (* no typeclass instance *)
End ClassNothing.

Module ClassCoercion.
Class B.
Class A := { ab :> B }.
Parameter a : A.
Check a : B.  (* coercion *)
Existing Instance a.
Fail Type _ : B.  (* no typeclass instance *)
End ClassCoercion.

Module ClassTC.
Class B.
Class A := { ab :: B }.
Parameter a : A.
Fail Check a : B.  (* no coercion *)
Existing Instance a.
Type _ : B.  (* typeclass instance *)
End ClassTC.

Module ClassCoercionTC.
Class B.
Class A := { ab ::> B }.
Parameter a : A.
Check a : B.  (* coercion *)
Existing Instance a.
Type _ : B.  (* typeclass instance *)
End ClassCoercionTC.
