Class EqDec T := { eqb : T -> T -> bool }.

Section TC.

#[local] Instance unit_EqDec : EqDec unit := { eqb := fun _ _ => true }.

End TC.

#[local] Existing Instance unit_EqDec.

Existing Class EqDec.
