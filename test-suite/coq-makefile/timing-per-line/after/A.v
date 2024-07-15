Require IntDef.
Declare Reduction comp := native_compute.
Definition foo0 := Eval comp in (IntDef.Z.div_eucl, IntDef.Z.div_eucl).
Definition foo1 := Eval comp in (foo0, foo0).
