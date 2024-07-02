Require Stdlib.ZArith.BinInt.
Declare Reduction comp :=     vm_compute.
Definition foo0 := Eval comp in (Stdlib.ZArith.BinInt.Z.div_eucl, Stdlib.ZArith.BinInt.Z.div_eucl).
Definition foo1 := Eval comp in (foo0, foo0).
