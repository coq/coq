Require Coq.ZArith.BinInt.
Declare Reduction comp := native_compute.
Definition foo0 := Eval comp in (Coq.ZArith.BinInt.Z.div_eucl, Coq.ZArith.BinInt.Z.div_eucl).
Definition foo1 := Eval comp in (foo0, foo0).
