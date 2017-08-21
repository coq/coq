Set Primitive Projections.
Record unit : Set := tt {}.
Fail Check fun x : unit => eq_refl : tt = x.
Fail Check fun x : unit => eq_refl : x = tt.
Fail Check fun x y : unit => (eq_refl : x = tt) : x = y.
Fail Check fun x y : unit => eq_refl : x = y.

Record ok : Set := tt' { a : unit }.

Record nonprim : Prop := { undef : unit }.
Record prim : Prop := { def : True }.
