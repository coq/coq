(* Check correct use of if-then-else predicate annotation (cf bug 690) *)

Check fun b : bool =>
 if b as b0 return (if b0 then b0 = true else b0 = false)
 then refl_equal true
 else refl_equal false.

