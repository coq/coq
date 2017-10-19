(* The synthesis of the elimination predicate may fail if algebric *)
(* universes are not cautiously treated *)

Check (fun b : bool => if b then Type else nat).

(* Check correct use of if-then-else predicate annotation (cf BZ#690) *)

Check fun b : bool =>
 if b as b0 return (if b0 then b0 = true else b0 = false)
 then refl_equal true
 else refl_equal false.

