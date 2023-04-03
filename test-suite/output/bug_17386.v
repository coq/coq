Goal True.
evar (x:nat).
pose (y:=1).
let _ := constr:(eq_refl : x = 1) in idtac.
Show.
(*
x := 1
y := 1

should be
x, y := 1
 *)
Abort.
