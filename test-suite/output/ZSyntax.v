Require ZArith.
Check `32`.
Check [f:nat->Z]`(f O) + 0`.
Check [x:positive]`(POS (xO x))`.
Check [x:positive]`(POS x)+1`.
Check [x:positive]`(POS x)`.
Check [x:positive]`(NEG (xO x))`.
Check [x:positive]`(POS (xO x))+0`.
Check [x:positive]`(Zopp (POS (xO x)))`.
Check [x:positive]`(Zopp (POS (xO x)))+0`.
Check `(inject_nat O)+1`.
Check (Zplus `0` (inject_nat (plus O O))).
Check `(inject_nat O)=0`.

(* Submitted by Pierre Casteran *)
Require Arith.
Check (Zplus `0` (inject_nat (11))).
