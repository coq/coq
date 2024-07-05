Require Import BinNums PrimInt63 Uint63Axioms.

Open Scope uint63_scope.

Goal False.
cut (let (q, r) := (0, 0) in (to_Z q, to_Z r) = ((Zpos (xO (xO (xO (xO (xO (xO (xO (xO (xO (xO (xO (xO (xO (xO (xO (xO (xO (xO (xO (xO (xO (xO (xO (xO (xO (xO (xO (xO (xO (xO (xO (xO (xO (xO (xO (xO (xO (xO (xO (xO (xO (xO (xO (xO (xO (xO (xO (xO (xO (xO (xO (xO (xO (xO (xO (xO (xO (xO (xO (xO (xO (xO (xO xH)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (* 9223372036854775808%Z *), Z0));
  [discriminate| ].
Fail (change (0, 0) with (diveucl_21 1 0 1); apply diveucl_21_spec).
Abort.
