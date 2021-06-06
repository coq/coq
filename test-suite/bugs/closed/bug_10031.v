Require Import Uint63 ZArith.

Open Scope uint63_scope.

Goal False.
cut (let (q, r) := (0, 0) in (φ q, φ r) = (9223372036854775808%Z, 0%Z));
  [discriminate| ].
Fail (change (0, 0) with (diveucl_21 1 0 1); apply diveucl_21_spec).
Abort.
