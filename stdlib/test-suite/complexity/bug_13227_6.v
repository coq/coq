From Stdlib Require Import Lia ZArith.
Open Scope Z_scope.

Unset Lia Cache.

(* Expected time < 1.00s *)
Goal forall (x2 x3 x : Z)
     (H : 0 <= 1073741824 * x + x2 - 67146752)
     (H0 : 0 <= -8192 + x2)
     (H1 : 0 <= 34816 + - x2)
     (H2 : 0 <= -1073741824 * x - x2 + 1073741823),
  False.
Proof.
  intros.
  Time lia.
Qed.
