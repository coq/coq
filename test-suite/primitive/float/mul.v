Require Import PrimFloat.

Open Scope float_scope.

Definition huge := 0x1p+1023%float.  (* Z.ldexp one 1023%Z. *)
Definition tiny := 0x0.8p-1022%float.  (* Z.ldexp one (-1023)%Z. *)

Check (eq_refl : huge * tiny = one).

Check (eq_refl : huge * huge = infinity).

Check (eq_refl : one * nan = nan).

Check (eq_refl : infinity * infinity = infinity).

Check (eq_refl : infinity * neg_infinity = neg_infinity).

Check (eq_refl : zero * zero = zero).
Check (eq_refl : neg_zero * zero = neg_zero).
Check (eq_refl : neg_zero * neg_zero = zero).
Check (eq_refl : zero * neg_zero = neg_zero).

Check (eq_refl : huge * neg_infinity = neg_infinity).

Check (eq_refl : one * tiny = tiny).
Check (eq_refl : one * huge = huge).
Check (eq_refl : zero * huge = zero).
Check (eq_refl : zero * (-huge) = neg_zero).

Check (eq_refl : zero * infinity = nan).
Check (eq_refl : neg_infinity * zero = nan).
