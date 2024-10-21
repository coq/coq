Require Import PrimInt63 PrimFloat.

Open Scope float_scope.

Definition huge := 0x1p+1023%float.  (* Z.ldexp one 1023%Z. *)
Definition tiny := 0x0.8p-1022%float.  (* Z.ldexp one (-1023)%Z. *)

Check (eq_refl : huge / tiny = infinity).

Check (eq_refl : huge / huge = one).

Check (eq_refl : one / nan = nan).

Check (eq_refl : infinity / infinity = nan).

Check (eq_refl : infinity / neg_infinity = nan).

Check (eq_refl : zero / zero = nan).
Check (eq_refl : neg_zero / zero = nan).

Check (eq_refl : huge / neg_infinity = neg_zero).

Check (eq_refl : one / tiny = huge).
Check (eq_refl : one / huge = tiny).
Check (eq_refl : zero / huge = zero).
Check (eq_refl : zero / (-huge) = neg_zero).

Check (eq_refl : tiny / one = tiny).
Check (eq_refl : huge / one = huge).
Check (eq_refl : infinity / one = infinity).

Check (eq_refl : zero / infinity = zero).
Check (eq_refl : infinity / zero = infinity).
