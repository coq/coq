(* Test for the Kernel Conversion Dep Heuristic flag *)

(* Deactivate Height Heuristic to avoid setting strategy levels for
   definitions, which would render Dep Heuristic useless. *)
Unset Kernel Conversion Height Heuristic.

(* Define a factorial function *)
Fixpoint fact (n : nat) := match n with O => 1 | S n => (S n) * fact n end.

(* Define constants that depend on each other:
   fact100' depends on fact100 which depends on fact *)
Definition fact100 := fact 100.
Definition fact100' := fact100.

(* Without the heuristic, conversion prefers unfolding right-to-left by default.
   - fact100 = fact100' is fast because fact100' (on the right) is unfolded first,
     revealing fact100, and both sides are then syntactically equal
   - fact100' = fact100 is slow because fact100 (on the right) is unfolded first
     and fully reduced to normal form before the left side is considered

   With the heuristic enabled, when the oracle doesn't prefer either constant,
   we prefer unfolding the constant that depends on the other one. Since
   fact100' depends on fact100, we prefer unfolding fact100' regardless of
   which side it appears on. *)

(* Test 1: This direction is always fast (unfolds fact100' first) *)
Timeout 1 Check eq_refl : fact100 = fact100'.

(* Test 2: Without heuristic this times out, with heuristic it's fast *)
(* First verify the timeout behavior without the heuristic *)
Unset Kernel Conversion Dep Heuristic.
Fail Timeout 1 Check eq_refl : fact100' = fact100.

(* Now enable the heuristic and verify it works *)
Set Kernel Conversion Dep Heuristic.
Timeout 1 Check eq_refl : fact100' = fact100.
