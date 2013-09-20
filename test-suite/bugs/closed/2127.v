(* Check that "apply eq_refl" is not exported as an interactive
   tactic but as a statically globalized one *)

(* (this is a simplification of the original bug report) *)

Module A.
Hint Rewrite eq_sym using apply eq_refl : foo.
End A.
