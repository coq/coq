(* Check that "apply refl_equal" is not exported as an interactive
   tactic but as a statically globalized one *)

(* (this is a simplification of the original bug report) *)

Module A.
Hint Rewrite sym_equal using apply refl_equal : foo.
End A.
