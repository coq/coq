(* Taking automatically into account internal dependencies of a |match] *)

Let a n := @exist nat _ _ (refl_equal (n + 1)).
Goal let (n, _) := a 3 in n = 4.
pattern 3 at 1.
Abort.

Goal match refl_equal 0 in _ = n return n = 0 with
     | refl_equal => refl_equal 0
     end = refl_equal 0.
pattern 0 at 1 2 3 4 5 6.
Abort.
