Coercion nat_of_option (u : option nat) : nat :=
  match u with Some u => u | None => 0 end.

Number Notation nat Nat.of_num_int Nat.to_num_int : nat_scope.

Check 3.  (* should be "3 : nat" and not "Some 3 : option nat" *)

Check eq_refl : 3 = S (S (S O)).
