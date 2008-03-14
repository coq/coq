(* Check that "where" clause behaves as if given independently of the  *)
(* definition (variant of bug #113? submitted by Assia Mahboubi) *)

Fixpoint plus1 (n m:nat) {struct n} : nat :=
   match n with
   | O => m
   | S p => S (p+m)
   end
 where "n + m" := (plus1 n m) : nat_scope.
