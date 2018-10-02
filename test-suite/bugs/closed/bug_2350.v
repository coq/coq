(* Check that the fix tactic, when called from refine, reduces enough
   to see the products *)

Definition foo := forall n:nat, n=n.
Definition bar : foo.
refine (fix aux (n:nat) := _).
