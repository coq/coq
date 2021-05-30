Section FooSect.

  Fail Unset Guard Checking.

  (* Let bad := fix bad (n:nat) : False := bad n. *)

  (* Fixpoint loop (n : nat) : nat := loop n. *)

  (* Set Guard Checking. *)
  (* Definition really_bad := bad 0. *)

End FooSect.

(* Print Assumptions loop. *)
(* Print Assumptions really_bad. TODO *)
