(* Example submitted by Randy Pollack *)

Parameter K : forall T : Type, T -> T.
Check (K (forall T : Type, T -> T) K).
