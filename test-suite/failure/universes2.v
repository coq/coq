(* Example submitted by Randy Pollack *)

Parameter K: (T:Type)T->T.
Check (K ((T:Type)T->T) K).
(* Universe Inconsistency *)
