Set Printing Universes.
Local Close Scope nat_scope.
Check (fun ab : Prop * Prop => (fst ab : Prop) * (snd ab : Prop)).
(* fun ab : Prop * Prop =>
(fst (* Top.5817 Top.5818 *) ab:Prop) * (snd (* Top.5817 Top.5818 *) ab:Prop)
     : Prop * Prop -> Prop *)
Check (fun ab : Prop * Prop => (fst ab : Prop) * (snd ab : Prop) : Prop).
(* Toplevel input, characters 51-84:
Error: In environment
ab : Prop * Prop
The term
 "(fst (* Top.5833 Top.5834 *) ab:Prop) *
  (snd (* Top.5833 Top.5834 *) ab:Prop)" has type
 "Type (* max(Top.5829, Top.5830) *)" while it is expected to have type
 "Prop". *)
