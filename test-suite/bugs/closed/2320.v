(* Managing metavariables in the return clause of a match *)

(* This was working in 8.1 but is failing in 8.2 and 8.3. It works in
   trunk thanks to the new proof engine. It could probably made to work in
   8.2 and 8.3 if a return predicate of the form "dummy 0" instead of
   (or in addition to) a sophisticated predicate of the form 
   "as x in dummy y return match y with 0 => ?P | _ => ID end" *)

Inductive dummy : nat -> Prop := constr : dummy 0.

Lemma failure : forall (x : dummy 0), x = constr.
Proof.
intros x.
refine (match x with constr => _ end).
