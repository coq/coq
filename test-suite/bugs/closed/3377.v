Set Primitive Projections.
Set Implicit Arguments.
Record prod A B := pair { fst : A; snd : B}.

Goal fst (@pair Type Type Type Type).
Set Printing All.
match goal with |- ?f ?x => set (foo := f x) end.
Abort.

Goal forall x : prod Set Set, x = @pair _ _ (fst x) (snd x).
Proof.
  intro x.
  lazymatch goal with
    | [ |- ?x = @pair _ _ (?f ?x) (?g ?x) ] => pose f
  end.
(* Toplevel input, characters 7-44:
Error: No matching clauses for match. *)
Abort.
