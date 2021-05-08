Axiom P : unit -> Prop.
Axiom l : forall (x : unit), P x -> True.
Axiom m : forall (x : unit), P x.

Goal True.
pose proof m.
eapply l.
firstorder.
Abort. (* Works, no error *)

Goal True.
eapply l.
pose proof m.
firstorder.
Abort.
(* Used to give:
Anomaly "in econstr: grounding a non evar-free term" *)
