Definition arrow_apply (f : Prop -> Prop) := True -> f True. (* We need True-> to trigger a unification in an extended context *)

Definition something (x : Prop) := arrow_apply (fun _ => x).

Axiom trivial: forall l1: Prop, something l1 -> something l1.

Lemma t : exists f, arrow_apply f.
eexists.
unshelve apply trivial.
(* was giving "something ?l1@{t:=_UNBOUND_REL_1}" while the evar is not supposed to depend on t *)
(* so, we check that, indeed, t is not here *)
match goal with [ H : True |- _ ] => fail 1 | _ => idtac end.
Abort.
