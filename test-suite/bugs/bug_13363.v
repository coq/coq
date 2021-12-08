Axiom X : Type.
Axiom P : (X -> unit) -> Prop.

Axiom F: unit -> unit.
Axiom G : unit -> unit.

Lemma Hyp ss':
    P (fun y : X => ss') ->
    P (fun y : X => G (F ss')).
Admitted.

Lemma bug : exists x, P x.
Proof.
intros.
eexists (fun y : X => G _).
eapply Hyp. cbn beta.
Abort.
