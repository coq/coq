Set Universe Polymorphism.

(* was error universe is unbound *)
Lemma foo@{} : (nat :> Type).
Proof. exact 0. Qed.

Check foo@{}.
