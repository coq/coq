Axiom P : nat -> Prop.

Definition myFact := forall x, P x.

Hint Extern 1 (P _) => progress (unfold myFact in *).

Lemma test : (True -> myFact) -> P 3.
Proof. 
  intros. debug eauto.
Qed.
