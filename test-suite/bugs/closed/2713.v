Set Implicit Arguments.

Definition pred_le A (P Q : A->Prop) := 
  forall x, P x -> Q x.

Lemma pred_le_refl : forall A (P:A->Prop),
  pred_le P P.
Proof. unfold pred_le. auto. Qed.

Hint Resolve pred_le_refl.

Lemma test : 
  forall (P1 P2:nat->Prop), 
  (forall Q, pred_le (fun a => P1 a /\ P2 a) Q -> True) ->
   True.
Proof. intros. eapply H. eauto. (* used to work *)
       apply pred_le_refl. Qed.
