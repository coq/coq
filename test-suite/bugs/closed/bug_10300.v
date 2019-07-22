Set Implicit Arguments.

Definition hprop := nat -> Prop.

Definition himpl := fun H1 H2 : hprop => forall (h : nat), H1 h -> H2 h.

Parameter himpl_refl : forall H : hprop, himpl H H.

Parameter hstar : hprop -> hprop -> hprop.

Parameter hpure : hprop.

Lemma test : (forall (H:hprop), himpl (hstar H H) hpure -> True) -> True.
Proof. intros M. eapply M. apply himpl_refl. Abort.
