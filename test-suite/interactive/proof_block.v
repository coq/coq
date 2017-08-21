Goal False /\ True.
Proof.
split.
  idtac.
  idtac.
  exact I.
idtac.
idtac.
exact I.
Qed.

Lemma baz :  (exists n, n = 3 /\ n = 3) /\ True.
Proof.
split. { eexists. split. par: trivial. }
trivial.
Qed.

Lemma baz1 :  (True /\ False) /\ True.
Proof.
split. { split. par: trivial. }
trivial.
Qed.

Lemma foo : (exists n, n = 3 /\ n = 3) /\ True.
Proof.
split.
  { idtac.
    unshelve eexists.
    { apply 3. }
    { split.
      { idtac. trivialx. }
      { reflexivity. } } }
  trivial.
Qed.

Lemma foo1 : False /\ True.
Proof.
split.
  { exact I. }
  { exact I. }
Qed.

Definition banana := true + 4. 

Check banana.

Lemma bar : (exists n, n = 3 /\ n = 3) /\ True.
Proof.
split.
  - idtac.
    unshelve eexists.
    + apply 3.
    + split.
      * idtacx. trivial. 
      * reflexivity.
  - trivial.
Qed.

Lemma baz2 :  ((1=0 /\ False) /\ True) /\ False.
Proof.
split. split. split.
 - solve [ auto ].
 - solve [ trivial ].
 - solve [ trivial ].
 - exact 6.
Qed.
