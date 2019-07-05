Set Printing Dependent Evars Line.
Lemma strange_imp_trans :
  forall P Q R : Prop, (Q -> R) -> (P -> Q) -> (P -> Q) -> P -> R.
Proof.
  auto.
Qed.

Lemma modpon : forall P Q : Prop, (P -> Q) /\ P -> Q.
Proof.
  tauto.
Qed.

Section eex.
  Variables P1 P2 P3 P4 : Prop.
  Hypothesis p12 : P1 -> P2.
  Hypothesis p123 : (P1 -> P2) -> P3.
  Hypothesis p34 : P3 -> P4.

  Lemma p14 : P4.
  Proof.
    eapply strange_imp_trans.
          apply modpon.
  Abort.
End eex.
