Set Mangle Names.
Import EqNotations.
Lemma eq_sigT_sig_eq X P (x1 x2:X) H1 H2 :
  forall (E1 : x1=x2), rew E1 in H1 = H2 -> existT P x1 H1 = existT P x2 H2.
Proof.
  intros ->.
  intros <-.
  reflexivity.
Defined.
