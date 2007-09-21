Require Export NZPlus.
Require Export NZOrder.

Module NZPlusOrderPropFunct
  (Import NZPlusMod : NZPlusSig)
  (Import NZOrderMod : NZOrderSig with Module NZBaseMod := NZPlusMod.NZBaseMod).

Module Export NZPlusPropMod := NZPlusPropFunct NZPlusMod.
Module Export NZOrderPropMod := NZOrderPropFunct NZOrderMod.
Open Local Scope NatIntScope.

Theorem NZplus_lt_mono_l : forall n m p, n < m <-> p + n < p + m.
Proof.
intros n m p; NZinduct p.
now do 2 rewrite NZplus_0_l.
intro p. do 2 rewrite NZplus_succ_l. now rewrite <- NZsucc_lt_mono.
Qed.

Theorem NZplus_lt_mono_r : forall n m p, n < m <-> n + p < m + p.
Proof.
intros n m p.
rewrite (NZplus_comm n p); rewrite (NZplus_comm m p); apply NZplus_lt_mono_l.
Qed.

Theorem NZplus_lt_mono : forall n m p q, n < m -> p < q -> n + p < m + q.
Proof.
intros n m p q H1 H2.
apply NZlt_trans with (m + p);
[now apply -> NZplus_lt_mono_r | now apply -> NZplus_lt_mono_l].
Qed.

Theorem NZplus_le_mono_l : forall n m p, n <= m <-> p + n <= p + m.
Proof.
intros n m p; NZinduct p.
now do 2 rewrite NZplus_0_l.
intro p. do 2 rewrite NZplus_succ_l. now rewrite <- NZsucc_le_mono.
Qed.

Theorem NZplus_le_mono_r : forall n m p, n <= m <-> n + p <= m + p.
Proof.
intros n m p.
rewrite (NZplus_comm n p); rewrite (NZplus_comm m p); apply NZplus_le_mono_l.
Qed.

Theorem NZplus_le_mono : forall n m p q, n <= m -> p <= q -> n + p <= m + q.
Proof.
intros n m p q H1 H2.
apply NZle_trans with (m + p);
[now apply -> NZplus_le_mono_r | now apply -> NZplus_le_mono_l].
Qed.

Theorem NZplus_lt_le_mono : forall n m p q, n < m -> p <= q -> n + p < m + q.
Proof.
intros n m p q H1 H2.
apply NZlt_le_trans with (m + p);
[now apply -> NZplus_lt_mono_r | now apply -> NZplus_le_mono_l].
Qed.

Theorem NZplus_le_lt_mono : forall n m p q, n <= m -> p < q -> n + p < m + q.
Proof.
intros n m p q H1 H2.
apply NZle_lt_trans with (m + p);
[now apply -> NZplus_le_mono_r | now apply -> NZplus_lt_mono_l].
Qed.

End NZPlusOrderPropFunct.


(*
 Local Variables:
 tags-file-name: "~/coq/trunk/theories/Numbers/TAGS"
 End:
*)
