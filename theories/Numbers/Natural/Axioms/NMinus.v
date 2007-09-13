Require Export NPlusOrder.

Module Type NMinusSignature.
Declare Module Export NPredModule : NPredSignature.
Open Local Scope NatScope.

Parameter Inline minus : N -> N -> N.

Notation "x - y" := (minus x y) : NatScope.

Add Morphism minus with signature E ==> E ==> E as minus_wd.

Axiom minus_0_r : forall n, n - 0 == n.
Axiom minus_succ_r : forall n m, n - (S m) == P (n - m).

End NMinusSignature.

Module NMinusProperties (Import NMinusModule : NMinusSignature)
                        (Import NPlusMod : NPlusSig with
                          Module NBaseMod := NMinusModule.NPredModule.NBaseMod)
                        (Import NOrderModule : NOrderSig with
                          Module NBaseMod := NMinusModule.NPredModule.NBaseMod).
Module Export NPlusOrderPropertiesModule :=
  NPlusOrderProperties NPlusMod NOrderModule.
Open Local Scope NatScope.

Theorem minus_1_r : forall n, n - 1 == P n.
Proof.
intro n; rewrite minus_succ_r; now rewrite minus_0_r.
Qed.

Theorem minus_0_l : forall n, 0 - n == 0.
Proof.
induct n.
apply minus_0_r.
intros n IH; rewrite minus_succ_r; rewrite IH. now apply pred_0.
Qed.

Theorem minus_comm_succ : forall n m, S n - S m == n - m.
Proof.
intro n; induct m.
rewrite minus_succ_r. do 2 rewrite minus_0_r. now rewrite pred_succ.
intros m IH. rewrite minus_succ_r. rewrite IH. now rewrite minus_succ_r.
Qed.

Theorem minus_succ_l : forall n m, n <= m -> S m - n == S (m - n).
Proof.
intros n m H; pattern n, m; apply le_ind_rel.
unfold rel_wd. intros x x' H1 y y' H2; rewrite H1; now rewrite H2.
intros; now do 2 rewrite minus_0_r.
clear n m H. intros n m H1 H2.
now do 2 rewrite minus_comm_succ. assumption.
Qed.

Theorem minus_le : forall n m, n <= m -> n - m == 0.
Proof.
intros n m H; pattern n, m; apply le_ind_rel.
unfold rel_wd; intros x x' H1 y y' H2; rewrite H1; now rewrite H2.
apply minus_0_l.
clear n m H; intros n m H1 H2. now rewrite minus_comm_succ.
assumption.
Qed.

Theorem minus_diag : forall n, n - n == 0.
Proof.
intro n; apply minus_le; apply le_refl.
Qed.

Theorem minus_plus : forall n m, n <= m -> (m - n) + n == m.
Proof.
intros n m H; pattern n, m; apply le_ind_rel.
unfold rel_wd; intros x x' H1 y y' H2; rewrite H1; now rewrite H2.
intro; rewrite minus_0_r; now rewrite plus_0_r.
clear n m H. intros n m _ H2. rewrite minus_comm_succ. rewrite plus_succ_r.
now rewrite H2.
assumption.
Qed.

End NMinusProperties.




(*
 Local Variables:
 tags-file-name: "~/coq/trunk/theories/Numbers/TAGS"
 End:
*)
