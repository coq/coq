Require Import ZArith.
Require Import ConstructiveEpsilon.

Definition Z_inj_nat (z : Z) : nat :=
  match z with
  | Z0 => 0
  | Zpos p => Pos.to_nat (p~0)
  | Zneg p => Pos.to_nat (Pos.pred_double p)
  end.

Definition Z_inj_nat_rev (n : nat) : Z :=
  match n with
  | O => 0
  | S n' => match Pos.of_nat n with
            | xH =>   Zneg xH
            | xO p => Zpos p
            | xI p => Zneg (Pos.succ p)
            end
  end.

Lemma Pos_pred_double_inj: forall (p q : positive),
    Pos.pred_double p = Pos.pred_double q -> p = q.
Proof.
  intros p q H.
  apply (f_equal Pos.succ) in H.
  do 2 rewrite Pos.succ_pred_double in H.
  inversion H; reflexivity.
Qed.

Lemma Z_inj_nat_id: forall (z : Z),
  Z_inj_nat_rev (Z_inj_nat z) = z.
Proof.
  intros z.
  unfold Z_inj_nat, Z_inj_nat_rev.
  destruct z eqn:Hdz.
  - reflexivity.
  - rewrite Pos2Nat.id.
    destruct (Pos.to_nat p~0) eqn:Hd.
    + pose proof Pos2Nat.is_pos p~0 as H.
      rewrite <- Nat.neq_0_lt_0 in H.
      exfalso; apply H, Hd.
    + reflexivity.
  - rewrite Pos2Nat.id.
    destruct (Pos.to_nat (Pos.pred_double p)) eqn: Hd.
    + pose proof Pos2Nat.is_pos (Pos.pred_double p) as H.
      rewrite <- Nat.neq_0_lt_0 in H.
      exfalso; apply H, Hd.
    + destruct (Pos.pred_double p) eqn:Hd2.
      * rewrite <- Pos.pred_double_succ in Hd2.
        apply Pos_pred_double_inj in Hd2.
        rewrite Hd2; reflexivity.
      * apply (f_equal Pos.succ) in Hd2.
        rewrite Pos.succ_pred_double in Hd2.
        rewrite <- Pos.xI_succ_xO in Hd2.
        inversion Hd2.
      * change xH with (Pos.pred_double xH) in Hd2.
        apply Pos_pred_double_inj in Hd2.
        rewrite Hd2; reflexivity.
Qed.

Lemma Z_inj_nat_inj: forall (x y : Z),
    Z_inj_nat x = Z_inj_nat y -> x = y.
Proof.
  intros x y H.
  apply (f_equal Z_inj_nat_rev) in H.
  do 2 rewrite Z_inj_nat_id in H.
  assumption.
Qed.

Lemma constructive_indefinite_ground_description_Z:
  forall P : Z -> Prop,
  (forall z : Z, {P z} + {~ P z}) ->
  (exists z : Z, P z) -> {z : Z | P z}.
Proof.
  apply (constructive_indefinite_ground_description Z Z_inj_nat Z_inj_nat_rev Z_inj_nat_id).
Qed.
