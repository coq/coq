Require Import ZArith.
Require Import ZAux.

Open Scope Z_scope.

Fixpoint Ppow a z {struct z}:=
  match z with
    xH => a
  | xO z1 => let v := Ppow a z1 in (Pmult v v)
  | xI z1 => let v := Ppow a z1 in (Pmult a (Pmult v v))
  end.

Theorem Ppow_correct: forall a z,
  Zpos (Ppow a z) = (Zpos a) ^ (Zpos z).
intros a z; elim z; simpl Ppow; auto; 
  try (intros z1 Hrec; repeat rewrite Zpos_mult_morphism; rewrite Hrec).
  rewrite Zpos_xI; rewrite Zpower_exp; auto with zarith.
    rewrite Zpower_exp_1; rewrite (Zmult_comm 2);
    try rewrite Zpower_mult; auto with zarith.
    change 2 with (1 + 1); rewrite Zpower_exp; auto with zarith.
    rewrite Zpower_exp_1; rewrite Zmult_comm; auto.
    apply Zle_ge; auto with zarith.
  rewrite Zpos_xO; rewrite (Zmult_comm 2); 
    rewrite Zpower_mult; auto with zarith.
    change 2 with (1 + 1); rewrite Zpower_exp; auto with zarith.
    rewrite Zpower_exp_1; auto.
 rewrite Zpower_exp_1; auto.
Qed.

Theorem Ppow_plus: forall a z1 z2,
 Ppow a (z1 + z2) = ((Ppow a z1) * (Ppow a z2))%positive.
intros a z1 z2.
  assert (tmp: forall x y, Zpos x = Zpos y -> x = y).
    intros x y H; injection H; auto.
  apply tmp.
  rewrite Zpos_mult_morphism; repeat rewrite Ppow_correct.
  rewrite Zpos_plus_distr; rewrite Zpower_exp; auto; red; simpl;
    intros; discriminate.
Qed.
