Require Import BinInt Zdiv Zdiv_facts Znumtheory PreOmega Lia.
Local Open Scope Z_scope.

Module Z.

Definition omodulo d a b := Z.modulo (a - d) b + d.

Lemma omodulo_0 a b : Z.omodulo 0 a b = Z.modulo a b.
Proof. cbv [Z.omodulo]. rewrite Z.sub_0_r, Z.add_0_r; trivial. Qed.

Lemma div_omod d a b : b <> 0 -> a = b * ((a-d)/b) + omodulo d a b.
Proof. cbv [omodulo]; pose proof Z.div_mod (a-d) b; lia. Qed.

Lemma omod_pos_bound d a b : 0 < b -> d <= Z.omodulo d a b < d+b.
Proof. cbv [Z.omodulo]. Z.to_euclidean_division_equations; lia. Qed.

Lemma omod_neg_bound d a b : b < 0 -> d+b < Z.omodulo d a b <= d.
Proof. cbv [Z.omodulo]. Z.to_euclidean_division_equations; lia. Qed.

Definition omod_bound_or d a b (H : b <> 0) : _ \/ _ :=
  match Z_dec b 0 with
  | inleft (left neg) => or_introl (omod_neg_bound d a b neg)
  | inleft (right pos) => or_intror (omod_pos_bound d a b ltac:(lia))
  | inright zero => ltac:(lia)
  end.

Lemma omod_small_iff d a b :
  (d <= a < d+b \/ b = 0 \/ d+b < a <= d) <-> Z.omodulo d a b = a.
Proof.
  cbv [Z.omodulo]; case (Z.eq_dec b 0) as [->|];
  rewrite ?Zmod_0_r; try pose proof Z.mod_small_iff (a-d) b; lia.
Qed.

Lemma omod_small d a b : d <= a < d+b -> Z.omodulo d a b = a.
Proof. intros; apply omod_small_iff; auto 2. Qed.

Lemma omod_small_neg d a b : d+b < a <= d -> Z.omodulo d a b = a.
Proof. intros; apply omod_small_iff; auto 3. Qed.

Lemma omod_0_r d a : Z.omodulo d a 0 = a.
Proof. intros; apply omod_small_iff; auto 3. Qed.

Local Ltac t := cbv [Z.omodulo]; repeat rewrite
  ?Zplus_mod_idemp_l, ?Zplus_mod_idemp_r, ?Zminus_mod_idemp_l, ?Zminus_mod_idemp_r, ?Z.add_simpl_r, ?Zmod_mod;
  try solve [trivial | lia | f_equal; lia].

Lemma omod_omod d a b : Z.omodulo d (Z.omodulo d a b) b = Z.omodulo d a b. Proof. t. Qed.

Lemma omod_mod d a b : Z.omodulo d (Z.modulo a b) b = Z.omodulo d a b. Proof. t. Qed.

Lemma mod_omod d a b : Z.modulo (Z.omodulo d a b) b = Z.modulo a b. Proof. t. Qed.

Lemma omod_inj_mod d x y m : x mod m = y mod m -> Z.omodulo d x m = Z.omodulo d y m.
Proof. rewrite <-(omod_mod _ x), <-(omod_mod _ y); congruence. Qed.

Lemma mod_inj_omod d x y m : Z.omodulo d x m = Z.omodulo d y m -> x mod m = y mod m.
Proof. rewrite <-(mod_omod d x), <-(mod_omod d y); congruence. Qed.

Lemma omod_idemp_add d x y m :
  Z.omodulo d (Z.omodulo d x m + Z.omodulo d y m) m = Z.omodulo d (x + y) m.
Proof. apply omod_inj_mod; rewrite Zplus_mod, !mod_omod, <-Zplus_mod; trivial. Qed.

Lemma omod_idemp_sub d x y m :
  Z.omodulo d (Z.omodulo d x m - Z.omodulo d y m) m = Z.omodulo d (x - y) m.
Proof. apply omod_inj_mod; rewrite Zminus_mod, !mod_omod, <-Zminus_mod; trivial. Qed.

Lemma omod_idemp_mul d x y m :
  Z.omodulo d (Z.omodulo d x m * Z.omodulo d y m) m = Z.omodulo d (x * y) m.
Proof. apply omod_inj_mod; rewrite Zmult_mod, !mod_omod, <-Zmult_mod; trivial. Qed.

Lemma omod_diveq_iff c a b d :
  (b = 0 \/ c*b <= a - d < c*b + b \/ c*b + b < a - d <= c*b) <->
  Z.omodulo d a b = a-b*c.
Proof. cbv [omodulo]. rewrite Z.mod_diveq_iff; lia. Qed.

Definition omod_diveq c a b d := proj1 (omod_diveq_iff c a b d).

Definition smodulo a b := Z.omodulo (- Z.quot b 2) a b.

Lemma div_smod a b : b <> 0 -> a = b * ((a+Z.quot b 2)/b) + Z.smodulo a b.
Proof.
  cbv [Z.smodulo]; pose proof Z.div_omod (- Z.quot b 2) a b.
  rewrite <-(Z.sub_opp_r a (b ÷ 2)); lia.
Qed.

Lemma smod_eq a b : b <> 0 -> smodulo a b = a - b * ((a + Z.quot b 2) / b).
Proof. intros H; pose proof div_smod a _ H; lia. Qed.

Lemma smod_pos_bound a b: 0 < b -> -b <= 2*Z.smodulo a b < b.
Proof. cbv [Z.omodulo Z.smodulo]; Z.to_euclidean_division_equations; lia. Qed.

Lemma smod_neg_bound a b: b < 0 -> b < 2*Z.smodulo a b <= -b.
Proof. cbv [Z.smodulo Z.omodulo]. Z.to_euclidean_division_equations; lia. Qed.

Definition smod_bound_or a b (H : b <> 0) : _ \/ _ :=
  match Z_dec b 0 with
  | inleft (left neg) => or_introl (smod_neg_bound a b neg)
  | inleft (right pos) => or_intror (smod_pos_bound a b ltac:(lia))
  | inright zero => ltac:(lia)
  end.

Lemma smod_smod a b : Z.smodulo (Z.smodulo a b) b = Z.smodulo a b.
Proof. apply omod_omod. Qed.

Lemma smod_mod a b : Z.smodulo (Z.modulo a b) b = Z.smodulo a b.
Proof. apply omod_mod. Qed.
Lemma mod_smod a b : Z.modulo (Z.smodulo a b) b = Z.modulo a b.
Proof. apply mod_omod. Qed.

Lemma smod_inj_mod x y m : x mod m = y mod m -> Z.smodulo x m = Z.smodulo y m.
Proof. apply omod_inj_mod. Qed.

Lemma mod_inj_smod x y m : Z.smodulo x m = Z.smodulo y m -> x mod m = y mod m.
Proof. apply mod_inj_omod. Qed.

Lemma smod_idemp_add x y m :
  Z.smodulo (Z.smodulo x m + Z.smodulo y m) m = Z.smodulo (x + y) m.
Proof. apply omod_idemp_add. Qed.

Lemma smod_idemp_sub x y m :
  Z.smodulo (Z.smodulo x m - Z.smodulo y m) m = Z.smodulo (x - y) m.
Proof. apply omod_idemp_sub. Qed.

Lemma smod_idemp_mul x y m :
  Z.smodulo (Z.smodulo x m * Z.smodulo y m) m = Z.smodulo (x * y) m.
Proof. apply omod_idemp_mul. Qed.

Lemma smod_small_iff a b (d := - Z.quot b 2) :
  (- b <= 2*a - Z.rem b 2 < b \/ b = 0 \/ b < 2*a - Z.rem b 2 <= - b)
  <-> smodulo a b = a.
Proof.
  pose proof Z.quot_rem b 2 ltac:(lia).
  cbv [smodulo]; pose proof omod_small_iff (- Z.quot b 2) a b; lia.
Qed.

Lemma smod_even_small_iff a b (H : Z.rem b 2 = 0) :
  (-b <= 2*a < b \/ b = 0 \/ b < 2*a <= -b) <-> Z.smodulo a b = a.
Proof. rewrite <-smod_small_iff, H; lia. Qed.

Lemma smod_small a b : -b <= 2*a - Z.rem b 2 < b -> Z.smodulo a b = a.
Proof. intros; apply smod_small_iff; auto 2. Qed.

Lemma smod_even_small a b : Z.rem b 2 = 0 -> -b <= 2*a < b -> Z.smodulo a b = a.
Proof. intros; apply smod_even_small_iff; auto 2. Qed.

Lemma smod_pow2_small a w (H : 0 < w) : - 2 ^ w <= 2 * a < 2 ^ w -> Z.smodulo a (2^w) = a.
Proof.
  intros; apply Z.smod_even_small; trivial.
  rewrite <-(Z.succ_pred w), Z.pow_succ_r; Z.to_euclidean_division_equations; lia.
Qed.

Lemma smod_small_neg a b : b < 2*a - Z.rem b 2 <= - b -> Z.smodulo a b = a.
Proof. intros; apply smod_small_iff; auto 3. Qed.

Lemma smod_even_small_neg a b : Z.rem b 2 = 0 -> b < 2*a <= - b -> Z.smodulo a b = a.
Proof. intros; apply smod_even_small_iff; auto 3. Qed.

Lemma smod_0_r a : Z.smodulo a 0 = a.
Proof. apply Z.omod_0_r. Qed.

Lemma smod_0_l m : Z.smodulo 0 m = 0.
Proof. apply smod_small_iff; Z.to_euclidean_division_equations; lia. Qed.

Lemma smod_diveq_iff c a b :
  (b = 0 \/ c*b <= a + Z.quot b 2 < c*b + b \/ c*b + b < a + Z.quot b 2 <= c * b) <->
  Z.smodulo a b = a-b*c.
Proof. cbv [smodulo]. rewrite <-omod_diveq_iff; lia. Qed.

Definition smod_diveq c a b := proj1 (smod_diveq_iff c a b).

Lemma smod_diveq_even_iff c a b :
  Z.rem b 2 = 0 ->
  (b = 0 \/ 2*c*b <= 2*a+b < 2*c*b + 2*b \/ 2*c*b+2*b < 2*a+b <= 2*c*b) <->
  Z.smodulo a b = a-b*c.
Proof. cbv [smodulo]. rewrite <-omod_diveq_iff. Z.to_euclidean_division_equations; nia. Qed.

Definition smod_diveq_even c a b H := proj1 (smod_diveq_even_iff c a b H).

Lemma smod_smod_divide a b c : (c | b) -> Z.smodulo (Z.smodulo a b) c = Z.smodulo a c.
Proof.
  intros [d ->]; eapply smod_inj_mod.
  destruct (Z.eqb_spec (d*c) 0) as [->|]. { rewrite Z.smod_0_r; trivial. }
  rewrite smod_eq; trivial.
  rewrite <-Z.add_opp_r, <-Z.mul_assoc, Z.mul_comm.
  rewrite <-Z.mul_assoc, Z.mul_comm, <-Z.mul_opp_l, Z.mod_add; nia.
Qed.

Lemma smod_complement a b h (H : b = 2*h) :
  Z.smodulo a b / h = - (Z.modulo a b / h).
Proof.
  destruct (Z.eqb_spec h 0); [subst; rewrite ?Zdiv_0_r; trivial|]; rewrite <-smod_mod.
  specialize (Z.mod_bound_or a b); generalize (a mod b); clear a; intros a **.
  pose proof Z.div_smod a b ltac:(lia).
  progress replace (Z.quot b 2) with h in *
    by (clear -n H; Z.to_euclidean_division_equations; nia).
  assert ((a/h = 1 \/ a/h = 0 \/ a/h = -1) /\ ((a+h)/b = 1 \/ (a+h)/b = 0) /\
    (Z.smodulo a b / h = 1 \/ Z.smodulo a b / h = 0 \/ Z.smodulo a b / h = -1)
  ); Z.to_euclidean_division_equations; nia.
  (* ─xnia (tactic) -----------------------  36.0%  94.1%       1    0.518s *)
  (* ─exact (uconstr) ---------------------  57.3%  57.3%       2    0.219s *)
Qed.

Lemma smod_idemp_opp x m :
  Z.smodulo (- Z.smodulo x m) m = Z.smodulo (- x) m.
Proof.
  rewrite <-(Z.sub_0_l x), <-smod_idemp_sub, smod_0_l.
  rewrite (Z.sub_0_l (*workaround*) (smodulo x m)); trivial.
Qed.

Lemma smod_pow_l a b c : Z.smodulo ((Z.smodulo a c) ^ b) c = Z.smodulo (a ^ b) c.
Proof.
  destruct (Z.leb_spec 0 b); cycle 1.
  { rewrite !Z.pow_neg_r; trivial. }
  pattern b; eapply natlike_ind; trivial; clear dependent b; intros b H IH.
  rewrite !Z.pow_succ_r by trivial.
  symmetry; rewrite <-Z.smod_idemp_mul; symmetry.
  rewrite <-Z.smod_idemp_mul.
  symmetry; rewrite <-Z.smod_idemp_mul; symmetry.
  f_equal.
  f_equal.
  rewrite IH, Z.smod_smod; trivial.
Qed.

End Z.
