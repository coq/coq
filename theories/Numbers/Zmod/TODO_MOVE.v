Require Import Coq.Logic.HLevels. (* TODO: refactor to not Require funext *)
Require Import Coq.Bool.Bool.

Lemma Is_true_hprop b : IsHProp (Is_true b).
Proof. destruct b; auto using true_hprop, false_hprop. Qed.
Definition transparent_true (b : bool) : (True -> Is_true b) -> Is_true b :=
  match b with
  | true => fun _ => I
  | false => fun H => False_rect _ (H I)
  end.


Require Import ZArith Lia Znumtheory.
Module Import Znumtheory.

Lemma cong_iff_0 a b m : a mod m = b mod m <-> (a - b) mod m = 0.
Proof.
  case (Z.eq_dec m 0) as [->|Hm]; [rewrite ?Zmod_0_r; lia|].
  split; intros H. { rewrite Zminus_mod, H, Z.sub_diag, Z.mod_0_l; trivial. }
  apply Zmod_divides in H; trivial; case H as [c H].
  replace b with (a + (-c) * m) by lia; rewrite Z.mod_add; trivial.
Qed.

Lemma cong_iff_ex a b m (Hm : m <> 0) : a mod m = b mod m <-> exists n, a - b = n * m.
Proof. rewrite cong_iff_0, Z.mod_divide by trivial; reflexivity. Qed.

Lemma cong_mul_cancel_r_coprime a b m (Hm : m <> 0) (Hb : Z.gcd b m = 1)
  (H : (a * b) mod m = 0) : a mod m = 0.
Proof.
  apply Zmod_divide in H; trivial; [].
  rewrite Z.mul_comm in H; apply Gauss, Zdivide_mod in H; trivial.
  apply rel_prime_sym, Zgcd_1_rel_prime; trivial.
Qed.


Definition invmod a m := fst (fst (extgcd a m)).

Lemma invmod_0_l m : invmod 0 m = 0. Proof. reflexivity. Qed.

Lemma invmod_ok a m (Hm : m <> 0) : invmod a m * a mod m = Z.gcd a m mod m.
Proof.
  cbv [invmod]; destruct extgcd as [[u v]g] eqn:H.
  eapply extgcd_correct in H; case H as [[]]; subst; cbn [fst snd].
  erewrite <-Z.mod_add, H; trivial.
Qed.

Lemma invmod_coprime' a m (Hm : m <> 0) (H : Z.gcd a m = 1) : invmod a m * a mod m = 1 mod m.
Proof. rewrite invmod_ok, H; trivial. Qed.

Lemma invmod_coprime a m (Hm : 2 <= m) (H : Z.gcd a m = 1) : invmod a m * a mod m = 1.
Proof. rewrite invmod_coprime', Z.mod_1_l; lia. Qed.

Lemma invmod_prime a m (Hm : prime m) (H : a mod m <> 0) : invmod a m * a mod m = 1.
Proof.
  pose proof prime_ge_2 _ Hm as Hm'. rewrite Z.mod_divide in H by lia.
  apply invmod_coprime, Zgcd_1_rel_prime, rel_prime_sym, prime_rel_prime; auto.
Qed.

Lemma invmod_mod_l a m (Hm : m <> 0) (Ha : Z.gcd a m = 1) : invmod (a mod m) m mod m = invmod a m mod m.
Proof.
  cbv [invmod].
  destruct extgcd as ([]&?) eqn:HA; apply extgcd_correct in HA.
  destruct extgcd as ([]&?) eqn:HB in |- *; apply extgcd_correct in HB.
  intuition idtac; cbn [fst snd]. eassert (_ = Z.gcd (a mod m) m) as E by eauto.
  rewrite ?Z.gcd_mod, ?(Z.gcd_comm _ a) in *; trivial; subst.
  rewrite <-H2 in E; clear H2.
  apply (f_equal (fun x => x mod m)) in E. rewrite !Z.mod_add in E by trivial.
  rewrite Z.mul_mod_idemp_r in E by lia.
  apply cong_iff_0 in E; apply cong_iff_0.
  rewrite <-Z.mul_sub_distr_r in E.
  eapply cong_mul_cancel_r_coprime in E; trivial.
Qed.

Lemma coprime_invmod a m (H : Z.gcd a m = 1) : Z.gcd (Znumtheory.invmod a m) m = 1.
Proof.
  cbv [Znumtheory.invmod fst].
  destruct extgcd as ([]&?) eqn:HA; apply extgcd_correct in HA; case HA as [Hb Hg'].
  rewrite H in *; subst.
  apply Z.bezout_1_gcd; cbv [Z.Bezout].
  rewrite <-Hg'.
  match goal with z0 : Z, z1 : Z |- _ => exists z0, z1; ring end.
Qed.


Theorem chinese_remainder a m1 b m2
  (Hm1 : m1 <> 0) (Hm2 : m2 <> 0) (H : Z.gcd m1 m2 = 1)
  (H1 : a mod m1 = b mod m1) (H2 : a mod m2 = b mod m2) :
  a mod (m1 * m2) = b mod (m1 * m2).
Proof.
  apply cong_iff_0; apply cong_iff_0 in H2.
  apply cong_iff_ex in H1; trivial; []; case H1 as [k H1]. rewrite H1 in *.
  apply cong_mul_cancel_r_coprime in H2; trivial.
  rewrite Z.mul_comm, Zmult_mod_distr_l. rewrite H2, Z.mul_0_r; trivial.
Qed.



Definition solvecong (m1 m2 : Z) :=
  let '(a, b, d) := extgcd m1 m2 in
  fun (r1 r2 : Z) => r1 - (r1 - r2)/d*a*m1.

Lemma solvecong_correct m1 m2 r1 r2 (H : (r1 - r2) mod (Z.gcd m1 m2) = 0)
  (x := solvecong m1 m2 r1 r2) : x mod m1 = r1 mod m1 /\ x mod m2 = r2 mod m2.
Proof.
  cbv [solvecong] in *; case (extgcd m1 m2) as [[a b] d] eqn:E.
  eapply extgcd_correct in E; case E as [E D]; rewrite <-D in *; clear D.
  replace x with (r2 + (r1 - r2)/d*b*m2) at 2 by (Z.div_mod_to_equations; lia); cbv [x].
  rewrite <-Zminus_mod_idemp_r, <-Zplus_mod_idemp_r, 2Z_mod_mult, Z.add_0_r, Z.sub_0_r; auto.
Qed.

Lemma solvecong_coprime m1 m2 r1 r2 (H : Z.gcd m1 m2 = 1)
  (x := solvecong m1 m2 r1 r2) : x mod m1 = r1 mod m1 /\ x mod m2 = r2 mod m2.
Proof. apply solvecong_correct. rewrite H, Z.mod_1_r; trivial. Qed.

Lemma chinese_remainder_solvecong a r1 m1 r2 m2
  (H : Z.gcd m1 m2 = 1) (Hm1 : m1 <> 0) (Hm2 : m2 <> 0)
  (H1 : a mod m1 = r1 mod m1) (H2 : a mod m2 = r2 mod m2) :
  a mod (m1 * m2) = solvecong m1 m2 r1 r2 mod (m1 * m2).
Proof.
  case (solvecong_coprime m1 m2 r1 r2 H) as [].
  eapply chinese_remainder; congruence.
Qed.

Lemma solvecong_comm m1 m2 r1 r2
  (H : Z.gcd m1 m2 = 1) (Hm1 : m1 <> 0) (Hm2 : m2 <> 0) :
  solvecong m1 m2 r1 r2 mod (m1 * m2) = solvecong m2 m1 r2 r1 mod (m1 * m2).
Proof.
  rewrite Z.mul_comm at 2.
  case (solvecong_coprime m1 m2 r1 r2 H) as [].
  erewrite <-(chinese_remainder_solvecong _ r1); try assumption.
  symmetry; erewrite <-(chinese_remainder_solvecong _ r2); try assumption.
  { rewrite Z.mul_comm; trivial. }
  { rewrite Z.gcd_comm; trivial. }
  instantiate (1:=solvecong m1 m2 r1 r2).
  all : assumption.
Qed.

End Znumtheory.

Module Pos.
  Import BinPosDef.
  Lemma land_mono : forall a b, (Pos.land a b <= N.pos a)%N.
  Proof. induction a, b; cbn [Pos.land]; try specialize (IHa b); lia. Qed.

  Lemma ldiff_mono : forall a b, (Pos.ldiff a b <= N.pos a)%N.
  Proof. induction a, b; cbn [Pos.ldiff]; try specialize (IHa b); try lia. Qed.

  Lemma div2_le a : (Pos.div2 a <= a)%positive.
  Proof. induction a; cbn [Pos.div2]; lia. Qed.

  Lemma shiftr_mono a b : (Pos.shiftr a b <= a)%positive.
  Proof.
    case b as [|b]; cbn [Pos.shiftr]; [lia|].
    revert a; induction b; cbn [Pos.iter];
      repeat (etransitivity; [eapply div2_le || eapply IHb|]); reflexivity.
  Qed.

  Lemma shiftl_mono a b : (a <= Pos.shiftl a b)%positive.
  Proof.
    case b as [|b]; cbn [Pos.shiftl]; [lia|].
    revert a; induction b; cbn [Pos.iter]; intros;
      try pose (IHb (Pos.iter xO a b)); try pose (IHb a); lia.
  Qed.

  Definition ones (p : positive) : positive :=
    N.iter (Pos.pred_N p) (fun n => n~1)%positive xH.

  Lemma iter_op_correct {A} op x p zero
    (op_zero_r : op x zero = x)
    (op_assoc : forall x y zero : A, op x (op y zero) = op (op x y) zero)
    : @Pos.iter_op A op p x = Pos.iter (op x) zero p.
  Proof.
    induction p using Pos.peano_ind; cbn;
      rewrite ?Pos.iter_op_succ, ?Pos.iter_succ, ?IHp; auto.
  Qed.

  Import Nnat.
  Lemma pow_add_r (a b c : positive) : (a^(b+c) = a^b * a^c)%positive.
  Proof.
    enough (N.pos (a ^ (b + c)) = N.pos (a ^ b * a ^ c)) by lia.
    rewrite <-(positive_nat_N (Pos.pow _ _)), Pos2Nat.inj_pow, Nat2N.inj_pow, 2positive_nat_N.
    replace (N.pos (b+c)) with (N.pos b + N.pos c)%N by lia; rewrite N.pow_add_r; lia.
  Qed.
End Pos.

Module N2Z.
  Lemma inj_lxor n m : Z.of_N (N.lxor n m) = Z.lxor (Z.of_N n) (Z.of_N m).
  Proof. destruct n, m; reflexivity. Qed.

  Lemma inj_land n m : Z.of_N (N.land n m) = Z.land (Z.of_N n) (Z.of_N m).
  Proof. destruct n, m; reflexivity. Qed.

  Lemma inj_lor n m : Z.of_N (N.lor n m) = Z.lor (Z.of_N n) (Z.of_N m).
  Proof. destruct n, m; reflexivity. Qed.

  Lemma inj_ldiff n m : Z.of_N (N.ldiff n m) = Z.ldiff (Z.of_N n) (Z.of_N m).
  Proof. destruct n, m; reflexivity. Qed.

  Lemma inj_shiftl: forall x y, Z.of_N (N.shiftl x y) = Z.shiftl (Z.of_N x) (Z.of_N y).
  Proof.
    intros x y.
    apply Z.bits_inj_iff'; intros k Hpos.
    rewrite Z2N.inj_testbit; [|assumption].
    rewrite Z.shiftl_spec; [|assumption].

    assert ((Z.to_N k) >= y \/ (Z.to_N k) < y)%N as g by (
        unfold N.ge, N.lt; induction (N.compare (Z.to_N k) y); [left|auto|left];
        intro H; inversion H).

    destruct g as [g|g];
    [ rewrite N.shiftl_spec_high; [|apply N2Z.inj_le; rewrite Z2N.id|apply N.ge_le]
    | rewrite N.shiftl_spec_low]; try assumption.

    - rewrite <- N2Z.inj_testbit; f_equal.
        rewrite N2Z.inj_sub, Z2N.id; [reflexivity|assumption|apply N.ge_le; assumption].

    - apply N2Z.inj_lt in g.
        rewrite Z2N.id in g; [symmetry|assumption].
        apply Z.testbit_neg_r; lia.
  Qed.

  Lemma inj_shiftr: forall x y, Z.of_N (N.shiftr x y) = Z.shiftr (Z.of_N x) (Z.of_N y).
  Proof.
    intros.
    apply Z.bits_inj_iff'; intros k Hpos.
    rewrite Z2N.inj_testbit; [|assumption].
    rewrite Z.shiftr_spec, N.shiftr_spec; [|apply N2Z.inj_le; rewrite Z2N.id|]; try assumption.
    rewrite <- N2Z.inj_testbit; f_equal.
    rewrite N2Z.inj_add; f_equal.
    apply Z2N.id; assumption.
  Qed.
End N2Z.

Module Z.
  Lemma ones_succ n (H : Z.le 0 n) : Z.ones (Z.succ n) = Z.succ_double (Z.ones n).
  Proof. rewrite 2Z.ones_equiv, Z.pow_succ_r; lia. Qed.

  Lemma pos_ones p : Z.pos (Pos.ones p) = Z.ones (Z.pos p).
  Proof.
    cbv [Pos.ones]. set (fun n => _) as step.
    replace (Z.pos p) with (Z.succ (Z.of_N (Pos.pred_N p))) by lia.
    induction (Pos.pred_N p) using N.peano_ind; trivial.
    rewrite Z.ones_succ, N2Z.inj_succ, <-IHn by lia; clear IHn.
    rewrite N.iter_succ. rewrite Pos2Z.pos_xI, Z.succ_double_spec; trivial.
  Qed.

  Import Znumtheory.
  Local Open Scope Z_scope.
  Lemma gcd_of_N a b : Z.gcd (Z.of_N a) (Z.of_N b) = Z.of_N (N.gcd a b).
  Proof. case a, b; trivial. Qed.

  Lemma mod_pow_l a b c : (a mod c)^b mod c = ((a ^ b) mod c).
  Proof.
    destruct (Z.ltb_spec b 0) as [|Hb]. { rewrite !Z.pow_neg_r; trivial. }
    destruct (Z.eqb_spec c 0) as [|Hc]. { subst. rewrite !Zmod_0_r; trivial. }
    generalize dependent b; eapply natlike_ind; trivial; intros x Hx IH.
    rewrite !Z.pow_succ_r, <-Z.mul_mod_idemp_r, IH, Z.mul_mod_idemp_l, Z.mul_mod_idemp_r; trivial.
  Qed.

  Lemma coprime_mul a b m : Z.gcd a m = 1 -> Z.gcd b m = 1 -> Z.gcd (a * b) m = 1.
  Proof.
    intros.
    apply Zgcd_1_rel_prime, rel_prime_sym, rel_prime_mult;
    apply rel_prime_sym, Zgcd_1_rel_prime; trivial.
  Qed.

  (** Modulo with an offset *)
  Definition omodulo d a b := Z.modulo (a - d) b + d.

  Lemma omodulo_0 a b : Z.omodulo 0 a b = Z.modulo a b.
  Proof. cbv [Z.omodulo]. rewrite Z.sub_0_r, Z.add_0_r; trivial. Qed.

  Lemma div_omod d a b : b <> 0 -> a = b * ((a-d)/b) + omodulo d a b.
  Proof. cbv [omodulo]; pose proof Z.div_mod (a-d) b; lia. Qed.

  Lemma omod_pos_bound d a b : 0 < b -> d <= Z.omodulo d a b < d+b.
  Proof. cbv [Z.omodulo]. Z.to_euclidean_division_equations; lia. Qed.

  Lemma omod_neg_bound d a b : b < 0 -> d+b < Z.omodulo d a b <= d.
  Proof. cbv [Z.omodulo]. Z.to_euclidean_division_equations; lia. Qed.

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
    ?Zplus_mod_idemp_l, ?Zplus_mod_idemp_r, ?Zminus_mod_idemp_l, ?Zminus_mod_idemp_r;
    try solve [trivial | lia | f_equal; lia].

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


  Definition smodulo a b := Z.omodulo (- Z.quot b 2) a b.

  Lemma div_smod a b : b <> 0 -> a = b * ((a+Z.quot b 2)/b) + Z.smodulo a b.
  Proof.
    cbv [Z.smodulo]; pose proof Z.div_omod (- Z.quot b 2) a b.
    rewrite <-(Z.sub_opp_r a (b ÷ 2)); lia.
  Qed.

  Lemma smod_pos_bound a b: 0 < b -> -b <= 2*Z.smodulo a b < b.
  Proof. cbv [Z.omodulo Z.smodulo]; Z.to_euclidean_division_equations; lia. Qed.

  Lemma smod_neg_bound a b: b < 0 -> b < 2*Z.smodulo a b <= -b.
  Proof. cbv [Z.smodulo Z.omodulo]. Z.to_euclidean_division_equations; lia. Qed.

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

  Lemma smod_small_neg a b : b < 2*a - Z.rem b 2 <= - b -> Z.smodulo a b = a.
  Proof. intros; apply smod_small_iff; auto 3. Qed.

  Lemma smod_even_small_neg a b : Z.rem b 2 = 0 -> b < 2*a <= - b -> Z.smodulo a b = a.
  Proof. intros; apply smod_even_small_iff; auto 3. Qed.

  Lemma smod_0_r a : Z.smodulo a 0 = a.
  Proof. apply Z.omod_0_r. Qed.

  Lemma smod_0_l m : Z.smodulo 0 m = 0.
  Proof. apply smod_small_iff; Z.to_euclidean_division_equations; lia. Qed.

  Lemma smod_idemp_opp x m :
    Z.smodulo (- Z.smodulo x m) m = Z.smodulo (- x) m.
  Proof.
    rewrite <-(Z.sub_0_l x), <-smod_idemp_sub, smod_0_l.
    rewrite (Z.sub_0_l (*workaround*) (smodulo x m)); trivial.
  Qed.
End Z.

Module N.
  Local Open Scope N_scope.

  Lemma land_mono a b : N.land a b <= a.
  Proof. case a, b; cbn [N.land]; trivial using Pos.land_mono; lia. Qed.

  Lemma ldiff_mono a b : N.ldiff a b <= a.
  Proof. case a, b; cbn [N.ldiff]; trivial using Pos.ldiff_mono; lia. Qed.

  Lemma div2_le a : N.div2 a <= a.
  Proof. case a; cbn; [lia|]. destruct p; lia. Qed.

  Lemma shiftr_mono a b : N.shiftr a b <= a.
  Proof.
    case b as [|b]; cbn [N.shiftr]; try lia.
    revert a; induction b; cbn [Pos.iter];
      repeat (etransitivity; [eapply div2_le || eapply IHb|]); reflexivity.
  Qed.

  Lemma shiftl_mono a b : a <= N.shiftl a b.
  Proof. case a as []; [lia|]. apply Pos.shiftl_mono. Qed.

  Lemma pos_pow a b : N.pos (a ^ b) = N.pow (N.pos a) (N.pos b).
  Proof. trivial. Qed.

  Lemma ones_succ n (H : N.le 0 n) : N.ones (N.succ n) = N.succ_double (N.ones n).
  Proof. rewrite 2N.ones_equiv, N.pow_succ_r; lia. Qed.
  
  Lemma pos_ones p : N.pos (Pos.ones p) = N.ones (N.pos p).
  Proof.
    cbv [Pos.ones]. set (fun n => _) as step.
    replace (N.pos p) with (N.succ (Pos.pred_N p)) by lia.
    induction (Pos.pred_N p) using N.peano_ind; trivial.
    rewrite N.ones_succ, <-IHn by lia; clear IHn.
    rewrite N.iter_succ. rewrite N.succ_double_spec; trivial.
  Qed.

  (* TODO: high part first or low part first? *)
  Definition undivmod b hi lo := b*hi + lo.

  Lemma div_undivmod b hi lo (H : lo < b) : N.div (undivmod b hi lo) b = hi.
  Proof. cbv [undivmod]. zify; Z.div_mod_to_equations; nia. Qed.

  Lemma mod_undivmod b hi lo (H : lo < b) : N.modulo (undivmod b hi lo) b = lo.
  Proof.
    cbv [undivmod]; rewrite N.add_comm, N.mul_comm,  N.Div0.mod_add, N.mod_small; trivial.
  Qed.

  Lemma undivmod_pow2 w hi lo (H : lo < 2^w) :
    N.undivmod (2^w) hi lo = N.lor (N.shiftl hi w) lo.
  Proof.
    cbv [N.undivmod]. enough (N.land (N.shiftl hi w) lo = 0).
    { rewrite <-N.lxor_lor, <-N.add_nocarry_lxor, N.shiftl_mul_pow2; lia. }
    rewrite <-(N.mod_small _ _ H).
    apply N.bits_inj_0; intros i; rewrite ?N.land_spec.
    case (N.ltb_spec i w) as [].
    all : rewrite ?N.shiftl_spec_low, ?N.shiftl_spec_high, ?N.mod_pow2_bits_high by lia.
    all : rewrite ?Bool.andb_false_l, ?Bool.andb_false_r; trivial.
  Qed.

  Definition iter_op {A} (op : A -> A -> A) (zero x : A) (n : N) :=
    match n with N0 => zero | Npos p => Pos.iter_op op p x end.

  Lemma iter_op_0_r {A} op zero x : @iter_op A op zero x 0 = zero. Proof. trivial. Qed.

  Lemma iter_op_1_r {A} op zero x : @iter_op A op zero x 1 = x. Proof. trivial. Qed.

  Lemma iter_op_succ_r {A} op zero x n
    (opp_zero_r : x = op x zero)
    (op_assoc  : forall x y z : A, op x (op y z) = op (op x y) z)
    : @iter_op A op zero x (N.succ n) = op x (iter_op op zero x n).
  Proof. case n; cbn; auto using Pos.iter_op_succ. Qed.

  Lemma iter_op_add_r {A} op zero x n
    (opp_zero_r : x = op x zero)
    (op_assoc  : forall x y z : A, op x (op y z) = op (op x y) z)
    : @iter_op A op zero x (N.succ n) = op x (iter_op op zero x n).
  Proof. induction n using N.peano_ind; cbn; rewrite ?iter_op_succ_r; auto. Qed.

  Lemma iter_op_correct {A} op zero x n
    (opp_zero_r : x = op x zero)
    (op_assoc  : forall x y z : A, op x (op y z) = op (op x y) z)
    : @iter_op A op zero x n = N.iter n (op x) zero.
  Proof. case n; cbn; auto using Pos.iter_op_correct. Qed.


  Lemma coprime_mul a b m : N.gcd a m = 1 -> N.gcd b m = 1 -> N.gcd (a * b) m = 1.
  Proof.
    intros H G.
    eapply N2Z.inj.
    rewrite <-Z.gcd_of_N, N2Z.inj_mul.
    apply Z.coprime_mul; rewrite Z.gcd_of_N, ?H, ?G; trivial.
  Qed.
  Lemma gcd_1_l n : N.gcd 1 n = 1.
  Proof. case n; trivial. Qed.

  Lemma mod_pow_l a b c : ((a mod c)^b mod c = ((a ^ b) mod c))%N.
  Proof.
    induction b using N.peano_ind; intros; trivial; pose proof N.Div0.mul_mod.
    rewrite ?N.pow_succ_r', <-N.Div0.mul_mod_idemp_r, IHb; auto.
  Qed.
End N.

Module List.
  Import Coq.Lists.List.

  Lemma tl_length {A} l : length (@tl A l) = pred (length l).
  Proof. case l; trivial. Qed.

  Lemma tl_map {A B} (f : A -> B) l : tl (map f l) = map f (tl l).
  Proof. case l; trivial. Qed.

  Lemma hd_error_skipn {A} n : forall xs, @hd_error A (skipn n xs) = nth_error xs n.
  Proof. induction n, xs; cbn [hd_error skipn]; auto. Qed.

  Lemma skipn_seq n : forall start len, skipn n (seq start len) = seq (start+n) (len-n).
  Proof. induction n, len; cbn [skipn seq]; rewrite ?Nat.add_0_r, ?IHn; auto. Qed.

  Lemma nth_error_seq n start len : nth_error (seq start len) n = 
    if Nat.ltb n len then Some (Nat.add start n) else None.
  Proof.
    rewrite <-hd_error_skipn, skipn_seq.
    destruct (Nat.sub len n) eqn:?, (Nat.ltb_spec n len); cbn [nth_error seq]; trivial; lia.
  Qed.

  Section WithF.
    Context {A B} (f : A -> option B).
    Fixpoint mapfilter (l : list A) :=
      match l with
      | nil => nil
      | cons a l =>
          match f a with
          | Some b => cons b (mapfilter l)
          | None => mapfilter l
          end
      end.

    Lemma in_mapfilter b l : In b (mapfilter l) <-> exists a, In a l /\ f a = Some b.
    Proof.
      revert b; induction l; cbn [mapfilter]; [firstorder idtac|].
      case f eqn:?; cbn [In];
      setoid_rewrite IHl; clear IHl; (* save 100ms on firstorder *)
      time firstorder (subst; eauto; congruence).
    Qed.

    Lemma NoDup_mapfilter l (Hf : forall x y, f x = f y -> x <> y -> f x = None) : NoDup l -> NoDup (mapfilter l).
    Proof.
      induction 1 as [|x]; cbn [mapfilter]; trivial using NoDup_nil.
      case f eqn:?; try constructor; trivial.
      intros (y&?&?)%in_mapfilter.
      firstorder congruence || (* Tactic failure: no link *)
      assert (x <> y) as HH by congruence; 
      specialize (Hf x y ltac:(congruence) HH); congruence.
    Qed.
  End WithF.

  Lemma mapfilter_Some {A B} (f : A -> B) l :
    mapfilter (fun x => Some (f x)) l = map f l.
  Proof. induction l; cbn; congruence. Qed.

  Lemma mapfilter_ext {A B} (f g : A -> option B) l :
    Forall (fun x => f x = g x) l ->
    mapfilter f l = mapfilter g l.
  Proof.
    induction 1; cbn; trivial.
    rewrite H; destruct g; congruence.
  Qed.

  Lemma mapfilter_map {A B C} (f : A -> B) (g : B -> option C) l :
    mapfilter g (map f l) = mapfilter (fun x => g (f x)) l.
  Proof.
    induction l; cbn [mapfilter map]; trivial.
    destruct g; congruence.
  Qed.

  Lemma map_mapfilter {A B C} (f : A -> option B) (g : B -> C) l :
    map g (mapfilter f l) = mapfilter (fun x => option_map g (f x)) l.
  Proof.
    induction l; cbn [mapfilter map]; trivial.
    destruct f; cbn [option_map map]; congruence.
  Qed.
End List.

Require Permutation.
Module Import Permutation.
Import Permutation.
Lemma Permutation_map_same_l {A} (f : A -> A) (l : list A) :
  List.NoDup (List.map f l) -> List.incl (List.map f l) l -> Permutation (List.map f l) l.
Proof.
  intros; eapply Permutation.NoDup_Permutation_bis; rewrite ?List.map_length; trivial.
Qed.
End Permutation.
