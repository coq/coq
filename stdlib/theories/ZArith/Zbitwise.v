Require Import BinInt Lia Btauto. Local Open Scope Z_scope.
Import (ltac.notations) BinInt.Z.

Module Z.

Local Infix ".|" := Z.lor (at level 40).
Local Infix ".&" := Z.land (at level 40).
Local Infix ".^" := Z.lxor (at level 40).
Local Notation ".~ x" := (Z.lnot x) (at level 35).
Local Notation "x .[ i ]" := (Z.testbit x i) (at level 9, format "x .[ i ]").

Local Infix "^^" := xorb (at level 40).

Local Hint Rewrite
  Z.b2z_bit0
  Z.bits_opp
  Z.lnot_spec
  Z.testbit_ones_nonneg
  Z.testbit_ones
  Z.add_bit0
  Z.shiftl_spec
  Z.shiftr_spec
  using solve [trivial] : bitwise.

Local Ltac to_bitwise :=
  let i := fresh "i" in
  bitwise as i ?Hi;
  repeat match goal with H : ?a = ?b :> Z |- _ =>
    apply (f_equal (fun x => Z.testbit x i)) in H end.
Local Ltac prove_bitwise :=
  apply Bool.eqb_true_iff;
  repeat match goal with H : _ = _ :> bool |- _ =>
    apply Bool.eqb_true_iff in H; revert H end;
  rewrite <-?Bool.negb_xorb, <-?Bool.implb_true_iff, ?Bool.implb_orb;
  autorewrite with bitwise;
  btauto.
Local Ltac p := to_bitwise; prove_bitwise.

(** Bitwise operations alone *)

Lemma lnot_lnot x : Z.lnot (Z.lnot x) = x.
Proof. apply Z.lnot_involutive. Qed.

Lemma ldiff_lor_land x y : Z.ldiff (x .| y) (x .& y) = x .^ y.
Proof. p. Qed.

(** Bitwise complement and +1/-1 *)

Lemma succ_lnot x : Z.lnot x + 1 = - x.
Proof. pose proof Z.add_lnot_diag x; lia. Qed.

Lemma lnot_pred x : Z.lnot (x - 1) = - x.
Proof. pose proof succ_lnot (x-1). lia. Qed.

Lemma lnot_eq_pred_opp x : Z.lnot x = -x-1.
Proof. pose proof lnot_pred (x+1). replace (x+1-1) with x in *; lia. Qed.

Lemma opp_lnot x : - (Z.lnot x) = x+1.
Proof. pose proof Z.add_lnot_diag x; lia. Qed.

Lemma lnot_opp x : Z.lnot (-x) = x-1.
Proof. pose proof Z.add_lnot_diag (-x); lia. Qed.

(** Bitwise complement as an input to + or - *)

Lemma sub_lnot_r x y : x - Z.lnot y = x + y + 1.
Proof. pose proof lnot_eq_pred_opp y; pose proof lnot_lnot y; lia. Qed.

Lemma pred_sub_lnot_r x y : x - Z.lnot y - 1 = x + y.
Proof. pose proof sub_lnot_r x y; lia. Qed.

Lemma add_lnot_r x y : x + Z.lnot y = x - y - 1.
Proof. pose proof lnot_eq_pred_opp y; pose proof lnot_lnot y; lia. Qed.

Lemma succ_add_lnot_r x y : x + Z.lnot y + 1 = x - y.
Proof. pose proof add_lnot_r x y; lia. Qed.

Lemma lnot_sub x y : Z.lnot (x - y) = Z.lnot x + y.
Proof. rewrite !lnot_eq_pred_opp; lia. Qed.

(** Explicit formulas for carry bits during addition. Conceptually, the theory
 * here matches the bitblasting rules for integers. However, the vector of
 * carry bits is represented as a [Z] so it can be used in bitwise operations.
 * The last three lemmas about [addcarries] are the main interface, but the
 * generalization [adccarries] is provided as the same theory applies. *)

Definition adccarries (x y : Z) (c : bool) := (x + y + Z.b2z c) .^ (x .^ y).
Definition addcarries (x y : Z)            := (x + y)           .^ (x .^ y).

Lemma addcarries_ok x y : addcarries x y = adccarries x y false.
Proof. cbv [addcarries adccarries] in *; rewrite Z.add_0_r; trivial. Qed.

Lemma addcarryeqn (x y : Z) (c0 : bool)
  (z := (x + y + Z.b2z c0))
  (c := z .^ (x .^ y))
  : Z.shiftr c 1 = (x .& y) .| (c .& (x .^ y)).
Proof.
  case (Z.add_carry_bits x y c0) as (C&?&?&?).
  enough (Z.shiftr c 1 = (x .& y) .| (c .& (x .| y))) by p.
  assert (C = (x + y + Z.b2z c0) .^ (x .^ y)) as HC by p.
  rewrite <-Z.div2_div, Z.div2_spec in H0.
  subst c z; congruence.
Qed.

Lemma testbit_adccarries_0 x y c : Z.testbit (adccarries x y c) 0 = c.
Proof. cbv [adccarries]. autorewrite with bitwise. btauto. Qed.

Lemma shiftr_adccarries_1 x y c : Z.shiftr (adccarries x y c) 1 =
  (x .& y) .| ((x .^ y) .& (adccarries x y c)).
Proof. cbv [adccarries]. rewrite addcarryeqn. p. Qed.

Lemma testbit_adccarries_pos x y c i (Hi : 0 < i) : Z.testbit (adccarries x y c) i =
  (x.[i-1] && y.[i-1] || (x.[i-1]^^y.[i-1]) && (adccarries x y c).[i-1])%bool.
Proof.
  pose proof shiftr_adccarries_1 x y c.
  apply (f_equal (fun x => Z.testbit x (i-1))) in H.
  autorewrite with bitwise in H; rewrite <-H.
  rewrite Z.shiftr_spec; try lia. f_equal; lia.
Qed.

Lemma testbit_addcarries_0 x y : Z.testbit (addcarries x y) 0 = false.
Proof. rewrite addcarries_ok; apply testbit_adccarries_0. Qed.

Lemma shiftr_addcarries_1 x y : Z.shiftr (addcarries x y) 1 =
  (x .& y) .| ((x .^ y) .& (addcarries x y)).
Proof. rewrite addcarries_ok; apply shiftr_adccarries_1. Qed.

Lemma testbit_addcarries_pos x y i (Hi : 0 < i) : Z.testbit (addcarries x y) i =
  (x.[i-1] && y.[i-1] || (x.[i-1]^^y.[i-1]) && (addcarries x y).[i-1])%bool.
Proof. rewrite addcarries_ok; apply testbit_adccarries_pos, Hi. Qed.

Local Hint Rewrite testbit_adccarries_0 testbit_addcarries_0 : bitwise.

Lemma addcarries_lor_land x y : addcarries (x .| y) (x .& y) = addcarries x y.
Proof.
  apply Z.bits_inj'; refine (Wf_Z.natlike_ind _ _ _); [prove_bitwise|intros i??].
  rewrite 2 (testbit_addcarries_pos _ _ (* work around coq#7672: *) (Z.succ i))
    by lia; replace (Z.succ i-1) with i by lia; prove_bitwise.
Qed.

(** Bitwise operations, addition, and subtraction *)

Lemma sub_lor_land x y : (x .| y) - (x .& y) = (x .^ y).
Proof. rewrite Z.sub_nocarry_ldiff, <-ldiff_lor_land; trivial. p. Qed.

Lemma add_lor_land x y : (x .| y) + (x .& y) = (x + y).
Proof. pose proof addcarries_lor_land x y. cbv [addcarries] in *. p. Qed.

Lemma sub_lor_l_same_l x y : y .| x - y = x .& .~ y.
Proof. rewrite Z.sub_nocarry_ldiff; p. Qed.

Lemma sub_lor_l_same_r x y : x .| y - y = x .& .~ y.
Proof. rewrite Z.sub_nocarry_ldiff; p. Qed.

Lemma sub_landn_rlandn x y : x.&.~y - .~x .& y = x - y.
Proof. rewrite (Z.land_comm (.~ _)), <-2sub_lor_l_same_r, Z.lor_comm; lia. Qed.

Lemma sub_land_same_l x y : x - x.&y = x .& .~y.
Proof. rewrite Z.sub_nocarry_ldiff; p. Qed.

(** Bitwise operations, addition, subtraction, and doubling *)

Lemma add_lxor_2land x y : (x .^ y) + 2*(x .& y) = x + y.
Proof. symmetry; rewrite <-add_lor_land, <-sub_lor_land; lia. Qed.

Lemma sub_2lor_lxor x y : 2*(x .| y) - x .^ y = x + y.
Proof. rewrite <-add_lxor_2land, <-sub_lor_land. lia. Qed.

Lemma sub_lxor_2rlandn x y : x .^ y - 2*(.~x .& y) = x - y.
Proof.
  rewrite (Z.land_comm (.~ _)), <-sub_lor_l_same_l, <-sub_lor_land.
  pose proof add_lor_land x y. lia.
Qed.

Lemma sub_2landn_lxor x y : 2*(x.&.~y) - x.^y = x - y.
Proof. rewrite <-sub_lor_l_same_r, <-sub_lor_land. pose (add_lor_land x y). lia. Qed.

End Z.
