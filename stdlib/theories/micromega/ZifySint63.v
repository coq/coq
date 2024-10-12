Require Import ZArith.
Require Import Sint63.
Require Import ZifyBool.
Import ZifyClasses.

Lemma to_Z_bounded (x : int) :
  (-4611686018427387904 <= to_Z x <= 4611686018427387903)%Z.
Proof. now apply to_Z_bounded. Qed.

#[global]
Instance Inj_int_Z : InjTyp int Z :=
  mkinj _ _ to_Z (fun x => -4611686018427387904 <= x <= 4611686018427387903)%Z
    to_Z_bounded.
Add Zify InjTyp Inj_int_Z.

#[global]
Instance Op_max_int : CstOp max_int :=
  { TCst := 4611686018427387903 ; TCstInj := eq_refl }.
Add Zify CstOp Op_max_int.

#[global]
Instance Op_min_int : CstOp min_int :=
  { TCst := -4611686018427387904 ; TCstInj := eq_refl }.
Add Zify CstOp Op_min_int.

#[global]
Instance Op_digits : CstOp digits :=
  { TCst := 63 ; TCstInj := eq_refl }.
Add Zify CstOp Op_digits.

#[global]
Instance Op_size : CstOp size :=
  { TCst := 63 ; TCstInj := eq_refl }.
Add Zify CstOp Op_size.

#[global]
Instance Op_wB : CstOp wB :=
  { TCst := 2^63 ; TCstInj := eq_refl }.
Add Zify CstOp Op_wB.

Lemma ltb_lt : forall n m,
  (n <? m)%sint63 = (to_Z n <? to_Z m)%Z.
Proof.
  intros; apply Bool.eq_true_iff_eq.
  rewrite ltb_spec, Z.compare_lt_iff, <- Z.ltb_lt.
  apply iff_refl.
Qed.

#[global]
Instance Op_ltb : BinOp ltb :=
  {| TBOp := Z.ltb; TBOpInj := ltb_lt |}.
Add Zify BinOp Op_ltb.

Lemma leb_le : forall n m,
  (n <=? m)%sint63 = (to_Z n <=? to_Z m)%Z.
Proof.
  intros; apply Bool.eq_true_iff_eq.
  rewrite leb_spec, Z.compare_le_iff, <- Z.leb_le.
  apply iff_refl.
Qed.

#[global]
Instance Op_leb : BinOp leb :=
  {| TBOp := Z.leb; TBOpInj := leb_le |}.
Add Zify BinOp Op_leb.

Lemma eqb_eq : forall n m,
  (n =? m)%sint63 = (to_Z n =? to_Z m)%Z.
Proof.
  intros; apply Bool.eq_true_iff_eq.
  rewrite eqb_spec, Z.eqb_eq.
  split; intro H.
  - now subst; reflexivity.
  - now apply to_Z_inj in H.
Qed.

#[global]
Instance Op_eqb : BinOp eqb :=
  {| TBOp := Z.eqb; TBOpInj := eqb_eq |}.
Add Zify BinOp Op_eqb.

Lemma eq_int_inj : forall  n m : int, n = m <-> (to_Z n = to_Z m)%sint63.
Proof.
  split; intro H.
  - rewrite H; reflexivity.
  - now apply to_Z_inj.
Qed.

#[global]
Instance Op_eq : BinRel (@eq int) :=
  {| TR := @eq Z; TRInj := eq_int_inj |}.
Add Zify BinRel Op_eq.

Notation cmodwB x :=
  ((x + 4611686018427387904) mod 9223372036854775808 - 4611686018427387904)%Z.

#[global]
Instance Op_add : BinOp add :=
  {| TBOp := fun x y => cmodwB (x + y); TBOpInj := add_spec |}%Z.
Add Zify BinOp Op_add.

#[global]
Instance Op_sub : BinOp sub :=
  {| TBOp := fun x y => cmodwB (x - y); TBOpInj := sub_spec |}%Z.
Add Zify BinOp Op_sub.

#[global]
Instance Op_opp : UnOp Uint63.opp :=
  {| TUOp := fun x => cmodwB (- x); TUOpInj := (sub_spec 0) |}%Z.
Add Zify UnOp Op_opp.

#[global]
Instance Op_succ : UnOp succ :=
  {| TUOp := fun x => cmodwB (x + 1); TUOpInj := succ_spec |}%Z.
Add Zify UnOp Op_succ.

#[global]
Instance Op_pred : UnOp Uint63.pred :=
  {| TUOp := fun x => cmodwB (x - 1); TUOpInj := pred_spec |}%Z.
Add Zify UnOp Op_pred.

#[global]
Instance Op_mul : BinOp mul :=
  {| TBOp := fun x y => cmodwB (x * y); TBOpInj := mul_spec |}%Z.
Add Zify BinOp Op_mul.

#[global]
Instance Op_mod : BinOp PrimInt63.mods :=
  {| TBOp := Z.rem ; TBOpInj := mod_spec |}.
Add Zify BinOp Op_mod.

#[global]
Instance Op_asr : BinOp asr :=
  {| TBOp := fun x y => x / 2^ y ; TBOpInj := asr_spec |}%Z.
Add Zify BinOp Op_asr.

Definition quots (x d : Z) : Z :=
  if ((x =? -4611686018427387904)%Z && (d =? -1)%Z)%bool then
    -4611686018427387904
  else
    Z.quot x d.

Lemma div_quots (x y : int) : to_Z (x / y) = quots (to_Z x) (to_Z y).
Proof.
  unfold quots; destruct andb eqn: eq_min_m1.
  - rewrite Bool.andb_true_iff, !Z.eqb_eq in eq_min_m1.
    change (-4611686018427387904)%Z with (to_Z min_int) in eq_min_m1.
    change (-1)%Z with (to_Z (-1)) in eq_min_m1.
    destruct eq_min_m1 as [to_Z_x_min to_Z_y_m1].
    now rewrite (to_Z_inj _ _ to_Z_x_min), (to_Z_inj _ _ to_Z_y_m1).
  - apply div_spec.
    now rewrite Bool.andb_false_iff, !Z.eqb_neq in eq_min_m1.
Qed.

#[global]
Instance Op_div : BinOp div :=
  {| TBOp := quots ; TBOpInj := div_quots |}.
Add Zify BinOp Op_div.

Lemma quots_spec (x y : Z) :
  ((x = -4611686018427387904 /\ y = -1 /\ quots x y = -4611686018427387904)
  \/ ((x <> -4611686018427387904 \/ y <> -1) /\ quots x y = Z.quot x y))%Z.
Proof.
  unfold quots; case andb eqn: eq_min_m1.
  - now left; rewrite Bool.andb_true_iff, !Z.eqb_eq in eq_min_m1.
  - now right; rewrite Bool.andb_false_iff, !Z.eqb_neq in eq_min_m1.
Qed.

#[global]
Instance quotsSpec : BinOpSpec quots :=
  {| BPred := fun x d r : Z =>
       ((x = -4611686018427387904 /\ d = -1 /\ r = -4611686018427387904)
       \/ ((x <> -4611686018427387904 \/ d <> -1) /\ r = Z.quot x d))%Z;
     BSpec := quots_spec |}.
Add Zify BinOpSpec quotsSpec.

#[global]
Instance Op_of_Z : UnOp of_Z :=
  { TUOp := fun x => cmodwB x; TUOpInj := of_Z_spec }.
Add Zify UnOp Op_of_Z.

#[global]
Instance Op_to_Z : UnOp to_Z :=
  { TUOp := fun x => x ; TUOpInj := fun x : int => eq_refl }.
Add Zify UnOp Op_to_Z.

Lemma is_zeroE : forall n : int, is_zero n = (to_Z n =? 0)%Z.
Proof.
  intro n; apply Bool.eq_true_iff_eq.
  rewrite is_zero_spec, Z.eqb_eq; split.
  - now intro eqn0; rewrite eqn0.
  - now change 0%Z with (to_Z 0); apply to_Z_inj.
Qed.

#[global]
Instance Op_is_zero : UnOp is_zero :=
  { TUOp := (Z.eqb 0) ; TUOpInj := is_zeroE }.
Add Zify UnOp Op_is_zero.

#[global]
Instance Op_abs : UnOp abs :=
  { TUOp := fun x => cmodwB (Z.abs x) ; TUOpInj := abs_spec }.
Add Zify UnOp Op_abs.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
