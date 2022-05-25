Require Import ZArith.
Require Import Uint63.
Require Import ZifyBool.
Import ZifyClasses.

Lemma to_Z_bounded : forall x, (0 <= to_Z x < 9223372036854775808)%Z.
Proof. apply to_Z_bounded. Qed.

#[global]
Instance Inj_int_Z : InjTyp int Z :=
  mkinj _ _ to_Z (fun x => 0 <= x < 9223372036854775808)%Z to_Z_bounded.
Add Zify InjTyp Inj_int_Z.

#[global]
Instance Op_max_int : CstOp max_int :=
  { TCst := 9223372036854775807 ; TCstInj := eq_refl }.
Add Zify CstOp Op_max_int.

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
  (n <? m)%uint63 = (φ (n)%uint63 <? φ (m)%uint63)%Z.
Proof.
  intros. apply Bool.eq_true_iff_eq.
  rewrite ltb_spec. rewrite <- Z.ltb_lt.
  apply iff_refl.
Qed.

#[global]
Instance Op_ltb : BinOp ltb :=
  {| TBOp := Z.ltb; TBOpInj := ltb_lt |}.
Add Zify BinOp Op_ltb.

Lemma leb_le : forall n m,
  (n <=? m)%uint63 = (φ (n)%uint63 <=? φ (m)%uint63)%Z.
Proof.
  intros. apply Bool.eq_true_iff_eq.
  rewrite leb_spec. rewrite <- Z.leb_le.
  apply iff_refl.
Qed.

#[global]
Instance Op_leb : BinOp leb :=
  {| TBOp := Z.leb; TBOpInj := leb_le |}.
Add Zify BinOp Op_leb.

Lemma eqb_eq : forall n m,
  (n =? m)%uint63 = (φ (n)%uint63 =? φ (m)%uint63)%Z.
Proof.
  intros. apply Bool.eq_true_iff_eq.
  rewrite eqb_spec. rewrite Z.eqb_eq.
  split ; intro H.
  - now subst; reflexivity.
  - now apply to_Z_inj in H.
Qed.

#[global]
Instance Op_eqb : BinOp eqb :=
  {| TBOp := Z.eqb; TBOpInj := eqb_eq |}.
Add Zify BinOp Op_eqb.

Lemma eq_int_inj : forall  n m : int, n = m <-> (φ  n = φ m)%uint63.
Proof.
  split; intro H.
  - rewrite H ; reflexivity.
  - apply to_Z_inj; auto.
Qed.

#[global]
Instance Op_eq : BinRel (@eq int) :=
  {| TR := @eq Z; TRInj := eq_int_inj |}.
Add Zify BinRel Op_eq.

#[global]
Instance Op_add : BinOp add :=
  {| TBOp := fun x y => (x + y) mod 9223372036854775808%Z; TBOpInj := add_spec |}%Z.
Add Zify BinOp Op_add.

#[global]
Instance Op_sub : BinOp sub :=
  {| TBOp := fun x y => (x - y) mod 9223372036854775808%Z; TBOpInj := sub_spec |}%Z.
Add Zify BinOp Op_sub.

#[global]
Instance Op_opp : UnOp Uint63.opp :=
  {| TUOp := (fun x => (- x) mod 9223372036854775808)%Z; TUOpInj := (sub_spec 0) |}%Z.
Add Zify UnOp Op_opp.

#[global]
Instance Op_oppcarry : UnOp oppcarry :=
  {| TUOp := (fun x => 2^63 -  x - 1)%Z; TUOpInj := oppcarry_spec |}%Z.
Add Zify UnOp Op_oppcarry.

#[global]
Instance Op_succ : UnOp succ :=
  {| TUOp := (fun x => (x + 1) mod 2^63)%Z; TUOpInj := succ_spec |}%Z.
Add Zify UnOp Op_succ.

#[global]
Instance Op_pred : UnOp Uint63.pred :=
  {| TUOp := (fun x => (x - 1) mod 2^63)%Z; TUOpInj := pred_spec |}%Z.
Add Zify UnOp Op_pred.

#[global]
Instance Op_mul : BinOp mul :=
  {| TBOp := fun x y => (x * y) mod 9223372036854775808%Z; TBOpInj := mul_spec |}%Z.
Add Zify BinOp Op_mul.

#[global]
Instance Op_gcd : BinOp gcd:=
  {| TBOp := (fun x y => Zgcd_alt.Zgcdn (2 * 63)%nat y x) ; TBOpInj := to_Z_gcd |}.
Add Zify BinOp Op_gcd.

#[global]
Instance Op_mod : BinOp Uint63.mod :=
  {| TBOp := Z.modulo ; TBOpInj := mod_spec |}.
Add Zify BinOp Op_mod.

#[global]
Instance Op_subcarry : BinOp subcarry :=
  {| TBOp := (fun x y => (x - y - 1) mod 2^63)%Z ; TBOpInj := subcarry_spec |}.
Add Zify BinOp Op_subcarry.

#[global]
Instance Op_addcarry : BinOp addcarry :=
  {| TBOp := (fun x y => (x + y + 1) mod 2^63)%Z ; TBOpInj := addcarry_spec |}.
Add Zify BinOp Op_addcarry.

#[global]
Instance Op_lsr : BinOp lsr :=
  {| TBOp := (fun x y => x / 2^ y)%Z ; TBOpInj := lsr_spec |}.
Add Zify BinOp Op_lsr.

#[global]
Instance Op_lsl : BinOp lsl :=
  {| TBOp := (fun x y => (x  * 2^ y) mod 2^ 63)%Z ; TBOpInj := lsl_spec |}.
Add Zify BinOp Op_lsl.

#[global]
Instance Op_lor : BinOp Uint63.lor :=
  {| TBOp := Z.lor ; TBOpInj := lor_spec' |}.
Add Zify BinOp Op_lor.

#[global]
Instance Op_land : BinOp Uint63.land :=
  {| TBOp := Z.land ; TBOpInj := land_spec' |}.
Add Zify BinOp Op_land.

#[global]
Instance Op_lxor : BinOp Uint63.lxor :=
  {| TBOp := Z.lxor ; TBOpInj := lxor_spec' |}.
Add Zify BinOp Op_lxor.

#[global]
Instance Op_div : BinOp div :=
  {| TBOp := Z.div ; TBOpInj := div_spec |}.
Add Zify BinOp Op_div.

#[global]
Instance Op_bit : BinOp bit :=
  {| TBOp := Z.testbit ; TBOpInj := bitE |}.
Add Zify BinOp Op_bit.

#[global]
Instance Op_of_Z : UnOp of_Z :=
  { TUOp := (fun x => x mod 9223372036854775808)%Z; TUOpInj := of_Z_spec }.
Add Zify UnOp Op_of_Z.

#[global]
Instance Op_to_Z : UnOp to_Z :=
  { TUOp := fun x => x ; TUOpInj := fun x : int => eq_refl }.
Add Zify UnOp Op_to_Z.

#[global]
Instance Op_is_zero : UnOp is_zero :=
  { TUOp := (Z.eqb 0) ; TUOpInj := is_zeroE }.
Add Zify UnOp Op_is_zero.

Lemma is_evenE : forall x,
    is_even x = Z.even φ (x)%uint63.
Proof.
  intros.
  generalize (is_even_spec x).
  rewrite Z_evenE.
  destruct (is_even x).
  - symmetry. apply Z.eqb_eq. auto.
  - symmetry. apply Z.eqb_neq. congruence.
Qed.

#[global]
Instance Op_is_even : UnOp is_even :=
  { TUOp := Z.even ; TUOpInj := is_evenE }.
Add Zify UnOp Op_is_even.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
