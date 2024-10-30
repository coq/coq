(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
(*            Benjamin Gregoire, Laurent Thery, INRIA, 2007             *)
(************************************************************************)

Require Import Utf8.
Require Export DoubleType.
Require Import Lia.
Require Import Zpow_facts.
Require Import Zgcd_alt.
Require ZArith.
Import Znumtheory.
Require Export PrimInt63 Uint63Axioms.

Notation int := int (only parsing).
Notation lsl := lsl (only parsing).
Notation lsr := lsr (only parsing).
Notation land := land (only parsing).
Notation lor := lor (only parsing).
Notation lxor := lxor (only parsing).
Notation add := add (only parsing).
Notation sub := sub (only parsing).
Notation mul := mul (only parsing).
Notation mulc := mulc (only parsing).
Notation div := div (only parsing).
Notation mod := mod (only parsing).
Notation eqb := eqb (only parsing).
Notation ltb := ltb (only parsing).
Notation leb := leb (only parsing).

Notation size := Uint63Axioms.size (only parsing).
Notation digits := Uint63Axioms.digits (only parsing).
Notation max_int := Uint63Axioms.max_int (only parsing).
Notation get_digit := Uint63Axioms.get_digit (only parsing).
Notation set_digit := Uint63Axioms.set_digit (only parsing).
Notation is_zero := Uint63Axioms.is_zero (only parsing).
Notation is_even := Uint63Axioms.is_even (only parsing).
Notation bit := Uint63Axioms.bit (only parsing).
Notation addcarry := Uint63Axioms.addcarry (only parsing).
Notation to_Z := Uint63Axioms.to_Z (only parsing).
Notation of_pos := Uint63Axioms.of_pos (only parsing).
Notation of_Z := Uint63Axioms.of_Z (only parsing).
Notation wB := Uint63Axioms.wB (only parsing).
Notation of_to_Z := Uint63Axioms.of_to_Z (only parsing).
Notation lsl_spec := Uint63Axioms.lsl_spec (only parsing).
Notation lsr_spec := Uint63Axioms.lsr_spec (only parsing).
Notation land_spec := Uint63Axioms.land_spec (only parsing).
Notation lor_spec := Uint63Axioms.lor_spec (only parsing).
Notation lxor_spec := Uint63Axioms.lxor_spec (only parsing).
Notation add_spec := Uint63Axioms.add_spec (only parsing).
Notation sub_spec := Uint63Axioms.sub_spec (only parsing).
Notation mul_spec := Uint63Axioms.mul_spec (only parsing).
Notation mulc_spec := Uint63Axioms.mulc_spec (only parsing).
Notation div_spec := Uint63Axioms.div_spec (only parsing).
Notation mod_spec := Uint63Axioms.mod_spec (only parsing).
Notation eqb_correct := Uint63Axioms.eqb_correct (only parsing).
Notation eqb_refl := Uint63Axioms.eqb_refl (only parsing).
Notation ltb_spec := Uint63Axioms.ltb_spec (only parsing).
Notation leb_spec := Uint63Axioms.leb_spec (only parsing).
Notation compare_def_spec := Uint63Axioms.compare_def_spec (only parsing).
Notation head0_spec := Uint63Axioms.head0_spec (only parsing).
Notation tail0_spec := Uint63Axioms.tail0_spec (only parsing).
Notation addc_def_spec := Uint63Axioms.addc_def_spec (only parsing).
Notation addcarryc_def_spec := Uint63Axioms.addcarryc_def_spec (only parsing).
Notation subc_def_spec := Uint63Axioms.subc_def_spec (only parsing).
Notation subcarryc_def_spec := Uint63Axioms.subcarryc_def_spec (only parsing).
Notation diveucl_def_spec := Uint63Axioms.diveucl_def_spec (only parsing).
Notation diveucl_21_spec := Uint63Axioms.diveucl_21_spec (only parsing).
Notation addmuldiv_def_spec := Uint63Axioms.addmuldiv_def_spec (only parsing).

Local Open Scope uint63_scope.

Module Import Uint63NotationsInternalB.
Infix "<<" := lsl (at level 30, no associativity) : uint63_scope.
Infix ">>" := lsr (at level 30, no associativity) : uint63_scope.
Infix "land" := land (at level 40, left associativity) : uint63_scope.
Infix "lor" := lor (at level 40, left associativity) : uint63_scope.
Infix "lxor" := lxor (at level 40, left associativity) : uint63_scope.
Infix "+" := add : uint63_scope.
Infix "-" := sub : uint63_scope.
Infix "*" := mul : uint63_scope.
Infix "/" := div : uint63_scope.
Infix "mod" := mod (at level 40, no associativity) : uint63_scope.
Infix "=?" := eqb (at level 70, no associativity) : uint63_scope.
Infix "<?" := ltb (at level 70, no associativity) : uint63_scope.
Infix "<=?" := leb (at level 70, no associativity) : uint63_scope.
Infix "≤?" := leb (at level 70, no associativity) : uint63_scope.
End Uint63NotationsInternalB.

Register Inline max_int.
Register Inline is_zero.
Register Inline is_even.
(* Register bit as PrimInline. *)

(** Extra modulo operations *)
Definition opp (i:int) := 0 - i.
Register Inline opp.

Definition oppcarry i := max_int - i.
Register Inline oppcarry.

Definition succ i := i + 1.
Register Inline succ.

Definition pred i := i - 1.
Register Inline pred.

Register Inline addcarry.

Definition subcarry i j := i - j - 1.
Register Inline subcarry.

(** Exact arithmetic operations *)

Notation addc := addc (only parsing).
Notation addcarryc := addcarryc (only parsing).
Notation subc := subc (only parsing).
Notation subcarryc := subcarryc (only parsing).
Notation diveucl := diveucl (only parsing).
Notation diveucl_21 := diveucl_21 (only parsing).
Notation addmuldiv := addmuldiv (only parsing).

Module Import Uint63NotationsInternalC.
Notation "- x" := (opp x) : uint63_scope.
Notation "n '+c' m" := (addc n m) (at level 50, no associativity) : uint63_scope.
Notation "n '-c' m" := (subc n m) (at level 50, no associativity) : uint63_scope.
End Uint63NotationsInternalC.

Definition oppc (i:int) := 0 -c i.
Register Inline oppc.

Definition succc i := i +c 1.
Register Inline succc.

Definition predc i := i -c 1.
Register Inline predc.

Notation compare := compare (only parsing).

Import Bool ZArith.

Notation to_nat i := (Z.to_nat (to_Z i)).
Notation of_nat n := (of_Z (Z.of_nat n)).

Module Import Uint63NotationsInternalD.
Notation "n ?= m" := (compare n m) (at level 70, no associativity) : uint63_scope.
Notation "'φ' x" := (to_Z x) (at level 0) : uint63_scope.
Notation "'Φ' x" :=
   (zn2z_to_Z wB to_Z x) (at level 0) : uint63_scope.
End Uint63NotationsInternalD.

Lemma to_Z_rec_bounded size : forall x, (0 <= to_Z_rec size x < 2 ^ Z.of_nat size)%Z.
Proof.
  elim size.
  - simpl; auto with zarith.
  - intros n ih x; rewrite inj_S; simpl; assert (W := ih (x >> 1)%uint63).
    rewrite Z.pow_succ_r; auto with zarith.
    destruct (is_even x).
    + rewrite Zdouble_mult; auto with zarith.
    + rewrite Zdouble_plus_one_mult; auto with zarith.
Qed.

Corollary to_Z_bounded : forall x, (0 <= φ  x  < wB)%Z.
Proof. apply to_Z_rec_bounded. Qed.


(* =================================================== *)
Local Open Scope Z_scope.
(* General arithmetic results *)

Theorem Zmod_distr: forall a b r t, 0 <= a <= b -> 0 <= r -> 0 <= t < 2 ^a ->
  (2 ^a * r + t) mod (2 ^ b) = (2 ^a * r) mod (2 ^ b) + t.
Proof.
  intros a b r t ? ? ?.
  replace (2^b) with (2^a * 2^(b-a)) by (rewrite <-Zpower_exp; [f_equal| |]; lia).
  assert (0 < 2 ^ (b - a)) by (apply Z.pow_pos_nonneg; lia).
  rewrite Z.add_mul_mod_distr_l, <- Z.mul_mod_distr_l; lia.
Qed.

(* Results about pow2 *)
Lemma pow2_pos n : 0 <= n → 2 ^ n > 0.
Proof. intros h; apply Z.lt_gt, Zpower_gt_0; lia. Qed.

Lemma pow2_nz n : 0 <= n → 2 ^ n ≠ 0.
Proof. intros h; generalize (pow2_pos _ h); lia. Qed.

#[global]
Hint Resolve pow2_pos pow2_nz : zarith.

(* =================================================== *)

(** Trivial lemmas without axiom *)

Lemma wB_diff_0 : wB <> 0.
Proof. exact (fun x => let 'eq_refl := x in idProp). Qed.

Lemma wB_pos : 0 < wB.
Proof. reflexivity. Qed.

Lemma to_Z_0 : φ 0 = 0.
Proof. reflexivity. Qed.

Lemma to_Z_1 : φ 1 = 1.
Proof. reflexivity. Qed.

(* Notations *)
Local Open Scope Z_scope.

Local Notation "[+| c |]" :=
   (interp_carry 1 wB to_Z c)  (at level 0, c at level 99) : uint63_scope.

Local Notation "[-| c |]" :=
   (interp_carry (-1) wB to_Z c)  (at level 0, c at level 99) : uint63_scope.

Lemma can_inj {rT aT} {f: aT -> rT} {g: rT -> aT} (K: forall a, g (f a) = a) {a a'} (e: f a = f a') : a = a'.
Proof. generalize (K a) (K a'). congruence. Qed.

Lemma to_Z_inj x y : φ x = φ y → x = y.
Proof. exact (λ e, can_inj of_to_Z e). Qed.

(** I should add the definition (like for compare) *)
Notation head0 := head0 (only parsing).
Notation tail0 := tail0 (only parsing).

(** Square root functions using newton iteration **)
Local Open Scope uint63_scope.

Definition sqrt_step (rec: int -> int -> int) (i j: int) :=
  let quo := i / j in
  if quo <? j then rec i ((j + quo) >> 1)
  else j.

Definition iter_sqrt :=
 Eval lazy beta delta [sqrt_step] in
 fix iter_sqrt (n: nat) (rec: int -> int -> int)
          (i j: int) {struct n} : int :=
  sqrt_step
   (fun i j => match n with
      O =>  rec i j
   | S n => (iter_sqrt n (iter_sqrt n rec)) i j
   end) i j.

Definition sqrt i :=
  match compare 1 i with
    Gt => 0
  | Eq => 1
  | Lt => iter_sqrt size (fun i j => j) i (i >> 1)
  end.

Definition high_bit := 1 << (digits - 1).

Definition sqrt2_step (rec: int -> int -> int -> int)
   (ih il j: int)  :=
  if ih <? j then
    let (quo,_) := diveucl_21 ih il j in
    if quo <? j then
      match j +c quo with
      | C0 m1 => rec ih il (m1 >> 1)
      | C1 m1 => rec ih il ((m1 >> 1) + high_bit)
      end
    else j
  else j.

Definition iter2_sqrt :=
 Eval lazy beta delta [sqrt2_step] in
 fix iter2_sqrt (n: nat)
          (rec: int  -> int -> int -> int)
          (ih il j: int) {struct n} : int :=
  sqrt2_step
   (fun ih il j =>
     match n with
     | O =>  rec ih il j
     | S n => (iter2_sqrt n (iter2_sqrt n rec)) ih il j
   end) ih il j.

Definition sqrt2 ih il :=
  let s := iter2_sqrt size (fun ih il j => j) ih il max_int in
  let (ih1, il1) := mulc s s in
  match il -c il1 with
  | C0 il2 =>
    if ih1 <? ih then (s, C1 il2) else (s, C0 il2)
  | C1 il2 =>
    if ih1 <? (ih - 1) then (s, C1 il2) else (s, C0 il2)
  end.

(** Gcd **)
Fixpoint gcd_rec (guard:nat) (i j:int) {struct guard} :=
   match guard with
   | O => 1
   | S p => if j =? 0 then i else gcd_rec p j (i mod j)
   end.

Definition gcd := gcd_rec (2*size).

(** equality *)
Lemma eqb_complete : forall x y, x = y -> (x =? y) = true.
Proof.
 now intros x y H; rewrite H, Uint63Axioms.eqb_refl.
Qed.

Lemma eqb_spec : forall x y, (x =? y) = true <-> x = y.
Proof.
 split;auto using eqb_correct, eqb_complete.
Qed.

Lemma eqb_false_spec : forall x y, (x =? y) = false <-> x <> y.
Proof.
 intros;rewrite <- not_true_iff_false, eqb_spec;split;trivial.
Qed.

Lemma eqb_false_complete : forall x y, x <> y -> (x =? y) = false.
Proof.
 intros x y;rewrite eqb_false_spec;trivial.
Qed.

Lemma eqb_false_correct : forall x y, (x =? y) = false -> x <> y.
Proof.
 intros x y;rewrite eqb_false_spec;trivial.
Qed.

Definition eqs (i j : int) : {i = j} + { i <> j } :=
  (if i =? j as b return ((b = true -> i = j) -> (b = false -> i <> j) -> {i=j} + {i <> j} )
    then fun (Heq : true = true -> i = j) _ => left _ (Heq (eq_refl true))
    else fun _ (Hdiff : false = false -> i <> j) => right _ (Hdiff (eq_refl false)))
  (eqb_correct i j)
  (eqb_false_correct i j).

Lemma eq_dec : forall i j:int, i = j \/ i <> j.
Proof.
 intros i j;destruct (eqs i j);auto.
Qed.

(* Extra function on equality *)

Definition cast i j :=
     (if i =? j as b return ((b = true -> i = j) -> option (forall P : int -> Type, P i -> P j))
      then fun Heq : true = true -> i = j =>
             Some
             (fun (P : int -> Type) (Hi : P i) =>
               match Heq (eq_refl true) in (_ = y) return (P y) with
               | eq_refl => Hi
               end)
      else fun _ : false = true -> i = j => None) (eqb_correct i j).

Lemma cast_refl : forall i, cast i i = Some (fun P H => H).
Proof.
 unfold cast;intros i.
 generalize (eqb_correct i i).
 rewrite Uint63Axioms.eqb_refl;intros e.
 rewrite (Eqdep_dec.eq_proofs_unicity eq_dec (e (eq_refl true)) (eq_refl i));trivial.
Qed.

Lemma cast_diff : forall i j, i =? j = false -> cast i j = None.
Proof.
 intros i j H;unfold cast;intros; generalize (eqb_correct i j).
 rewrite H;trivial.
Qed.

Definition eqo i j :=
   (if i =? j as b return ((b = true -> i = j) -> option (i=j))
    then fun Heq : true = true -> i = j =>
             Some (Heq (eq_refl true))
     else fun _ : false = true -> i = j => None) (eqb_correct i j).

Lemma eqo_refl : forall i, eqo i i = Some (eq_refl i).
Proof.
 unfold eqo;intros i.
 generalize (eqb_correct i i).
 rewrite Uint63Axioms.eqb_refl;intros e.
 rewrite (Eqdep_dec.eq_proofs_unicity eq_dec (e (eq_refl true)) (eq_refl i));trivial.
Qed.

Lemma eqo_diff : forall i j, i =? j = false -> eqo i j = None.
Proof.
 unfold eqo;intros i j H; generalize (eqb_correct i j).
 rewrite H;trivial.
Qed.

(** Comparison *)

Lemma eqbP x y : reflect (φ  x  = φ  y ) (x =? y).
Proof. apply iff_reflect; rewrite eqb_spec; split; [ apply to_Z_inj | apply f_equal ]. Qed.

Lemma ltbP x y : reflect (φ  x  < φ  y )%Z (x <? y).
Proof. apply iff_reflect; symmetry; apply Uint63Axioms.ltb_spec. Qed.

Lemma lebP x y : reflect (φ  x  <= φ  y )%Z (x ≤? y).
Proof. apply iff_reflect; symmetry; apply leb_spec. Qed.

Lemma compare_spec x y : compare x y = (φ x ?= φ y)%Z.
Proof.
  rewrite compare_def_spec; unfold compare_def.
  case ltbP; [ auto using Z.compare_lt_iff | intros hge ].
  case eqbP; [ now symmetry; apply Z.compare_eq_iff | intros hne ].
  symmetry; apply Z.compare_gt_iff; lia.
Qed.

Lemma is_zero_spec x : is_zero x = true <-> x = 0%uint63.
Proof. apply eqb_spec. Qed.

Lemma diveucl_spec x y :
  let (q,r) := diveucl x y in
  (φ  q , φ  r ) = Z.div_eucl φ  x  φ  y .
Proof.
 rewrite diveucl_def_spec; unfold diveucl_def; rewrite div_spec, mod_spec; unfold Z.div, Z.modulo.
 destruct (Z.div_eucl φ  x  φ  y ); trivial.
Qed.

Local Open Scope Z_scope.
(** Addition *)
Lemma addc_spec x y : [+| x +c y |] = φ  x  + φ  y .
Proof.
  rewrite addc_def_spec; unfold addc_def, interp_carry.
  pose proof (to_Z_bounded x); pose proof (to_Z_bounded y).
  case ltbP; rewrite add_spec.
  - case (Z_lt_ge_dec (φ  x  + φ  y ) wB).
    + intros k; rewrite Zmod_small; lia.
    + intros hge; rewrite <- (Zmod_unique _ _ 1 (φ  x  + φ  y  - wB)); lia.
  - case (Z_lt_ge_dec (φ  x  + φ  y ) wB).
    + intros k; rewrite Zmod_small; lia.
    + intros hge; rewrite <- (Zmod_unique _ _ 1 (φ  x  + φ  y  - wB)); lia.
Qed.

Lemma succ_spec x : φ (succ x)  = (φ  x  + 1) mod wB.
Proof. apply add_spec. Qed.

Lemma succc_spec x : [+| succc x |] = φ  x  + 1.
Proof. apply addc_spec. Qed.

Lemma addcarry_spec x y : φ (addcarry x y)  = (φ  x  + φ  y  + 1) mod wB.
Proof. unfold addcarry; rewrite -> !add_spec, Zplus_mod_idemp_l; trivial. Qed.

Lemma addcarryc_spec x y : [+| addcarryc x y |] = φ  x  + φ  y  + 1.
Proof.
  rewrite addcarryc_def_spec; unfold addcarryc_def, interp_carry.
  pose proof (to_Z_bounded x); pose proof (to_Z_bounded y).
  case lebP; rewrite addcarry_spec.
  - case (Z_lt_ge_dec (φ  x  + φ  y  + 1) wB).
    + intros hlt; rewrite Zmod_small; lia.
    + intros hge; rewrite <- (Zmod_unique _ _ 1 (φ  x  + φ  y  + 1 - wB)); lia.
  - case (Z_lt_ge_dec (φ  x  + φ  y  + 1) wB).
    + intros hlt; rewrite Zmod_small; lia.
    + intros hge; rewrite <- (Zmod_unique _ _ 1 (φ  x  + φ  y  + 1 - wB)); lia.
Qed.

(** Subtraction *)
Lemma subc_spec x y : [-| x -c y |] = φ  x  - φ  y .
Proof.
  rewrite subc_def_spec; unfold subc_def; unfold interp_carry.
  pose proof (to_Z_bounded x); pose proof (to_Z_bounded y).
  case lebP.
  - intros hle; rewrite sub_spec, Z.mod_small; lia.
  - intros hgt; rewrite sub_spec, <- (Zmod_unique _ wB (-1) (φ  x  - φ  y  + wB)); lia.
Qed.

Lemma pred_spec x : φ (pred x) = (φ  x  - 1) mod wB.
Proof. apply sub_spec. Qed.

Lemma predc_spec x : [-| predc x |] = φ  x  - 1.
Proof. apply subc_spec. Qed.

Lemma oppc_spec x : [-| oppc x |] = - φ  x .
Proof. unfold oppc; rewrite -> subc_spec, to_Z_0; trivial. Qed.

Lemma opp_spec x : φ (- x) = - φ  x  mod wB.
Proof. unfold opp; rewrite -> sub_spec, to_Z_0; trivial. Qed.

Lemma oppcarry_spec x : φ (oppcarry x) = wB - φ  x  - 1.
Proof.
 unfold oppcarry; rewrite sub_spec.
 rewrite <- Zminus_plus_distr, Zplus_comm, Zminus_plus_distr.
 apply Zmod_small.
 generalize (to_Z_bounded x); auto with zarith.
Qed.

Lemma subcarry_spec x y : φ (subcarry x y) = (φ  x  - φ  y  - 1) mod wB.
Proof. unfold subcarry; rewrite !sub_spec, Zminus_mod_idemp_l; trivial. Qed.

Lemma subcarryc_spec x y : [-| subcarryc x y |] = φ  x  - φ  y  - 1.
Proof.
  rewrite subcarryc_def_spec; unfold subcarryc_def, interp_carry; fold (subcarry x y).
 pose proof (to_Z_bounded x); pose proof (to_Z_bounded y).
 case ltbP; rewrite subcarry_spec.
  - intros hlt; rewrite Zmod_small; lia.
  - intros hge; rewrite <- (Zmod_unique _ _ (-1) (φ  x  - φ  y  - 1 + wB)); lia.
Qed.

(** GCD *)
Lemma to_Z_gcd : forall i j, φ (gcd i j)  = Zgcdn (2 * size) (φ  j) (φ  i).
Proof.
 unfold gcd.
 elim (2*size)%nat.
 - reflexivity.
 - intros n ih i j; simpl.
   pose proof (to_Z_bounded j) as hj; pose proof (to_Z_bounded i).
   case eqbP; rewrite to_Z_0.
   + intros ->; rewrite Z.abs_eq; lia.
   + intros hne; rewrite ih; clear ih.
     rewrite <- mod_spec.
     revert hj hne; case φ  j ; intros; lia.
Qed.

Lemma gcd_spec a b : Zis_gcd (φ  a) (φ  b) (φ (gcd a b)).
Proof.
 rewrite to_Z_gcd.
 apply Zis_gcd_sym.
 apply Zgcdn_is_gcd.
 unfold Zgcd_bound.
 generalize (to_Z_bounded b).
 destruct φ b as [|p|p].
 - unfold size; auto with zarith.
 - intros (_,H).
   cut (Psize p <= size)%nat; [ lia | rewrite <- Zpower2_Psize; auto].
 - intros (H,_); compute in H; elim H; auto.
Qed.

(** Head0, Tail0 *)
Lemma head00_spec x : φ  x = 0 -> φ (head0 x) = φ  digits .
Proof. now intros h; rewrite (to_Z_inj _ 0 h). Qed.

Lemma tail00_spec x : φ  x = 0 -> φ (tail0 x) = φ digits.
Proof. now intros h; rewrite (to_Z_inj _ 0 h). Qed.

Infix "≡" := (eqm wB) (at level 70, no associativity) : uint63_scope.

Lemma eqm_mod x y : x mod wB ≡ y mod wB → x ≡ y.
Proof.
  intros h.
  eapply (eqm_trans).
  - apply eqm_sym; apply Zmod_eqm.
  - apply (eqm_trans _ _ _ _ h).
    apply Zmod_eqm.
Qed.

Lemma eqm_sub x y : x ≡ y → x - y ≡ 0.
Proof. intros h; unfold eqm; rewrite Zminus_mod, h, Z.sub_diag; reflexivity. Qed.

Lemma eqmE x y : x ≡ y → ∃ k, x - y = k * wB.
Proof. intros h%Z.cong_iff_ex; trivial. Qed.

Lemma eqm_subE x y : x ≡ y ↔ x - y ≡ 0.
Proof.
  split.
  - apply eqm_sub.
  - intros h; case (eqmE _ _ h); clear h; intros q h.
    assert (y = x - q * wB) by lia.
    clear h; subst y.
    unfold eqm; rewrite Zminus_mod, Z_mod_mult, Z.sub_0_r, Zmod_mod; reflexivity.
Qed.

Lemma int_eqm x y : x = y → φ x ≡ φ y.
Proof. unfold eqm; intros ->; reflexivity. Qed.

Lemma eqmI x y : φ x ≡ φ y → x = y.
Proof.
  unfold eqm.
  repeat rewrite Zmod_small by apply to_Z_bounded.
  apply to_Z_inj.
Qed.

(* ADD *)
Lemma add_assoc x y z: (x + (y + z) = (x + y) + z)%uint63.
Proof.
 apply to_Z_inj; rewrite !add_spec.
 rewrite -> Zplus_mod_idemp_l, Zplus_mod_idemp_r, Zplus_assoc; auto.
Qed.

Lemma add_comm x y: (x + y = y + x)%uint63.
Proof.
 apply to_Z_inj; rewrite -> !add_spec, Zplus_comm; auto.
Qed.

Lemma add_le_r m n:
  if  (n <=? m + n)%uint63 then  (φ m + φ n < wB)%Z else  (wB <= φ m + φ n)%Z.
Proof.
 case (to_Z_bounded m); intros H1m H2m.
 case (to_Z_bounded n); intros H1n H2n.
 case (Zle_or_lt wB (φ m + φ n)); intros H.
 - assert (H1: (φ (m + n) = φ m + φ n - wB)%Z). {
     rewrite add_spec.
     replace ((φ m + φ n) mod wB)%Z with ((((φ m + φ n) - wB) + wB) mod wB)%Z.
     - rewrite -> Zplus_mod, Z_mod_same_full, Zplus_0_r, !Zmod_small; auto with zarith.
       rewrite !Zmod_small; auto with zarith.
     - apply (f_equal2 Z.modulo); auto with zarith.
   }
   case_eq (n <=? m + n)%uint63; auto.
   rewrite leb_spec, H1; auto with zarith.
 - assert (H1: (φ (m + n)  = φ m + φ n)%Z).
   { rewrite add_spec, Zmod_small; auto with zarith. }
   replace (n <=? m + n)%uint63 with true; auto.
   apply sym_equal; rewrite leb_spec, H1; auto with zarith.
Qed.

Lemma add_cancel_l x y z : (x + y = x + z)%uint63 -> y = z.
Proof.
  intros h; apply int_eqm in h; rewrite !add_spec in h; apply eqm_mod, eqm_sub in h.
  replace (_ + _ - _) with (φ(y) - φ(z)) in h by lia.
  rewrite <- eqm_subE in h.
  apply eqmI, h.
Qed.

Lemma add_cancel_r x y z : (y + x = z + x)%uint63 -> y = z.
Proof.
  rewrite !(fun t => add_comm t x); intros Hl; apply (add_cancel_l x); auto.
Qed.

Coercion b2i (b: bool) : int := if b then 1%uint63 else 0%uint63.

(* LSR *)
Lemma lsr0 i : 0 >> i = 0%uint63.
Proof. apply to_Z_inj; rewrite lsr_spec; reflexivity. Qed.

Lemma lsr_0_r i: i >> 0 = i.
Proof. apply to_Z_inj; rewrite lsr_spec, Zdiv_1_r; exact eq_refl. Qed.

Lemma lsr_1 n : 1 >> n = (n =? 0)%uint63.
Proof.
  case eqbP.
  - intros h; rewrite (to_Z_inj _ _ h), lsr_0_r; reflexivity.
  - intros Hn.
    assert (H1n : (1 >> n = 0)%uint63); auto.
    apply to_Z_inj; rewrite lsr_spec.
    apply Zdiv_small; rewrite to_Z_1; split; auto with zarith.
    change 1%Z with (2^0)%Z.
    apply Zpower_lt_monotone; split; auto with zarith.
    rewrite to_Z_0 in Hn.
    generalize (to_Z_bounded n).
    lia.
Qed.

Lemma lsr_add i m n: ((i >> m) >> n = if n <=? m + n then i >> (m + n) else 0)%uint63.
Proof.
 case (to_Z_bounded m); intros H1m H2m.
 case (to_Z_bounded n); intros H1n H2n.
 case (to_Z_bounded i); intros H1i H2i.
 generalize (add_le_r m n); case (n <=? m + n)%uint63; intros H.
 - apply to_Z_inj; rewrite -> !lsr_spec, Zdiv_Zdiv, <- Zpower_exp; auto with zarith.
   rewrite add_spec, Zmod_small; auto with zarith.
 - apply to_Z_inj; rewrite -> !lsr_spec, Zdiv_Zdiv, <- Zpower_exp; auto with zarith.
   apply Zdiv_small. split; [ auto with zarith | ].
   eapply Z.lt_le_trans; [ | apply Zpower2_le_lin ]; auto with zarith.
Qed.

(* LSL *)
Lemma lsl0 i: 0 << i = 0%uint63.
Proof.
 apply to_Z_inj.
 generalize (lsl_spec 0 i).
 rewrite to_Z_0, Zmult_0_l, Zmod_0_l; auto.
Qed.

Lemma lsl0_r i : i << 0 = i.
Proof.
 apply to_Z_inj.
 rewrite -> lsl_spec, to_Z_0, Z.mul_1_r.
 apply Zmod_small; apply (to_Z_bounded i).
Qed.

Lemma lsl_add_distr x y n: (x + y) << n = ((x << n) + (y << n))%uint63.
Proof.
 apply to_Z_inj; rewrite -> !lsl_spec, !add_spec, Zmult_mod_idemp_l.
 rewrite -> !lsl_spec, <-Zplus_mod.
 apply (f_equal2 Z.modulo); auto with zarith.
Qed.

Lemma lsr_M_r x i (H: (digits <=? i = true)%uint63) : x >> i = 0%uint63.
Proof.
 apply to_Z_inj.
 rewrite lsr_spec, to_Z_0.
 case (to_Z_bounded x); intros H1x H2x.
 case (to_Z_bounded digits); intros H1d H2d.
 rewrite -> leb_spec in H.
 apply Zdiv_small; split; [ auto | ].
 apply (Z.lt_le_trans _ _ _ H2x).
 unfold wB; change (Z_of_nat size) with φ digits.
 apply Zpower_le_monotone; auto with zarith.
Qed.

(* BIT *)
Lemma bit_0_spec i: φ (bit i 0) = φ i mod 2.
Proof.
 unfold bit, is_zero. rewrite lsr_0_r.
 assert (Hbi: (φ i mod 2 < 2)%Z).
 { apply Z_mod_lt; auto with zarith. }
 case (to_Z_bounded i); intros H1i H2i.
 case (Z.mod_bound_pos_le (φ i) 2); auto with zarith; intros H3i H4i.
 assert (H2b: (0 < 2 ^ φ (digits - 1))%Z). {
   apply Zpower_gt_0; auto with zarith.
   case (to_Z_bounded (digits -1)); auto with zarith.
 }
 assert (H: φ (i << (digits -1)) = (φ i mod 2 * 2^ φ (digits -1))%Z). {
   rewrite lsl_spec.
   rewrite -> (Z_div_mod_eq_full φ i 2) at 1.
   rewrite -> Zmult_plus_distr_l, <-Zplus_mod_idemp_l.
   rewrite -> (Zmult_comm 2), <-Zmult_assoc.
   replace (2 * 2 ^ φ (digits - 1))%Z with wB; auto.
   rewrite Z_mod_mult, Zplus_0_l; apply Zmod_small.
   split; auto with zarith.
   replace wB with (2 * 2 ^ φ (digits -1))%Z; auto.
   apply Zmult_lt_compat_r; auto with zarith.
 }
 case (Zle_lt_or_eq 0 (φ i mod 2)); auto with zarith; intros Hi.
 2: generalize H; rewrite <-Hi, Zmult_0_l.
 2: replace 0%Z with φ 0; auto.
 2: now case eqbP.
 generalize H; replace (φ i mod 2) with 1%Z; auto with zarith.
 rewrite Zmult_1_l.
 intros H1.
 assert (H2: φ (i << (digits - 1)) <> φ 0).
 { replace φ 0 with 0%Z; auto with zarith. }
 now case eqbP.
Qed.

Lemma bit_split i : ( i = (i >> 1 ) << 1 + bit i 0)%uint63.
Proof.
 apply to_Z_inj.
 rewrite -> add_spec, lsl_spec, lsr_spec, bit_0_spec, Zplus_mod_idemp_l.
 replace (2 ^ φ 1) with 2%Z; auto with zarith.
 rewrite -> Zmult_comm, <-Z_div_mod_eq_full.
 rewrite Zmod_small; auto; case (to_Z_bounded i); auto.
Qed.

Lemma bit_lsr x i j :
 (bit (x >> i) j = if j <=? i + j then bit x (i + j) else false)%uint63.
Proof.
  unfold bit; rewrite lsr_add; case (_ ≤? _); auto.
Qed.

Lemma bit_b2i (b: bool) i : bit b i = (i =? 0)%uint63 && b.
Proof.
 case b; unfold bit; simpl b2i.
 - rewrite lsr_1; case (i =? 0)%uint63; auto.
 - rewrite lsr0, lsl0, andb_false_r; auto.
Qed.

Lemma bit_1 n : bit 1 n = (n =? 0)%uint63.
Proof.
 unfold bit; rewrite lsr_1.
 case (_ =? _)%uint63; simpl; auto.
Qed.

Local Hint Resolve Z.lt_gt Z.div_pos : zarith.

Lemma to_Z_split x : φ x = φ (x  >> 1) * 2 + φ (bit x 0).
Proof.
  case (to_Z_bounded x); intros H1x H2x.
  case (to_Z_bounded (bit x 0)); intros H1b H2b.
  assert (F1: 0 <= φ (x >> 1) < wB/2). {
    rewrite -> lsr_spec, to_Z_1, Z.pow_1_r. split; auto with zarith.
    apply Zdiv_lt_upper_bound; auto with zarith.
  }
  rewrite -> (bit_split x) at 1.
  rewrite -> add_spec, Zmod_small, lsl_spec, to_Z_1, Z.pow_1_r, Zmod_small;
    split; auto with zarith.
  - change wB with ((wB/2)*2); auto with zarith.
  - rewrite -> lsl_spec, to_Z_1, Z.pow_1_r, Zmod_small; auto with zarith.
    change wB with ((wB/2)*2); auto with zarith.
  - rewrite -> lsl_spec, to_Z_1, Z.pow_1_r, Zmod_small; auto with zarith.
    2: change wB with ((wB/2)*2); auto with zarith.
    change wB with (((wB/2 - 1) * 2 + 1) + 1).
    assert (φ (bit x 0) <= 1); auto with zarith.
    case bit; discriminate.
Qed.

Lemma bit_M i n (H: (digits <=? n = true)%uint63): bit i n = false.
Proof. unfold bit; rewrite lsr_M_r; auto. Qed.

Lemma bit_half i n (H: (n <? digits = true)%uint63) : bit (i>>1) n = bit i (n+1).
Proof.
 unfold bit.
 rewrite lsr_add.
 case_eq (n <=? (1 + n))%uint63.
 - replace (1+n)%uint63 with (n+1)%uint63; [auto|idtac].
   apply to_Z_inj; rewrite !add_spec, Zplus_comm; auto.
 - intros H1; assert (H2: n = max_int).
   2: generalize H; rewrite H2; discriminate.
   case (to_Z_bounded n); intros H1n H2n.
   case (Zle_lt_or_eq φ n (wB - 1)); auto with zarith;
     intros H2; apply to_Z_inj; auto.
   generalize (add_le_r 1 n); rewrite H1.
   change φ max_int with (wB - 1)%Z.
   replace φ 1 with 1%Z; auto with zarith.
Qed.

Lemma bit_ext i j : (forall n, bit i n = bit j n) -> i = j.
Proof.
  case (to_Z_bounded j); case (to_Z_bounded i).
  unfold wB; revert i j; elim size.
  - simpl; intros i j ???? _; apply to_Z_inj; lia.
  - intros n ih i j.
    rewrite Nat2Z.inj_succ, Z.pow_succ_r by auto with zarith.
    intros hi1 hi2 hj1 hj2 hext.
    rewrite (bit_split i), (bit_split j), hext.
    do 2 f_equal; apply ih; clear ih.
    1, 3: apply to_Z_bounded.
    1, 2: now rewrite lsr_spec; apply Z.div_lt_upper_bound.
    intros b.
    case (Zle_or_lt φ digits φ b).
    + rewrite <- leb_spec; intros; rewrite !bit_M; auto.
    + rewrite <- ltb_spec; intros; rewrite !bit_half; auto.
Qed.

Lemma bit_lsl x i j : bit (x << i) j =
                        (if (j <? i) || (digits <=? j) then false else bit x (j - i))%uint63.
Proof.
  assert (F1: 1 >= 0) by discriminate.
  case_eq (digits <=? j)%uint63; intros H.
  - rewrite orb_true_r, bit_M; auto.
  - set (d := φ digits).
    case (Zle_or_lt d (φ j)); intros H1.
    1:case (leb_spec digits j); rewrite H; auto with zarith.
    1:intros _ HH; generalize (HH H1); discriminate.
    clear H.
    generalize (ltb_spec j i); case ltb; intros H2; unfold bit; simpl.
    + change 62%uint63 with (digits - 1)%uint63.
      assert (F2: (φ j < φ i)%Z) by (case H2; auto); clear H2.
      replace (is_zero (((x << i) >> j) << (digits - 1))) with true; auto.
      case (to_Z_bounded j); intros  H1j H2j.
      apply sym_equal; rewrite is_zero_spec; apply to_Z_inj.
      rewrite lsl_spec, lsr_spec, lsl_spec.
      replace wB with (2^d); auto.
      pattern d at 1; replace d with ((d - (φ j + 1)) + (φ j + 1))%Z by ring.
      rewrite Zpower_exp; auto with zarith.
      replace φ i with ((φ i - (φ j + 1)) + (φ j + 1))%Z by ring.
      rewrite -> Zpower_exp, Zmult_assoc; auto with zarith.
      rewrite Zmult_mod_distr_r.
      rewrite -> Zplus_comm, Zpower_exp, !Zmult_assoc; auto with zarith.
      rewrite -> Z_div_mult_full; auto with zarith.
      rewrite <-Zmult_assoc, <-Zpower_exp; auto with zarith.
      replace (1 + φ digits - 1)%Z with d; auto with zarith.
      rewrite Z_mod_mult; auto.
    + case H2; intros _ H3; case (Zle_or_lt φ i φ j); intros F2.
      2: generalize (H3 F2); discriminate.
      clear H2 H3.
      apply (f_equal negb).
      apply (f_equal is_zero).
      apply to_Z_inj.
      rewrite -> !lsl_spec, !lsr_spec, !lsl_spec.
      pattern wB at 2 3; replace wB with (2^(1+ φ (digits - 1))); auto.
      rewrite -> Zpower_exp, Z.pow_1_r; auto with zarith.
      rewrite !Zmult_mod_distr_r.
      apply (f_equal2 Zmult); auto.
      replace wB with (2^ d); auto with zarith.
      replace d with ((d - φ i) + φ i)%Z by ring.
      case (to_Z_bounded i); intros  H1i H2i.
      rewrite Zpower_exp; auto with zarith.
      rewrite Zmult_mod_distr_r.
      case (to_Z_bounded j); intros  H1j H2j.
      replace φ (j - i) with (φ j - φ i)%Z.
      2: rewrite sub_spec, Zmod_small; auto with zarith.
      set (d1 := (d - φ i)%Z).
      set (d2 := (φ j - φ i)%Z).
      pattern φ j at 1;
        replace φ j with (d2 + φ i)%Z.
      2: unfold d2; ring.
      rewrite -> Zpower_exp; auto with zarith.
      rewrite -> Zdiv_mult_cancel_r.
      2: generalize (Zpower2_lt_lin φ  i  H1i); auto with zarith.
      rewrite -> (Z_div_mod_eq_full φ x (2^d1)) at 2.
      pattern d1 at 2;
        replace d1 with (d2 + (1+ (d - φ j - 1)))%Z
        by (unfold d1, d2; ring).
      rewrite Zpower_exp; auto with zarith.
      rewrite <-Zmult_assoc, Zmult_comm.
      rewrite Zdiv.Z_div_plus_full_l; auto with zarith.
      rewrite Zpower_exp, Z.pow_1_r; auto with zarith.
      rewrite <-Zplus_mod_idemp_l.
      rewrite <-!Zmult_assoc, Zmult_comm, Z_mod_mult, Zplus_0_l; auto.
Qed.

(* LOR *)
Lemma lor_lsr i1 i2 i: (i1 lor i2) >> i = (i1 >> i) lor (i2 >> i).
Proof.
 apply bit_ext; intros n.
 rewrite -> lor_spec, !bit_lsr, lor_spec.
 case (_ <=? _)%uint63; auto.
Qed.

Lemma lor_le x y : (y <=? x lor y)%uint63 = true.
Proof.
 generalize x y (to_Z_bounded x) (to_Z_bounded y); clear x y.
 unfold wB; elim size.
 - replace (2^Z_of_nat 0) with 1%Z; auto with zarith.
   intros x y Hx Hy; replace x with 0%uint63.
   + replace y with 0%uint63; auto.
     apply to_Z_inj; rewrite to_Z_0; auto with zarith.
   + apply to_Z_inj; rewrite to_Z_0; auto with zarith.
 - intros n IH x y; rewrite inj_S.
   unfold Z.succ; rewrite -> Zpower_exp, Z.pow_1_r; auto with zarith.
   intros Hx Hy.
   rewrite leb_spec.
   rewrite -> (to_Z_split y) at 1; rewrite (to_Z_split (x lor y)).
   assert (φ (y>>1) <= φ ((x lor y) >> 1)).
   + rewrite -> lor_lsr, <-leb_spec; apply IH.
     * rewrite -> lsr_spec, to_Z_1, Z.pow_1_r; split; auto with zarith.
       apply Zdiv_lt_upper_bound; auto with zarith.
     * rewrite -> lsr_spec, to_Z_1, Z.pow_1_r; split; auto with zarith.
       apply Zdiv_lt_upper_bound; auto with zarith.
   + assert (φ (bit y 0) <= φ (bit (x lor y) 0)); auto with zarith.
     rewrite lor_spec; do 2 case bit; try discriminate.
Qed.

Lemma bit_0 n : bit 0 n = false.
Proof. unfold bit; rewrite lsr0; auto. Qed.

Lemma bit_add_or x y:
  (forall n, bit x n = true -> bit y n = true -> False) <-> (x + y)%uint63= x lor y.
Proof.
 generalize x y (to_Z_bounded x) (to_Z_bounded y); clear x y.
 unfold wB; elim size.
 - replace (2^Z_of_nat 0) with 1%Z; auto with zarith.
   intros x y Hx Hy; replace x with 0%uint63.
   + replace y with 0%uint63.
     { split; auto; intros _ n; rewrite !bit_0; discriminate. }
     apply to_Z_inj; rewrite to_Z_0; auto with zarith.
   + apply to_Z_inj; rewrite to_Z_0; auto with zarith.
 - intros n IH x y; rewrite inj_S.
   unfold Z.succ; rewrite Zpower_exp, Z.pow_1_r; auto with zarith.
   intros Hx Hy.
   split.
   + intros Hn.
     assert (F1: ((x >> 1) + (y >> 1))%uint63 = (x >> 1) lor (y >> 1)). {
       apply IH.
       - rewrite lsr_spec, Z.pow_1_r; split; auto with zarith.
         apply Zdiv_lt_upper_bound; auto with zarith.
       - rewrite lsr_spec, Z.pow_1_r; split; auto with zarith.
         apply Zdiv_lt_upper_bound; auto with zarith.
       - intros m H1 H2.
         case_eq (digits <=? m)%uint63;  [idtac | rewrite <- not_true_iff_false];
           intros Heq.
         + rewrite bit_M in H1; auto; discriminate.
         + rewrite leb_spec in Heq.
           apply (Hn (m + 1)%uint63);
             rewrite <-bit_half; auto; rewrite ltb_spec; auto with zarith.
     }
     rewrite (bit_split (x lor y)), lor_lsr, <- F1, lor_spec.
     replace (b2i (bit x 0 || bit y 0)) with (bit x 0 + bit y 0)%uint63.
     2: generalize (Hn 0%uint63); do 2 case bit; auto; intros [ ]; auto.
     rewrite lsl_add_distr.
     rewrite (bit_split x) at 1; rewrite (bit_split y) at 1.
     rewrite <-!add_assoc; apply (f_equal2 add); auto.
     rewrite add_comm, <-!add_assoc; apply (f_equal2 add); auto.
     rewrite add_comm; auto.
   + intros Heq.
     generalize (add_le_r x y); rewrite Heq, lor_le; intro Hb.
     generalize Heq; rewrite (bit_split x) at 1; rewrite (bit_split y )at 1; clear Heq.
     rewrite (fun y => add_comm y (bit x 0)), <-!add_assoc, add_comm,
       <-!add_assoc, (add_comm (bit y 0)), add_assoc, <-lsl_add_distr.
     rewrite (bit_split (x lor y)), lor_spec.
     intros Heq.
     assert (F: (bit x 0 + bit y 0)%uint63 = (bit x 0 || bit y 0)). {
       assert (F1: (2 | wB)) by (apply Zpower_divide; apply refl_equal).
       assert (F2: 0 < wB) by (apply refl_equal).
       assert (F3: φ (bit x 0 + bit y 0) mod 2 = φ (bit x 0 || bit y 0) mod 2). {
         apply trans_equal with ((φ ((x>>1 + y>>1) << 1) + φ (bit x 0 + bit y 0)) mod 2).
         - rewrite lsl_spec, Zplus_mod, Z.mod_mod_divide; auto with zarith.
           rewrite Z.pow_1_r, Z_mod_mult, Zplus_0_l, Zmod_mod; auto with zarith.
         - assert (forall a, a mod 2 = (a mod wB) mod 2) as ->.
           { intros. rewrite Z.mod_mod_divide; trivial. }
           rewrite <-add_spec, Heq; auto with zarith.
           rewrite add_spec, Z.mod_mod_divide; auto with zarith.
           rewrite lsl_spec, Zplus_mod, Z.mod_mod_divide; auto with zarith.
           rewrite Z.pow_1_r, Z_mod_mult, Zplus_0_l, Zmod_mod; auto with zarith.
       }
       generalize F3; do 2 case bit; try discriminate; auto.
     }
     case (IH (x >> 1) (y >> 1)).
     * rewrite lsr_spec, to_Z_1, Z.pow_1_r; split; auto with zarith.
       apply Zdiv_lt_upper_bound; auto with zarith.
     * rewrite lsr_spec, to_Z_1, Z.pow_1_r; split; auto with zarith.
       apply Zdiv_lt_upper_bound; auto with zarith.
     * intros _ HH m; case (to_Z_bounded m); intros H1m H2m.
       case_eq (digits <=? m)%uint63.
       -- intros Hlm; rewrite bit_M; auto; discriminate.
       -- rewrite <- not_true_iff_false, leb_spec; intros Hlm.
          case (Zle_lt_or_eq 0 φ m); auto; intros Hm.
          ++ replace m with ((m -1) + 1)%uint63. {
               rewrite <-(bit_half x), <-(bit_half y); auto with zarith.
               - apply HH.
                 rewrite <-lor_lsr.
                 assert (0 <= φ (bit (x lor y) 0) <= 1) by (case bit; split; discriminate).
                 rewrite F in Heq; generalize (add_cancel_r _ _ _ Heq).
                 intros Heq1; apply to_Z_inj.
                 generalize (f_equal to_Z Heq1); rewrite lsl_spec, to_Z_1, Z.pow_1_r, Zmod_small.
                 + rewrite lsl_spec, to_Z_1, Z.pow_1_r, Zmod_small; auto with zarith.
                   case (to_Z_bounded (x lor y)); intros H1xy H2xy.
                   rewrite lsr_spec, to_Z_1, Z.pow_1_r; auto with zarith.
                   change wB with ((wB/2)*2); split; auto with zarith.
                   assert (φ (x lor y) / 2  < wB / 2); auto with zarith.
                   apply Zdiv_lt_upper_bound; auto with zarith.
                 + split.
                   * case (to_Z_bounded (x >> 1 + y >> 1)); auto with zarith.
                   * rewrite add_spec.
                     apply Z.le_lt_trans with ((φ (x >> 1) + φ (y >> 1)) * 2); auto with zarith.
                     -- case (Z.mod_bound_pos_le (φ (x >> 1) + φ (y >> 1)) wB); auto with zarith.
                        case (to_Z_bounded (x >> 1)); case (to_Z_bounded (y >> 1)); auto with zarith.
                     -- generalize Hb; rewrite (to_Z_split x) at 1; rewrite (to_Z_split y) at 1.
                        case (to_Z_bounded (bit x 0)); case (to_Z_bounded (bit y 0)); auto with zarith.
               - rewrite ltb_spec, sub_spec, to_Z_1, Zmod_small; auto with zarith.
               - rewrite ltb_spec, sub_spec, to_Z_1, Zmod_small; auto with zarith.
             }
             apply to_Z_inj.
             rewrite add_spec, sub_spec, Zplus_mod_idemp_l, to_Z_1, Zmod_small; auto with zarith.
          ++ pose proof (to_Z_inj 0 _ Hm); clear Hm; subst m.
             intros hx hy; revert F; rewrite hx, hy; intros F.
             generalize (f_equal to_Z F). vm_compute. lia.
Qed.

Lemma addmuldiv_spec x y p :
  φ p <= φ digits  ->
  φ (addmuldiv p x y)  = (φ x * (2 ^ φ p) + φ y / (2 ^ (φ digits - φ  p))) mod wB.
Proof.
 intros H.
 assert (Fp := to_Z_bounded p); assert (Fd := to_Z_bounded digits).
 rewrite addmuldiv_def_spec; unfold addmuldiv_def.
 case (bit_add_or (x << p) (y >> (digits - p))); intros HH _.
 rewrite <-HH, add_spec, lsl_spec, lsr_spec, Zplus_mod_idemp_l, sub_spec.
 - rewrite (fun x y => Zmod_small (x - y)); auto with zarith.
 - intros n; rewrite -> bit_lsl, bit_lsr.
   generalize (add_le_r (digits - p) n).
   case (_ ≤? _); try discriminate.
   rewrite -> sub_spec, Zmod_small; auto with zarith; intros H1.
   case_eq (n <? p)%uint63; try discriminate.
   rewrite <- not_true_iff_false, ltb_spec; intros H2.
   case (_ ≤? _); try discriminate.
   intros _; rewrite bit_M; try discriminate.
   rewrite -> leb_spec, add_spec, Zmod_small, sub_spec, Zmod_small; auto with zarith.
   rewrite -> sub_spec, Zmod_small; auto with zarith.
Qed.

(* is_even *)
Lemma is_even_bit i : is_even i = negb (bit i 0).
Proof.
 unfold is_even.
 replace (i land 1) with (b2i (bit i 0)).
 - case bit; auto.
 - apply bit_ext; intros n.
   rewrite bit_b2i, land_spec, bit_1.
   generalize (eqb_spec n 0).
   case (n =? 0)%uint63; auto.
   + intros(H,_); rewrite andb_true_r, H; auto.
   + rewrite andb_false_r; auto.
Qed.

Lemma is_even_spec x : if is_even x then φ x mod 2 = 0 else φ x mod 2 = 1.
Proof.
rewrite is_even_bit.
generalize (bit_0_spec x); case bit; simpl; auto.
Qed.

Lemma is_even_0 : is_even 0 = true.
Proof. apply refl_equal. Qed.

Lemma is_even_lsl_1 i : is_even (i << 1) = true.
Proof.
 rewrite is_even_bit, bit_lsl; auto.
Qed.

(* Sqrt *)

 (* Direct transcription of an old proof
     of a fortran program in boyer-moore *)

Ltac elim_div :=
  unfold Z.div, Z.modulo;
  match goal with
  |  H : context[ Z.div_eucl ?X ?Y ] |-  _ =>
     generalize dependent H; generalize (Z_div_mod_full X Y) ; case (Z.div_eucl X Y)
  |  |-  context[ Z.div_eucl ?X ?Y ] =>
     generalize (Z_div_mod_full X Y) ; case (Z.div_eucl X Y)
  end; unfold Remainder.

Lemma quotient_by_2 a: a - 1 <= (a/2) + (a/2).
Proof.
 case (Z_mod_lt a 2); auto with zarith.
 intros H1; rewrite Zmod_eq_full; auto with zarith.
Qed.

Lemma sqrt_main_trick j k: 0 <= j -> 0 <= k ->
   (j * k) + j <= ((j + k)/2 + 1)  ^ 2.
Proof.
 intros Hj; generalize Hj k; pattern j; apply natlike_ind;
   auto; clear k j Hj.
 - intros _ k Hk; repeat rewrite Zplus_0_l.
   apply  Zmult_le_0_compat; generalize (Z_div_pos k 2); auto with zarith.
 - intros j Hj Hrec _ k Hk; pattern k; apply natlike_ind; auto; clear k Hk.
   + rewrite -> Zmult_0_r, Zplus_0_r, Zplus_0_l.
     generalize (sqr_pos (Z.succ j / 2)) (quotient_by_2 (Z.succ j));
       unfold Z.succ.
     rewrite Z.pow_2_r, Zmult_plus_distr_l; repeat rewrite Zmult_plus_distr_r.
     auto with zarith.
   + intros k Hk _.
     replace ((Z.succ j + Z.succ k) / 2) with ((j + k)/2 + 1).
     * generalize (Hrec Hj k Hk) (quotient_by_2 (j + k)).
       unfold Z.succ; repeat rewrite Z.pow_2_r;
         repeat rewrite Zmult_plus_distr_l; repeat rewrite Zmult_plus_distr_r.
       repeat rewrite Zmult_1_l; repeat rewrite Zmult_1_r.
       auto with zarith.
     * rewrite -> Zplus_comm, <- Z_div_plus_full_l; auto with zarith.
       apply f_equal2; auto with zarith.
Qed.

Lemma sqrt_main i j: 0 <= i -> 0 < j -> i < ((j + (i/j))/2 + 1) ^ 2.
Proof.
 intros Hi Hj.
 assert (Hij: 0 <= i/j) by (apply Z_div_pos; auto with zarith).
 refine (Z.lt_le_trans _ _ _ _ (sqrt_main_trick _ _ (Zlt_le_weak _ _ Hj) Hij)).
 pattern i at 1; rewrite -> (Z_div_mod_eq_full i j); case (Z_mod_lt i j); auto with zarith.
Qed.

Lemma sqrt_test_false i j: 0 <= i -> 0 < j -> i/j < j ->  (j + (i/j))/2 < j.
Proof.
  intros Hi Hj; elim_div; intros q r [ ? hr ]; [ lia | subst i ].
  elim_div; intros a b [ h [ hb | ] ]; lia.
Qed.

Lemma sqrt_test_true i j: 0 <= i -> 0 < j -> i/j >= j -> j ^ 2 <= i.
Proof.
 intros Hi Hj Hd; rewrite Z.pow_2_r.
 apply Z.le_trans with (j * (i/j)); auto with zarith.
 apply Z_mult_div_ge; auto with zarith.
Qed.

Lemma sqrt_step_correct rec i j:
  0 < φ i -> 0 < φ j -> φ i < (φ j + 1) ^ 2 ->
   2 * φ j < wB ->
  (forall j1 : int,
    0 < φ j1 < φ j -> φ i < (φ j1 + 1) ^ 2 ->
    φ (rec i j1) ^ 2 <= φ i < (φ (rec i j1) + 1) ^ 2) ->
  φ (sqrt_step rec i j) ^ 2 <= φ i < (φ (sqrt_step rec i j) + 1) ^ 2.
Proof.
 assert (Hp2: 0 < φ 2) by exact (refl_equal Lt).
 intros Hi Hj Hij H31 Hrec.
 unfold sqrt_step.
 case ltbP; rewrite div_spec.
 - intros hlt.
   assert (φ (j + i / j) = φ j + φ i/φ j) as hj.
   { rewrite add_spec, Zmod_small;rewrite div_spec; auto with zarith. }
   apply Hrec; rewrite lsr_spec, hj, to_Z_1; change (2 ^ 1) with 2.
   + split; [ | apply sqrt_test_false;auto with zarith].
     replace (φ j + φ i/φ j) with (1 * 2 + ((φ j - 2) + φ i / φ j)) by ring.
     rewrite Z_div_plus_full_l; auto with zarith.
     assert (0 <= φ i/ φ j) by (apply Z_div_pos; auto with zarith).
     assert (0 <= (φ j - 2 + φ i / φ j) / 2) ; auto with zarith.
     apply Z.div_pos; [ | lia ].
     case (Zle_lt_or_eq 1 φ j); auto with zarith; intros Hj1.
     rewrite <- Hj1, Zdiv_1_r; lia.
   + apply sqrt_main;auto with zarith.
 - split;[apply sqrt_test_true | ];auto with zarith.
Qed.

Lemma iter_sqrt_correct n rec i j: 0 < φ i -> 0 < φ j ->
  φ i < (φ j + 1) ^ 2 -> 2 * φ j < wB ->
  (forall j1, 0 < φ j1 -> 2^(Z_of_nat n) + φ j1 <= φ j ->
      φ i < (φ j1 + 1) ^ 2 -> 2 * φ j1 < wB ->
       φ (rec i j1) ^ 2 <= φ i < (φ (rec i j1) + 1) ^ 2) ->
  φ (iter_sqrt n rec i j) ^ 2 <= φ i < (φ (iter_sqrt n rec i j) + 1) ^ 2.
Proof.
 revert rec i j; elim n; unfold iter_sqrt; fold iter_sqrt; clear n.
 - intros rec i j Hi Hj Hij H31 Hrec; apply sqrt_step_correct. 1-4: lia.
   intros; apply Hrec; only 2: rewrite Zpower_0_r; auto with zarith.
 - intros n Hrec rec i j Hi Hj Hij H31 HHrec.
   apply sqrt_step_correct; auto.
   intros j1 Hj1  Hjp1; apply Hrec; auto with zarith.
   intros j2 Hj2 H2j2 Hjp2 Hj31; apply Hrec; auto with zarith.
   intros j3 Hj3 Hpj3.
   apply HHrec; auto.
   rewrite -> inj_S, Z.pow_succ_r.
   + apply Z.le_trans with (2 ^Z_of_nat n + φ j2); auto with zarith.
   + apply Zle_0_nat.
Qed.

Lemma sqrt_init i: 1 < i -> i < (i/2 + 1) ^ 2.
Proof.
 intros Hi.
 assert (H1: 0 <= i - 2) by auto with zarith.
 assert (H2: 1 <= (i / 2) ^ 2); auto with zarith. {
   replace i with (1* 2 + (i - 2)); auto with zarith.
   rewrite Z.pow_2_r, Z_div_plus_full_l; [|auto with zarith].
   generalize (sqr_pos ((i - 2)/ 2)) (Z_div_pos (i - 2) 2).
   rewrite Zmult_plus_distr_l; repeat rewrite Zmult_plus_distr_r.
   auto with zarith.
 }
 generalize (quotient_by_2 i).
 rewrite -> Z.pow_2_r in H2 |- *;
   repeat (rewrite Zmult_plus_distr_l ||
           rewrite Zmult_plus_distr_r ||
           rewrite Zmult_1_l || rewrite Zmult_1_r).
   auto with zarith.
Qed.

Lemma sqrt_spec : forall x,
       φ (sqrt x) ^ 2 <= φ x < (φ (sqrt x) + 1) ^ 2.
Proof.
 intros i; unfold sqrt.
 rewrite compare_spec. case Z.compare_spec; rewrite to_Z_1;
   intros Hi.
 - lia.
 - apply iter_sqrt_correct; auto with zarith;
     rewrite lsr_spec, to_Z_1; change (2^1) with 2;  auto with zarith.
   + replace φ i with (1 * 2 + (φ i - 2))%Z; try ring.
     assert (0 <= (φ i - 2)/2)%Z by (apply Z_div_pos; auto with zarith).
     rewrite Z_div_plus_full_l; auto with zarith.
   + apply sqrt_init; auto.
   + assert (W:= Z_mult_div_ge φ i 2);assert (W':= to_Z_bounded i);auto with zarith.
   + intros j2 H1 H2; contradict H2; apply Zlt_not_le.
     fold wB;assert (W:=to_Z_bounded i).
     apply Z.le_lt_trans with (φ i); auto with zarith.
     assert (0 <= φ i/2)%Z by (apply Z_div_pos; auto with zarith).
     apply Z.le_trans with (2 * (φ i/2)); auto with zarith.
     apply Z_mult_div_ge; auto with zarith.
 - case (to_Z_bounded i); repeat rewrite Z.pow_2_r; auto with zarith.
Qed.

(* sqrt2 *)
Lemma sqrt2_step_def rec ih il j:
   sqrt2_step rec ih il j =
   if (ih <? j)%uint63 then
    let quo := fst (diveucl_21 ih il j) in
    if (quo <? j)%uint63 then
     let m :=
      match j +c quo with
      | C0 m1 => m1 >> 1
      | C1 m1 => (m1 >> 1 + 1 << (digits -1))%uint63
      end in
     rec ih il m
    else j
   else j.
Proof.
 unfold sqrt2_step; case diveucl_21; intros i j';simpl.
 case (j +c i);trivial.
Qed.

Lemma sqrt2_lower_bound ih il j:
   Φ (WW ih il) < (φ j + 1) ^ 2 -> φ ih <= φ j.
Proof.
 intros H1.
 case (to_Z_bounded j); intros Hbj _.
 case (to_Z_bounded il); intros Hbil _.
 case (to_Z_bounded ih); intros Hbih Hbih1.
 assert ((φ ih < φ j + 1)%Z); auto with zarith.
 apply Zlt_square_simpl; auto with zarith.
 simpl zn2z_to_Z in H1.
 repeat rewrite <-Z.pow_2_r.
 refine (Z.le_lt_trans _ _ _ _ H1).
 apply Z.le_trans with (φ ih * wB)%Z;try rewrite Z.pow_2_r; auto with zarith.
Qed.

Lemma diveucl_21_spec_aux : forall a1 a2 b,
      wB/2 <= φ b ->
      φ a1 < φ b ->
      let (q,r) := diveucl_21 a1 a2 b in
      φ a1 *wB+ φ a2 = φ q * φ b + φ r /\
      0 <= φ r < φ b.
Proof.
 intros a1 a2 b H1 H2;assert (W:= diveucl_21_spec a1 a2 b).
 assert (W1:= to_Z_bounded a1).
 assert (W2:= to_Z_bounded a2).
 assert (Wb:= to_Z_bounded b).
 assert (φ b>0) as H by (auto with zarith).
 generalize (Z_div_mod (φ a1*wB+φ a2) φ b H).
 revert W.
 destruct (diveucl_21 a1 a2 b); destruct (Z.div_eucl (φ a1*wB+φ a2) φ b).
 intros (H', H''); auto; rewrite H', H''; clear H' H''.
 intros (H', H''); split; [ |exact H''].
 now rewrite H', Zmult_comm.
Qed.

Lemma div2_phi ih il j: (2^62 <= φ j -> φ ih < φ j ->
  φ (fst (diveucl_21 ih il j)) = Φ (WW ih il) / φ j)%Z.
Proof.
 intros Hj Hj1.
 generalize (diveucl_21_spec_aux ih il j Hj Hj1).
 case diveucl_21; intros q r (Hq, Hr).
 apply Zdiv_unique with φ r; auto with zarith.
 simpl @fst; apply eq_trans with (1 := Hq); ring.
Qed.

Lemma sqrt2_step_correct rec ih il j:
  2 ^ (Z_of_nat (size - 2)) <= φ ih ->
  0 < φ j -> Φ (WW ih il) < (φ j + 1) ^ 2 ->
  (forall j1, 0 < φ j1 < φ j ->  Φ (WW ih il) < (φ j1 + 1) ^ 2 ->
     φ (rec ih il j1) ^ 2 <= Φ (WW ih il) < (φ (rec ih il j1) + 1) ^ 2) ->
  φ (sqrt2_step rec ih il j) ^ 2 <= Φ (WW ih il)
      < (φ (sqrt2_step rec ih il j) + 1) ^  2.
Proof.
 assert (Hp2: (0 < φ 2)%Z) by exact (refl_equal Lt).
 intros Hih Hj Hij Hrec; rewrite sqrt2_step_def.
 assert (H1: (φ ih <= φ j)%Z) by (apply sqrt2_lower_bound with il; auto).
 case (to_Z_bounded ih); intros Hih1 _.
 case (to_Z_bounded il); intros Hil1 _.
 case (to_Z_bounded j); intros _ Hj1.
 assert (Hp3: (0 < Φ (WW ih il))).
 {simpl zn2z_to_Z;apply Z.lt_le_trans with (φ ih * wB)%Z; auto with zarith.
  apply Zmult_lt_0_compat; auto with zarith.
 }
 cbv zeta.
 case_eq (ih <? j)%uint63;intros Heq.
 2:{
   rewrite <-not_true_iff_false, ltb_spec in Heq.
   split; auto.
   apply sqrt_test_true; auto with zarith.
   unfold zn2z_to_Z; replace φ ih with φ j; auto with zarith.
   assert (0 <= φ il/φ j) by (apply Z_div_pos; auto with zarith).
   rewrite Zmult_comm, Z_div_plus_full_l; unfold base; auto with zarith.
 }
 rewrite -> ltb_spec in Heq.
 case (Zle_or_lt (2^(Z_of_nat size -1)) φ j); intros Hjj.
 1: case_eq (fst (diveucl_21 ih il j) <? j)%uint63;intros Heq0.
 2:{ rewrite <-not_true_iff_false, ltb_spec, (div2_phi _ _ _ Hjj Heq) in Heq0.
     split; auto; apply sqrt_test_true; auto with zarith. }
 - rewrite -> ltb_spec, (div2_phi _ _ _ Hjj Heq) in Heq0.
   match goal with |- context[rec _ _ ?X] =>
                     set (u := X)
   end.
   assert (H: φ u = (φ j + (Φ (WW ih il))/(φ j))/2).
   { unfold u; generalize (addc_spec j (fst (diveucl_21 ih il j)));
       case addc;unfold interp_carry;rewrite (div2_phi _ _ _ Hjj Heq);simpl zn2z_to_Z.
     { intros i H;rewrite lsr_spec, H;trivial. }
     intros i H;rewrite <- H.
     case (to_Z_bounded i); intros H1i H2i.
     rewrite -> add_spec, Zmod_small, lsr_spec.
     { change (1 * wB) with (φ (1 << (digits -1)) * 2)%Z.
       rewrite Z_div_plus_full_l; auto with zarith. }
     change wB with (2 * (wB/2))%Z; auto.
     replace φ (1 << (digits - 1)) with (wB/2); auto.
     rewrite lsr_spec; auto.
     replace (2^φ 1) with 2%Z; auto.
     split; auto with zarith.
     assert (φ i/2 < wB/2); auto with zarith.
     apply Zdiv_lt_upper_bound; auto with zarith. }
   apply Hrec; rewrite H; clear u H.
   + assert (Hf1: 0 <= Φ (WW ih il) / φ j) by (apply Z_div_pos; auto with zarith).
     case (Zle_lt_or_eq 1 (φ j)); auto with zarith; intros Hf2.
     split.
     * replace (φ j + Φ (WW ih il) / φ j)%Z with
         (1 * 2 + ((φ j - 2) + Φ (WW ih il) / φ j)) by lia.
       rewrite Z_div_plus_full_l; auto with zarith.
       assert (0 <= (φ j - 2 + Φ (WW ih il) / φ j) / 2) ; auto with zarith.
     * apply sqrt_test_false; auto with zarith.
   + apply sqrt_main; auto with zarith.
 - contradict Hij; apply Zle_not_lt.
   assert ((1 + φ j) <= 2 ^ (Z_of_nat size - 1)); auto with zarith.
   apply Z.le_trans with ((2 ^ (Z_of_nat size - 1)) ^2); auto with zarith.
   + assert (0 <= 1 + φ j); auto with zarith.
     apply Zmult_le_compat; auto with zarith.
   + change ((2 ^ (Z_of_nat size - 1))^2) with (2 ^ (Z_of_nat size - 2) * wB).
     apply Z.le_trans with (φ ih * wB); auto with zarith.
     unfold zn2z_to_Z, wB; auto with zarith.
Qed.

Lemma iter2_sqrt_correct n rec ih il j:
  2^(Z_of_nat (size - 2)) <= φ ih ->  0 < φ j -> Φ (WW ih il) < (φ j + 1) ^ 2 ->
  (forall j1, 0 < φ j1 -> 2^(Z_of_nat n) + φ j1 <= φ j ->
      Φ (WW ih il) < (φ j1 + 1) ^ 2 ->
       φ (rec ih il j1) ^ 2 <= Φ (WW ih il) < (φ (rec ih il j1) + 1) ^ 2)  ->
  φ (iter2_sqrt n rec ih il j) ^ 2 <= Φ (WW ih il)
      < (φ (iter2_sqrt n rec ih il j) + 1) ^ 2.
Proof.
 revert rec ih il j; elim n; unfold iter2_sqrt; fold iter2_sqrt; clear n.
 - intros rec ih il j Hi Hj Hij Hrec; apply sqrt2_step_correct. 1-3: lia.
   intros; apply Hrec; only 2: rewrite Zpower_0_r; auto with zarith.
 - intros n Hrec rec ih il j Hi Hj Hij HHrec.
   apply sqrt2_step_correct; auto.
   intros j1 Hj1  Hjp1; apply Hrec; auto with zarith.
   intros j2 Hj2 H2j2 Hjp2; apply Hrec; auto with zarith.
   intros j3 Hj3 Hpj3.
   apply HHrec; auto.
   rewrite -> inj_S, Z.pow_succ_r.
   + apply Z.le_trans with (2 ^Z_of_nat n + φ j2)%Z; auto with zarith.
   + apply Zle_0_nat.
Qed.

Lemma sqrt2_spec : forall x y,
       wB/ 4 <= φ x ->
       let (s,r) := sqrt2 x y in
          Φ (WW x y) = φ s ^ 2 + [+|r|] /\
          [+|r|] <= 2 * φ s.
 Proof.
 intros ih il Hih; unfold sqrt2.
 change Φ (WW ih il) with (Φ(WW ih il)).
 assert (Hbin: forall s, s * s + 2* s + 1 = (s + 1) ^ 2) by
  (intros s; ring).
 assert (Hb: 0 <= wB) by (red; intros HH; discriminate).
 assert (Hi2: Φ(WW ih il ) < (φ max_int + 1) ^ 2). {
  apply Z.le_lt_trans with ((wB - 1) * wB + (wB - 1)); auto with zarith.
  case (to_Z_bounded ih); case (to_Z_bounded il); intros H1 H2 H3 H4.
  unfold zn2z_to_Z; auto with zarith.
 }
 case (iter2_sqrt_correct size (fun _ _ j => j) ih il max_int); auto with zarith.
 - apply refl_equal.
 - intros j1 _ HH; contradict HH.
   apply Zlt_not_le.
   case (to_Z_bounded j1); auto with zarith.
   change (2 ^ Z_of_nat size) with (φ max_int+1)%Z; auto with zarith.
 - set (s := iter2_sqrt size (fun _ _ j : int=> j) ih il max_int).
   intros Hs1 Hs2.
   generalize (mulc_spec s s); case mulc.
   simpl fst; simpl snd; intros ih1 il1 Hihl1.
   generalize (subc_spec il il1).
   case subc; intros il2 Hil2.
   + simpl interp_carry in Hil2.
     case_eq (ih1  <? ih)%uint63;  [idtac | rewrite <- not_true_iff_false];
       rewrite ltb_spec; intros Heq.
     * unfold interp_carry; rewrite Zmult_1_l.
       rewrite -> Z.pow_2_r, Hihl1, Hil2.
       case (Zle_lt_or_eq (φ ih1 + 1) (φ ih)); auto with zarith.
       -- intros H2; contradict Hs2; apply Zle_not_lt.
          replace ((φ s + 1) ^ 2) with (Φ(WW ih1 il1) + 2 * φ s + 1).
          ++ unfold zn2z_to_Z.
             case (to_Z_bounded il); intros Hpil _.
             assert (Hl1l: φ il1 <= φ il).
             ** case (to_Z_bounded il2); rewrite Hil2; auto with zarith.
             ** enough (φ ih1 * wB + 2 * φ s + 1 <= φ ih * wB) by lia.
                case (to_Z_bounded s); intros _ Hps.
                case (to_Z_bounded ih1); intros Hpih1 _.
                apply Z.le_trans with ((φ ih1 + 2) * wB). { lia. }
                auto with zarith.
          ++ unfold zn2z_to_Z; rewrite <-Hihl1, Hbin; auto.
       -- intros H2; split.
          ++ unfold zn2z_to_Z; rewrite <- H2; ring.
          ++ replace (wB + (φ il - φ il1)) with (Φ(WW ih il) - (φ s * φ s)).
             { rewrite <-Hbin in Hs2; auto with zarith. }
             rewrite Hihl1; unfold zn2z_to_Z; rewrite <- H2; ring.
     * unfold interp_carry.
       case (Zle_lt_or_eq φ ih φ ih1); auto with zarith; intros H.
       -- contradict Hs1.
          apply Zlt_not_le; rewrite Z.pow_2_r, Hihl1.
          unfold zn2z_to_Z.
          case (to_Z_bounded il); intros _ H2.
          apply Z.lt_le_trans with ((φ ih + 1) * wB + 0).
          ++ rewrite Zmult_plus_distr_l, Zplus_0_r; auto with zarith.
          ++ case (to_Z_bounded il1); intros H3 _.
             apply Zplus_le_compat; auto with zarith.
       -- split.
          ++ rewrite Z.pow_2_r, Hihl1.
             unfold zn2z_to_Z; ring[Hil2 H].
          ++ replace φ il2 with (Φ(WW ih il) - Φ(WW ih1 il1)).
             { unfold zn2z_to_Z at 2; rewrite <-Hihl1.
               rewrite <-Hbin in Hs2; auto with zarith. }
             unfold zn2z_to_Z; rewrite H, Hil2; ring.
   + unfold interp_carry in Hil2 |- *.
     assert (Hsih: φ (ih - 1) = φ ih - 1).
     { rewrite sub_spec, Zmod_small; auto; replace φ 1 with 1; auto.
       case (to_Z_bounded ih); intros H1 H2.
       split; auto with zarith.
       apply Z.le_trans with (wB/4 - 1); auto with zarith. }
     case_eq (ih1 <? ih - 1)%uint63;  [idtac | rewrite <- not_true_iff_false];
       rewrite ltb_spec, Hsih; intros Heq.
     * rewrite Z.pow_2_r, Hihl1.
       case (Zle_lt_or_eq (φ ih1 + 2) φ ih); auto with zarith.
       -- intros H2; contradict Hs2; apply Zle_not_lt.
          replace ((φ s + 1) ^ 2) with (Φ(WW ih1 il1) + 2 * φ s + 1).
          ++ unfold zn2z_to_Z.
             assert (φ ih1 * wB + 2 * φ s + 1 <= φ ih * wB + (φ il - φ il1));
               auto with zarith.
             rewrite <-Hil2.
             case (to_Z_bounded il2); intros Hpil2 _.
             apply Z.le_trans with (φ ih * wB + - wB); auto with zarith.
             case (to_Z_bounded s);  intros _ Hps.
             assert (2 * φ s + 1 <= 2 * wB); auto with zarith.
             apply Z.le_trans with (φ ih1 * wB + 2 * wB); auto with zarith.
             assert (Hi: (φ ih1 + 3) * wB <= φ ih * wB) by auto with zarith.
             lia.
          ++ unfold zn2z_to_Z; rewrite <-Hihl1, Hbin; auto.
       -- intros H2; unfold zn2z_to_Z; rewrite <-H2.
          split.
          ++ replace φ il with ((φ il - φ il1) + φ il1) by ring.
             rewrite <-Hil2; ring.
          ++ replace (1 * wB + φ il2) with (Φ(WW ih il) - Φ(WW ih1 il1)).
             { unfold zn2z_to_Z at 2; rewrite <-Hihl1.
               rewrite <-Hbin in Hs2; auto with zarith. }
             unfold zn2z_to_Z; rewrite <-H2.
             replace φ il with ((φ il - φ il1) + φ il1); try ring.
             rewrite <-Hil2; ring.
     * case (Zle_lt_or_eq (φ ih - 1) (φ ih1)); auto with zarith; intros H1.
       -- assert (He: φ ih = φ ih1). {
            apply Zle_antisym; auto with zarith.
            case (Zle_or_lt φ ih1 φ ih); auto; intros H2.
            contradict Hs1; apply Zlt_not_le; rewrite Z.pow_2_r, Hihl1.
            unfold zn2z_to_Z.
            case (to_Z_bounded il); intros _ Hpil1.
            apply Z.lt_le_trans with ((φ ih + 1) * wB).
            - rewrite Zmult_plus_distr_l, Zmult_1_l; auto with zarith.
            - case (to_Z_bounded il1); intros Hpil2 _.
              apply Z.le_trans with ((φ ih1) * wB); auto with zarith.
          }
          contradict Hs1; apply Zlt_not_le; rewrite Z.pow_2_r, Hihl1.
          unfold zn2z_to_Z; rewrite He.
          assert (φ il - φ il1 < 0); auto with zarith.
          rewrite <-Hil2.
          case (to_Z_bounded il2); auto with zarith.
       -- split.
          ++ rewrite Z.pow_2_r, Hihl1.
             unfold zn2z_to_Z; rewrite <-H1.
             apply trans_equal with (φ ih * wB + φ il1 + (φ il - φ il1)).
             ** ring.
             ** rewrite <-Hil2; ring.
          ++ replace φ il2 with (Φ(WW ih il) - Φ(WW ih1 il1)).
             ** unfold zn2z_to_Z at 2; rewrite <- Hihl1.
                rewrite <-Hbin in Hs2; auto with zarith.
             ** unfold zn2z_to_Z.
                rewrite <-H1.
                ring_simplify.
                apply trans_equal with (wB + (φ il - φ il1)).
                1:ring.
                rewrite <-Hil2; ring.
 Qed.

(* of_pos *)
Lemma of_pos_rec_spec (k: nat) :
  (k <= size)%nat →
  ∀ p, φ(of_pos_rec k p) = Zpos p mod 2 ^ Z.of_nat k.
Proof.
  elim k; clear k.
  { intros _ [p|p| ]; simpl; rewrite to_Z_0, Zmod_1_r; reflexivity. }
  intros n ih hn.
  assert (n <= size)%nat as hn' by lia.
  specialize (ih hn').
  intros [ p | p | ].
  3: {
    rewrite Zmod_small.
    - reflexivity.
    - split.
      + lia.
      + apply Zpower_gt_1; lia.
  }
  - simpl.
    destruct (bit_add_or (of_pos_rec n p << 1) 1) as (H1, _).
    rewrite <- H1;clear H1.
    2: {
      intros i; rewrite bit_lsl, bit_1.
      case eqbP.
      + intros h; apply to_Z_inj in h; subst. exact (λ e _, diff_false_true e).
      + exact (λ _ _, diff_false_true).
    }
    rewrite add_spec, lsl_spec, ih, to_Z_1; clear ih.
    rewrite Z.pow_pos_fold, Zpos_P_of_succ_nat.
    change (Zpos p~1) with (2 ^ 1 * Zpos p + 1)%Z.
    rewrite Zmod_distr by lia.
    rewrite Zpower_Zsucc by auto with zarith.
    rewrite Zplus_mod_idemp_l.
    rewrite Zmod_small.
    { rewrite Zmult_mod_distr_l; lia. }
    set (a := Z.of_nat n).
    set (b := Zpos p).
    change (2 ^ 1) with 2.
    pose proof (pow2_pos a (Nat2Z.is_nonneg _)).
    elim_div; intros x y [ ? ha]. { lia. }
    destruct ha as [ ha | ]. 2: lia.
    split. { lia. }
    apply Z.lt_le_trans with (2 ^ (a + 1)).
    2: apply Z.pow_le_mono_r; subst a; lia.
    fold (Z.succ a); rewrite Z.pow_succ_r. { lia. }
    subst a; lia.
  - simpl. rewrite lsl_spec, ih, to_Z_1, Zmod_small.
    + rewrite Z.pow_pos_fold, Zpos_P_of_succ_nat, Zpower_Zsucc by lia.
      change (Zpos p~0) with (2 ^ 1 * Zpos p)%Z.
      rewrite Z.mul_mod_distr_l; auto with zarith.
    + set (a := Z.of_nat n).
      set (b := Zpos p).
      change (2 ^ 1) with 2.
      pose proof (pow2_pos a (Nat2Z.is_nonneg _)).
      elim_div; intros x y [ ? ha]. { lia. }
      destruct ha as [ ha | ]. 2: lia.
      split. { lia. }
      apply Z.lt_le_trans with (2 ^ (a + 1)).
      2: apply Z.pow_le_mono_r; subst a; lia.
      fold (Z.succ a); rewrite Z.pow_succ_r. { lia. }
      subst a; lia.
Qed.

Lemma is_int n :
  0 <= n < 2 ^ φ digits →
  n = φ (of_Z n).
Proof.
  destruct n;[reflexivity | | lia ].
  intros [_ h]. simpl.
  unfold of_pos. rewrite of_pos_rec_spec by lia.
  symmetry; apply Z.mod_small. split.
  - lia.
  - exact h.
Qed.

Lemma of_Z_spec n : φ (of_Z n) = n mod wB.
Proof.
  destruct n.
  - reflexivity.
  - now simpl; unfold of_pos; rewrite of_pos_rec_spec by lia.
  - simpl; unfold of_pos; rewrite opp_spec.
    rewrite of_pos_rec_spec; [ |auto]; fold wB.
    now rewrite <-(Z.sub_0_l), Zminus_mod_idemp_r.
Qed.

(* General lemmas *)
Lemma Z_oddE a : Z.odd a = (a mod 2 =? 1)%Z.
Proof. rewrite Zmod_odd; case Z.odd; reflexivity. Qed.

Lemma Z_evenE a : Z.even a = (a mod 2 =? 0)%Z.
Proof. rewrite Zmod_even; case Z.even; reflexivity. Qed.

(* is_zero *)
Lemma is_zeroE n : is_zero n = Z.eqb (φ n) 0.
Proof.
  case Z.eqb_spec.
  - intros h; apply (to_Z_inj n 0) in h; subst n; reflexivity.
  - generalize (proj1 (is_zero_spec n)).
    case is_zero; auto; intros ->; auto; destruct 1; reflexivity.
Qed.

(* bit *)
Lemma bitE i j : bit i j = Z.testbit φ(i) φ(j).
Proof.
  symmetry; apply negb_sym; rewrite is_zeroE, lsl_spec, lsr_spec.
  generalize (φ i) (to_Z_bounded i) (φ j) (to_Z_bounded j); clear i j;
  intros i [hi hi'] j [hj hj'].
  rewrite Z.testbit_eqb by auto; rewrite <- Z_oddE, Z.negb_odd, Z_evenE.
  remember (i / 2 ^ j) as k.
  change wB with (2 * 2 ^ φ (digits - 1)).
  unfold Z.modulo at 2.
  generalize (Z_div_mod_full k 2 (λ k, let 'eq_refl := k in I)); unfold Remainder.
  destruct Z.div_eucl as [ p q ]; intros [hk [ hq | ]]. 2: lia.
  rewrite hk.
  remember φ (digits - 1) as m.
  replace ((_ + _) * _) with (q * 2 ^ m + p * (2 * 2 ^ m)) by ring.
  rewrite Z_mod_plus by (subst m; reflexivity).
  assert (q = 0 ∨ q = 1) as D by lia.
  destruct D; subst; reflexivity.
Qed.

(* land, lor, lxor *)
Lemma lt_pow_lt_log d k n :
  0 < d <= n →
  0 <= k < 2 ^ d →
  Z.log2 k < n.
Proof.
  intros [hd hdn] [hk hkd].
  assert (k = 0 ∨ 0 < k) as D by lia.
  clear hk; destruct D as [ hk | hk ].
  - subst k; simpl; lia.
  - apply Z.log2_lt_pow2.
    + lia.
    + eapply Z.lt_le_trans.
      * eassumption.
      * apply Z.pow_le_mono_r; lia.
Qed.

Lemma land_spec' x y : φ (x land y) = Z.land φ(x) φ(y).
Proof.
  apply Z.bits_inj'; intros n hn.
  destruct (to_Z_bounded (x land y)) as [ hxy hxy' ].
  destruct (to_Z_bounded x) as [ hx hx' ].
  destruct (to_Z_bounded y) as [ hy hy' ].
  case (Z_lt_le_dec n (φ digits)); intros hd.
  2: {
    rewrite !Z.bits_above_log2; auto.
    - apply Z.land_nonneg; auto.
    - eapply Z.le_lt_trans.
      { apply Z.log2_land; assumption. }
      apply Z.min_lt_iff.
      left. apply (lt_pow_lt_log φ digits).
      + exact (conj eq_refl hd).
      + split; assumption.
    - apply (lt_pow_lt_log φ digits).
      + exact (conj eq_refl hd).
      + split; assumption.
  }
  rewrite (is_int n).
  { rewrite Z.land_spec, <- !bitE, land_spec; reflexivity. }
  apply (conj hn).
  apply (Z.lt_trans _ _ _ hd).
  apply Zpower2_lt_lin. lia.
Qed.

Lemma lor_spec' x y : φ (x lor y) = Z.lor φ(x) φ(y).
Proof.
  apply Z.bits_inj'; intros n hn.
  destruct (to_Z_bounded (x lor y)) as [ hxy hxy' ].
  destruct (to_Z_bounded x) as [ hx hx' ].
  destruct (to_Z_bounded y) as [ hy hy' ].
  case (Z_lt_le_dec n (φ digits)); intros hd.
  2: {
    rewrite !Z.bits_above_log2; auto.
    - apply Z.lor_nonneg; auto.
    - rewrite Z.log2_lor by assumption.
      apply Z.max_lub_lt; apply (lt_pow_lt_log φ digits); split; assumption || reflexivity.
    - apply (lt_pow_lt_log φ digits); split; assumption || reflexivity.
  }
  rewrite (is_int n).
  { rewrite Z.lor_spec, <- !bitE, lor_spec; reflexivity. }
  apply (conj hn).
  apply (Z.lt_trans _ _ _ hd).
  apply Zpower2_lt_lin. lia.
Qed.

Lemma lxor_spec' x y : φ (x lxor y) = Z.lxor φ(x) φ(y).
Proof.
  apply Z.bits_inj'; intros n hn.
  destruct (to_Z_bounded (x lxor y)) as [ hxy hxy' ].
  destruct (to_Z_bounded x) as [ hx hx' ].
  destruct (to_Z_bounded y) as [ hy hy' ].
  case (Z_lt_le_dec n (φ digits)); intros hd.
  2: {
    rewrite !Z.bits_above_log2; auto.
    - apply Z.lxor_nonneg; split; auto.
    - eapply Z.le_lt_trans.
      { apply Z.log2_lxor; assumption. }
      apply Z.max_lub_lt; apply (lt_pow_lt_log φ digits); split; assumption || reflexivity.
    - apply (lt_pow_lt_log φ digits); split; assumption || reflexivity.
  }
  rewrite (is_int n).
  { rewrite Z.lxor_spec, <- !bitE, lxor_spec; reflexivity. }
  apply (conj hn).
  apply (Z.lt_trans _ _ _ hd).
  apply Zpower2_lt_lin. lia.
Qed.

Lemma landC i j : i land j = j land i.
Proof.
 apply bit_ext; intros n.
 rewrite !land_spec, andb_comm; auto.
Qed.

Lemma landA i j k : i land (j land k) = i land j land k.
Proof.
 apply bit_ext; intros n.
 rewrite !land_spec, andb_assoc; auto.
Qed.

Lemma land0 i : 0 land i = 0%uint63.
Proof.
 apply bit_ext; intros n.
 rewrite land_spec, bit_0; auto.
Qed.

Lemma land0_r i : i land 0 = 0%uint63.
Proof. rewrite landC; exact (land0 i). Qed.

Lemma lorC i j : i lor j = j lor i.
Proof.
 apply bit_ext; intros n.
 rewrite !lor_spec, orb_comm; auto.
Qed.

Lemma lorA i j k : i lor (j lor k) = i lor j lor k.
Proof.
 apply bit_ext; intros n.
 rewrite !lor_spec, orb_assoc; auto.
Qed.

Lemma lor0 i : 0 lor i = i.
Proof.
 apply bit_ext; intros n.
 rewrite lor_spec, bit_0; auto.
Qed.

Lemma lor0_r i : i lor 0 = i.
Proof. rewrite lorC; exact (lor0 i). Qed.

Lemma lxorC i j : i lxor j = j lxor i.
Proof.
 apply bit_ext; intros n.
 rewrite !lxor_spec, xorb_comm; auto.
Qed.

Lemma lxorA i j k : i lxor (j lxor k) = i lxor j lxor k.
Proof.
 apply bit_ext; intros n.
 rewrite !lxor_spec, xorb_assoc; auto.
Qed.

Lemma lxor0 i : 0 lxor i = i.
Proof.
 apply bit_ext; intros n.
 rewrite lxor_spec, bit_0, xorb_false_l; auto.
Qed.

Lemma lxor0_r i : i lxor 0 = i.
Proof. rewrite lxorC; exact (lxor0 i). Qed.

Lemma opp_to_Z_opp (x : int) :
    φ x mod wB <> 0 ->
  (- φ (- x)) mod wB = (φ x) mod wB.
Proof.
  intros neqx0.
  rewrite opp_spec.
  rewrite (Z_mod_nz_opp_full (φ x%uint63)) by assumption.
  rewrite (Z.mod_small (φ x%uint63)) by apply to_Z_bounded.
  rewrite <- Z.add_opp_l.
  rewrite Z.opp_add_distr, Z.opp_involutive.
  replace (- wB) with (-1 * wB) by easy.
  rewrite Z_mod_plus by easy.
  now rewrite Z.mod_small by apply to_Z_bounded.
Qed.

(** Minimum / maximum *)

Definition min (i1 i2 : int) :=
  if (i1 <=? i2)%uint63 then i1 else i2.

Definition max (i1 i2 : int) :=
  if (i1 <=? i2)%uint63 then i2 else i1.

Lemma min_spec (x y : int) :
  φ (min x y) = Z.min (φ x) (φ y).
Proof.
  unfold min. destruct (lebP x y).
  - rewrite Z.min_l; [reflexivity | assumption].
  - rewrite Z.min_r; [reflexivity | lia].
Qed.

Lemma max_spec (x y : int) :
  φ (max x y) = Z.max (φ x) (φ y).
Proof.
  unfold max. destruct (lebP x y).
  - rewrite Z.max_r; [reflexivity | assumption].
  - rewrite Z.max_l; [reflexivity | lia].
Qed.

Lemma min_add_min_n_same (m i1 i2 : int) :
  to_Z i1 + to_Z i2 < wB ->
  Uint63.min m (Uint63.min m i1 + i2) = Uint63.min m (i1 + i2).
Proof.
  intros H. apply to_Z_inj.
  pose proof (to_Z_bounded m) as Hm.
  pose proof (to_Z_bounded i1) as Hi1.
  pose proof (to_Z_bounded i2) as Hi2.
  rewrite !min_spec, !add_spec, !min_spec, !Z.mod_small; lia.
Qed.

Lemma min_add_n_min_same (m i1 i2 : int) :
  to_Z i1 + to_Z i2 < wB ->
  Uint63.min m (i1 + Uint63.min m i2) = Uint63.min m (i1 + i2).
Proof.
  intros H. apply to_Z_inj.
  pose proof (to_Z_bounded m) as Hm.
  pose proof (to_Z_bounded i1) as Hi1.
  pose proof (to_Z_bounded i2) as Hi2.
  rewrite !min_spec, !add_spec, !min_spec, !Z.mod_small; lia.
Qed.

Module Export Uint63Notations.
  Local Open Scope uint63_scope.
  Export Uint63NotationsInternalB.
  Export Uint63NotationsInternalC.
  Export Uint63NotationsInternalD.
End Uint63Notations.
