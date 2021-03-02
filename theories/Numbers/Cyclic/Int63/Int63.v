(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * Most of the definitions in this file were deprecated. Use Uint63.v instead *)

Require Export DoubleType.
Require Export PrimInt63.
Require Uint63.

Bind Scope int63_scope with int.

#[deprecated(since="8.14",note="Use Uint63.mod instead.")]
Notation mod := Uint63.mod (only parsing).
Notation lor := Uint63.lor (only parsing).
Notation land := Uint63.land (only parsing).
Notation lxor := Uint63.lxor (only parsing).

Import Uint63.

Notation size := size (only parsing).

Notation int := int (only parsing).
Notation lsl := lsl (only parsing).
Notation lsr := lsr (only parsing).
Notation add := add (only parsing).
Notation sub := sub (only parsing).
Notation mul := mul (only parsing).
Notation mulc := mulc (only parsing).
#[deprecated(since="8.14",note="Use Uint63.div instead.")]
Notation div := div (only parsing).
Notation eqb := eqb (only parsing).
#[deprecated(since="8.14",note="Use Uint63.ltb instead.")]
Notation ltb := ltb (only parsing).
#[deprecated(since="8.14",note="Use Uint63.leb instead.")]
Notation leb := leb (only parsing).


Module Import Int63NotationsInternalB.
#[deprecated(since="8.14",note="Use the uint63_scope instead.")]
Infix "<<" := Uint63.lsl (at level 30, no associativity) : int63_scope.
#[deprecated(since="8.14",note="Use the uint63_scope instead.")]
Infix ">>" := Uint63.lsr (at level 30, no associativity) : int63_scope.
#[deprecated(since="8.14",note="Use the uint63_scope instead.")]
Infix "land" := Uint63.land (at level 40, left associativity) : int63_scope.
#[deprecated(since="8.14",note="Use the uint63_scope instead.")]
Infix "lor" := Uint63.lor (at level 40, left associativity) : int63_scope.
#[deprecated(since="8.14",note="Use the uint63_scope instead.")]
Infix "lxor" := Uint63.lxor (at level 40, left associativity) : int63_scope.
#[deprecated(since="8.14",note="Use the uint63_scope instead.")]
Infix "+" := Uint63.add : int63_scope.
#[deprecated(since="8.14",note="Use the uint63_scope instead.")]
Infix "-" := Uint63.sub : int63_scope.
#[deprecated(since="8.14",note="Use the uint63_scope instead.")]
Infix "*" := Uint63.mul : int63_scope.
#[deprecated(since="8.14",note="Use the uint63_scope instead.")]
Infix "/" := Uint63.div : int63_scope.
#[deprecated(since="8.14",note="Use the uint63_scope instead.")]
Infix "mod" := Uint63.mod (at level 40, no associativity) : int63_scope.
#[deprecated(since="8.14",note="Use the uint63_scope instead.")]
Infix "=?" := Uint63.eqb (at level 70, no associativity) : int63_scope.
#[deprecated(since="8.14",note="Use the uint63_scope instead.")]
Infix "<?" := Uint63.ltb (at level 70, no associativity) : int63_scope.
#[deprecated(since="8.14",note="Use the uint63_scope instead.")]
Infix "<=?" := Uint63.leb (at level 70, no associativity) : int63_scope.
#[deprecated(since="8.14",note="Use the uint63_scope instead.")]
Infix "≤?" := Uint63.leb (at level 70, no associativity) : int63_scope.
End Int63NotationsInternalB.


Notation digits := digits (only parsing).

#[deprecated(since="8.14",note="Use Uint63.max_int instead")]
Notation max_int := max_int (only parsing).

Notation get_digit := get_digit (only parsing).

Notation set_digit := set_digit (only parsing).

Notation is_zero := is_zero (only parsing).

Notation is_even := is_even (only parsing).

Notation bit := bit (only parsing).

Notation opp := opp (only parsing).

Notation oppcarry := oppcarry (only parsing).

Notation succ := succ (only parsing).

Notation pred := pred (only parsing).

Notation addcarry := addcarry (only parsing).

Notation subcarry := subcarry (only parsing).

Notation addc_def := addc_def (only parsing).
Notation addc := addc (only parsing).

Notation addcarryc_def := addcarryc_def (only parsing).
Notation addcarryc := addcarryc (only parsing).

Notation subc_def := subc_def (only parsing).
Notation subc := subc (only parsing).

Notation subcarryc_def := subcarryc_def (only parsing).
Notation subcarryc := subcarryc (only parsing).

#[deprecated(since="8.14",note="Use Uint63.diveucl_def instead")]
Notation diveucl_def := diveucl_def (only parsing).
#[deprecated(since="8.14",note="Use Uint63.diveucl instead")]
Notation diveucl := diveucl (only parsing).

#[deprecated(since="8.14",note="Use Uint63.diveucl_21 instead")]
Notation diveucl_21 := diveucl_21 (only parsing).

#[deprecated(since="8.14",note="Use Uint63.addmuldiv_def instead")]
Notation addmuldiv_def := addmuldiv_def (only parsing).
#[deprecated(since="8.14",note="Use Uint63.addmuldiv instead")]
Notation addmuldiv := addmuldiv (only parsing).

Module Import Int63NotationsInternalC.
#[deprecated(since="8.14",note="Use the uint63_scope instead.")]
Notation "- x" := (Uint63.opp x) : int63_scope.
#[deprecated(since="8.14",note="Use the uint63_scope instead.")]
Notation "n '+c' m" := (Uint63.addc n m) (at level 50, no associativity) : int63_scope.
#[deprecated(since="8.14",note="Use the uint63_scope instead.")]
Notation "n '-c' m" := (Uint63.subc n m) (at level 50, no associativity) : int63_scope.
End Int63NotationsInternalC.

Notation oppc := oppc (only parsing).

Notation succc := succc (only parsing).

Notation predc := predc (only parsing).

#[deprecated(since="8.14",note="Use Uint63.compare_def instead")]
Notation compare_def := compare_def (only parsing).
#[deprecated(since="8.14",note="Use Uint63.compare instead")]
Notation compare := compare (only parsing).

#[deprecated(since="8.14",note="Use Uint63.to_Z_rec instead")]
Notation to_Z_rec := to_Z_rec (only parsing).

#[deprecated(since="8.14",note="Use Uint63.to_Z instead")]
Notation to_Z := to_Z (only parsing).

#[deprecated(since="8.14",note="Use Uint63.of_pos_rec instead")]
Notation of_pos_rec := of_pos_rec (only parsing).

#[deprecated(since="8.14",note="Use Uint63.of_pos instead")]
Notation of_pos := of_pos (only parsing).

#[deprecated(since="8.14",note="Use Uint63.of_Z instead")]
Notation of_Z := of_Z (only parsing).

Notation wB := wB (only parsing).

Module Import Int63NotationsInternalD.
#[deprecated(since="8.14",note="Use the uint63_scope instead.")]
Notation "n ?= m" := (Uint63.compare n m) (at level 70, no associativity) : int63_scope.
#[deprecated(since="8.14",note="Use the uint63_scope instead.")]
Notation "'φ' x" := (Uint63.to_Z x) (at level 0) : int63_scope.
#[deprecated(since="8.14",note="Use the uint63_scope instead.")]
Notation "'Φ' x" :=
   (zn2z_to_Z Uint63.wB Uint63.to_Z x) (at level 0) : int63_scope.
End Int63NotationsInternalD.

#[deprecated(since="8.14",note="Use Uint63.to_Z_rec_bounded instead")]
Notation to_Z_rec_bounded := to_Z_rec_bounded (only parsing).

#[deprecated(since="8.14",note="Use Uint63.to_Z_bounded instead")]
Notation to_Z_bounded := to_Z_bounded (only parsing).

#[deprecated(since="8.14",note="Use BinInt.Z.div_lt_upper_bound instead")]
Notation Z_lt_div2 := Deprecated.Z_lt_div2 (only parsing).

Require Import ZArith.

#[deprecated(since="8.14",note="Use BinInt.Z.mod_bound_pos_le instead")]
Notation Zmod_le_first := Z.mod_bound_pos_le (only parsing).

#[deprecated(since="8.14",note="Use Uint63.Zmod_distr instead")]
Notation Zmod_distr := Zmod_distr (only parsing).

#[deprecated(since="8.14",note="Use Uint63.pow2_pos instead")]
Notation pow2_pos := pow2_pos (only parsing).

#[deprecated(since="8.14",note="Use Uint63.pow2_nz instead")]
Notation pow2_nz := pow2_nz (only parsing).

Notation wB_diff_0 := wB_diff_0 (only parsing).

Notation wB_pos := wB_pos (only parsing).

#[deprecated(since="8.14",note="Use Uint63.to_Z_0 instead")]
Notation to_Z_0 := to_Z_0 (only parsing).

#[deprecated(since="8.14",note="Use Uint63.to_Z_1 instead")]
Notation to_Z_1 := to_Z_1 (only parsing).

Local Open Scope Z_scope.

#[deprecated(since="8.14",note="Use the uint63_scope instead.")]
Local Notation "[+| c |]" := (interp_carry 1 Uint63.wB Uint63.to_Z c)
  (at level 0, c at level 99) : int63_scope.

#[deprecated(since="8.14",note="Use the uint63_scope instead.")]
Local Notation "[-| c |]" := (interp_carry (-1) Uint63.wB Uint63.to_Z c)
  (at level 0, c at level 99) : int63_scope.

#[deprecated(since="8.14",note="Use Uint63.of_to_Z instead")]
Notation of_to_Z := of_to_Z (only parsing).

#[deprecated(since="8.14",note="Use Uint63.can_inj instead")]
Notation can_inj := can_inj (only parsing).

#[deprecated(since="8.14",note="Use Uint63.to_Z_inj instead")]
Notation to_Z_inj := to_Z_inj (only parsing).

#[deprecated(since="8.14",note="Use Uint63.lsl_spec instead")]
Notation lsl_spec := lsl_spec (only parsing).

#[deprecated(since="8.14",note="Use Uint63.lsr_spec instead")]
Notation lsr_spec := lsr_spec (only parsing).

Notation land_spec := land_spec (only parsing).

Notation lor_spec := lor_spec (only parsing).

Notation lxor_spec := lxor_spec (only parsing).

#[deprecated(since="8.14",note="Use Uint63.add_spec instead")]
Notation add_spec := add_spec (only parsing).

#[deprecated(since="8.14",note="Use Uint63.sub_spec instead")]
Notation sub_spec := sub_spec (only parsing).

#[deprecated(since="8.14",note="Use Uint63.mul_spec instead")]
Notation mul_spec := mul_spec (only parsing).

#[deprecated(since="8.14",note="Use Uint63.mulc_spec instead")]
Notation mulc_spec := mulc_spec (only parsing).

#[deprecated(since="8.14",note="Use Uint63.div_spec instead")]
Notation div_spec := div_spec (only parsing).

#[deprecated(since="8.14",note="Use Uint63.mod_spec instead")]
Notation mod_spec := mod_spec (only parsing).

Notation eqb_correct := eqb_correct (only parsing).

Notation eqb_refl := eqb_refl (only parsing).

#[deprecated(since="8.14",note="Use Uint63.ltb_spec instead")]
Notation ltb_spec := ltb_spec (only parsing).

#[deprecated(since="8.14",note="Use Uint63.leb_spec instead")]
Notation leb_spec := leb_spec (only parsing).

Notation head0 := head0 (only parsing).
Notation tail0 := tail0 (only parsing).

#[deprecated(since="8.14",note="Use Uint63.compare_def_spec instead")]
Notation compare_def_spec := compare_def_spec (only parsing).

#[deprecated(since="8.14",note="Use Uint63.head0_spec instead")]
Notation head0_spec := head0_spec (only parsing).

#[deprecated(since="8.14",note="Use Uint63.tail0_spec instead")]
Notation tail0_spec := tail0_spec (only parsing).

Notation addc_def_spec := addc_def_spec (only parsing).

Notation addcarryc_def_spec := addcarryc_def_spec (only parsing).

Notation subc_def_spec := subc_def_spec (only parsing).

Notation subcarryc_def_spec := subcarryc_def_spec (only parsing).

#[deprecated(since="8.14",note="Use Uint63.diveucl_def_spec instead")]
Notation diveucl_def_spec := diveucl_def_spec (only parsing).

#[deprecated(since="8.14",note="Use Uint63.diveucl_21_spec instead")]
Notation diveucl_21_spec := diveucl_21_spec (only parsing).

#[deprecated(since="8.14",note="Use Uint63.addmuldiv_def_spec instead")]
Notation addmuldiv_def_spec := addmuldiv_def_spec (only parsing).

#[deprecated(since="8.14",note="Use Uint63.sqrt_step instead")]
Notation sqrt_step := sqrt_step (only parsing).

#[deprecated(since="8.14",note="Use Uint63.iter_sqrt instead")]
Notation iter_sqrt := iter_sqrt (only parsing).

#[deprecated(since="8.14",note="Use Uint63.sqrt instead")]
Notation sqrt := sqrt (only parsing).

Notation high_bit := high_bit (only parsing).

#[deprecated(since="8.14",note="Use Uint63.sqrt2_step instead")]
Notation sqrt2_step := sqrt2_step (only parsing).

#[deprecated(since="8.14",note="Use Uint63.iter2_sqrt instead")]
Notation iter2_sqrt := iter2_sqrt (only parsing).

#[deprecated(since="8.14",note="Use Uint63.sqrt2 instead")]
Notation sqrt2 := sqrt2 (only parsing).

#[deprecated(since="8.14",note="Use Uint63.gcd_rec instead")]
Notation gcd_rec := gcd_rec (only parsing).

#[deprecated(since="8.14",note="Use Uint63.gcd instead")]
Notation gcd := gcd (only parsing).

Notation eqb_complete := eqb_complete (only parsing).

Notation eqb_spec := eqb_spec (only parsing).

Notation eqb_false_spec := eqb_false_spec (only parsing).

Notation eqb_false_complete := eqb_false_complete (only parsing).

Notation eqb_false_correct := eqb_false_correct (only parsing).

Notation eqs := eqs (only parsing).

Notation eq_dec := eq_dec (only parsing).

Notation cast := cast (only parsing).

Notation cast_refl := cast_refl (only parsing).

Notation cast_diff := cast_diff (only parsing).

Notation eqo := eqo (only parsing).

Notation eqo_refl := eqo_refl (only parsing).

Notation eqo_diff := eqo_diff (only parsing).

#[deprecated(since="8.14",note="Use Uint63.eqbP instead")]
Notation eqbP := eqbP (only parsing).

#[deprecated(since="8.14",note="Use Uint63.ltbP instead")]
Notation ltbP := ltbP (only parsing).

#[deprecated(since="8.14",note="Use Uint63.lebP instead")]
Notation lebP := lebP (only parsing).

#[deprecated(since="8.14",note="Use Uint63.compare_spec instead")]
Notation compare_spec := compare_spec (only parsing).

Notation is_zero_spec := is_zero_spec (only parsing).

#[deprecated(since="8.14",note="Use Uint63.diveucl_spec instead")]
Notation diveucl_spec := diveucl_spec (only parsing).

#[deprecated(since="8.14",note="Use Uint63.addc_spec instead")]
Notation addc_spec := addc_spec (only parsing).

#[deprecated(since="8.14",note="Use Uint63.succ_spec instead")]
Notation succ_spec := succ_spec (only parsing).

#[deprecated(since="8.14",note="Use Uint63.succc_spec instead")]
Notation succc_spec := succc_spec (only parsing).

#[deprecated(since="8.14",note="Use Uint63.addcarry_spec instead")]
Notation addcarry_spec := addcarry_spec (only parsing).

#[deprecated(since="8.14",note="Use Uint63.addcarryc_spec instead")]
Notation addcarryc_spec := addcarryc_spec (only parsing).

#[deprecated(since="8.14",note="Use Uint63.subc_spec instead")]
Notation subc_spec := subc_spec (only parsing).

#[deprecated(since="8.14",note="Use Uint63.pred_spec instead")]
Notation pred_spec := pred_spec (only parsing).

#[deprecated(since="8.14",note="Use Uint63.predc_spec instead")]
Notation predc_spec := predc_spec (only parsing).

#[deprecated(since="8.14",note="Use Uint63.oppc_spec instead")]
Notation oppc_spec := oppc_spec (only parsing).

#[deprecated(since="8.14",note="Use Uint63.opp_spec instead")]
Notation opp_spec := opp_spec (only parsing).

#[deprecated(since="8.14",note="Use Uint63.oppcarry_spec instead")]
Notation oppcarry_spec := oppcarry_spec (only parsing).

#[deprecated(since="8.14",note="Use Uint63.subcarry_spec instead")]
Notation subcarry_spec := subcarry_spec (only parsing).

#[deprecated(since="8.14",note="Use Uint63.subcarryc_spec instead")]
Notation subcarryc_spec := subcarryc_spec (only parsing).

#[deprecated(since="8.14",note="Use Uint63.to_Z_gcd instead")]
Notation to_Z_gcd := to_Z_gcd (only parsing).

#[deprecated(since="8.14",note="Use Uint63.gcd_spec instead")]
Notation gcd_spec := gcd_spec (only parsing).

#[deprecated(since="8.14",note="Use Uint63.head00_spec instead")]
Notation head00_spec := head00_spec (only parsing).

#[deprecated(since="8.14",note="Use Uint63.tail00_spec instead")]
Notation tail00_spec := tail00_spec (only parsing).

#[deprecated(since="8.14",note="Use the uint63_scope instead.")]
Infix "≡" := (eqm Uint63.wB) (at level 70, no associativity) : int63_scope.

Notation eqm_mod := eqm_mod (only parsing).

Notation eqm_sub := eqm_sub (only parsing).

Notation eqmE := eqmE (only parsing).

Notation eqm_subE := eqm_subE (only parsing).

#[deprecated(since="8.14",note="Use Uint63.int_eqm instead")]
Notation int_eqm := int_eqm (only parsing).

#[deprecated(since="8.14",note="Use Uint63.eqmI instead")]
Notation eqmI := eqmI (only parsing).

Notation add_assoc := add_assoc (only parsing).

Notation add_comm := add_comm (only parsing).

#[deprecated(since="8.14",note="Use Uint63.add_le_r instead")]
Notation add_le_r := add_le_r (only parsing).

Notation add_cancel_l := add_cancel_l (only parsing).

Notation add_cancel_r := add_cancel_r (only parsing).

Notation b2i := b2i (only parsing).

Notation lsr0 := lsr0 (only parsing).

Notation lsr_0_r := lsr_0_r (only parsing).

Notation lsr_1 := lsr_1 (only parsing).

#[deprecated(since="8.14",note="Use Uint63.lsr_add instead")]
Notation lsr_add := lsr_add (only parsing).

Notation lsl0 := lsl0 (only parsing).

Notation lsl0_r := lsl0_r (only parsing).

Notation lsl_add_distr := lsl_add_distr (only parsing).

#[deprecated(since="8.14",note="Use Uint63.lsr_M_r instead")]
Notation lsr_M_r := lsr_M_r (only parsing).

#[deprecated(since="8.14",note="Use Uint63.bit_0_spec instead")]
Notation bit_0_spec := bit_0_spec (only parsing).

Notation bit_split := bit_split (only parsing).

#[deprecated(since="8.14",note="Use Uint63.bit_lsr instead")]
Notation bit_lsr := bit_lsr (only parsing).

Notation bit_b2i := bit_b2i (only parsing).

Notation bit_1 := bit_1 (only parsing).

#[deprecated(since="8.14",note="Use Uint63.to_Z_split instead")]
Notation to_Z_split := to_Z_split (only parsing).

#[deprecated(since="8.14",note="Use Uint63.bit_M instead")]
Notation bit_M := bit_M (only parsing).

#[deprecated(since="8.14",note="Use Uint63.bit_half instead")]
Notation bit_half := bit_half (only parsing).

Notation bit_ext := bit_ext (only parsing).

#[deprecated(since="8.14",note="Use Uint63.bit_lsl instead")]
Notation bit_lsl := bit_lsl (only parsing).

Notation lor_lsr := lor_lsr (only parsing).

#[deprecated(since="8.14",note="Use Uint63.lor_le instead")]
Notation lor_le := lor_le (only parsing).

Notation bit_0 := bit_0 (only parsing).

Notation bit_add_or := bit_add_or (only parsing).

#[deprecated(since="8.14",note="Use Uint63.addmuldiv_spec instead")]
Notation addmuldiv_spec := addmuldiv_spec (only parsing).

Notation is_even_bit := is_even_bit (only parsing).

#[deprecated(since="8.14",note="Use Uint63.is_even_spec instead")]
Notation is_even_spec := is_even_spec (only parsing).

Notation is_even_0 := is_even_0 (only parsing).

Notation is_even_lsl_1 := is_even_lsl_1 (only parsing).

#[deprecated(since="8.14",note="Use Uint63.elim_div instead")]
Ltac elim_div := elim_div.

#[deprecated(since="8.14",note="Use Uint63.quotient_by_2 instead")]
Notation quotient_by_2 := quotient_by_2 (only parsing).

#[deprecated(since="8.14",note="Use Uint63.sqrt_main_trick instead")]
Notation sqrt_main_trick := sqrt_main_trick (only parsing).

#[deprecated(since="8.14",note="Use Uint63.sqrt_main instead")]
Notation sqrt_main := sqrt_main (only parsing).

#[deprecated(since="8.14",note="Use Uint63.sqrt_test_false instead")]
Notation sqrt_test_false := sqrt_test_false (only parsing).

#[deprecated(since="8.14",note="Use Uint63.sqrt_test_true instead")]
Notation sqrt_test_true := sqrt_test_true (only parsing).

#[deprecated(since="8.14",note="Use Uint63.sqrt_step_correct instead")]
Notation sqrt_step_correct := sqrt_step_correct (only parsing).

#[deprecated(since="8.14",note="Use Uint63.iter_sqrt_correct instead")]
Notation iter_sqrt_correct := iter_sqrt_correct (only parsing).

#[deprecated(since="8.14",note="Use Uint63.sqrt_init instead")]
Notation sqrt_init := sqrt_init (only parsing).

#[deprecated(since="8.14",note="Use Uint63.sqrt_spec instead")]
Notation sqrt_spec := sqrt_spec (only parsing).

#[deprecated(since="8.14",note="Use Uint63.sqrt2_step_def instead")]
Notation sqrt2_step_def := sqrt2_step_def (only parsing).

#[deprecated(since="8.14",note="Use Uint63.sqrt2_lower_bound instead")]
Notation sqrt2_lower_bound := sqrt2_lower_bound (only parsing).

#[deprecated(since="8.14",note="Use Uint63.diveucl_21_spec_aux instead")]
Notation diveucl_21_spec_aux := diveucl_21_spec_aux (only parsing).

#[deprecated(since="8.14",note="Use Uint63.div2_phi instead")]
Notation div2_phi := div2_phi (only parsing).

#[deprecated(since="8.14",note="Use Uint63.sqrt2_step_correct instead")]
Notation sqrt2_step_correct := sqrt2_step_correct (only parsing).

#[deprecated(since="8.14",note="Use Uint63.iter2_sqrt_correct instead")]
Notation iter2_sqrt_correct := iter2_sqrt_correct (only parsing).

#[deprecated(since="8.14",note="Use Uint63.sqrt2_spec instead")]
Notation sqrt2_spec := sqrt2_spec (only parsing).

#[deprecated(since="8.14",note="Use Uint63.of_pos_rec_spec instead")]
Notation of_pos_rec_spec := of_pos_rec_spec (only parsing).

#[deprecated(since="8.14",note="Use Uint63.is_int instead")]
Notation is_int := is_int (only parsing).

#[deprecated(since="8.14",note="Use Uint63.of_Z_spec instead")]
Notation of_Z_spec := of_Z_spec (only parsing).

#[deprecated(since="8.14",note="Use Bool.negb_sym instead")]
Notation negbE := Deprecated.negbE (only parsing).

#[deprecated(since="8.14",note="Use Uint63.Z_oddE instead")]
Notation Z_oddE := Z_oddE (only parsing).

#[deprecated(since="8.14",note="Use Uint63.Z_evenE instead")]
Notation Z_evenE := Z_evenE (only parsing).

#[deprecated(since="8.14",note="Use Uint63.is_zeroE instead")]
Notation is_zeroE := is_zeroE (only parsing).

#[deprecated(since="8.14",note="Use Uint63.bitE instead")]
Notation bitE := bitE (only parsing).

#[deprecated(since="8.14",note="Use Uint63.lt_pow_lt_log instead")]
Notation lt_pow_lt_log := lt_pow_lt_log (only parsing).

#[deprecated(since="8.14",note="Use Uint63.land_spec' instead")]
Notation land_spec' := land_spec' (only parsing).

#[deprecated(since="8.14",note="Use Uint63.lor_spec' instead")]
Notation lor_spec' := lor_spec' (only parsing).

#[deprecated(since="8.14",note="Use Uint63.lxor_spec' instead")]
Notation lxor_spec' := lxor_spec' (only parsing).

Notation landC := landC (only parsing).

Notation landA := landA (only parsing).

Notation land0 := land0 (only parsing).

Notation land0_r := land0_r (only parsing).

Notation lorC := lorC (only parsing).

Notation lorA := lorA (only parsing).

Notation lor0 := lor0 (only parsing).

Notation lor0_r := lor0_r (only parsing).

Notation lxorC := lxorC (only parsing).

Notation lxorA := lxorA (only parsing).

Notation lxor0 := lxor0 (only parsing).

Notation lxor0_r := lxor0_r (only parsing).

#[deprecated(since="8.14",note="Use Uint63.opp_to_Z_opp instead")]
Notation opp_to_Z_opp := opp_to_Z_opp (only parsing).

Module Export Int63Notations.
  Local Open Scope uint63_scope.
  (* TODO leave 8.13 or update to 8.14? *)
  #[deprecated(since="8.13",note="use infix mod in the uint63_scope instead")]
   Notation "a \% m" := (a mod m) (at level 40, left associativity) : int63_scope.
  #[deprecated(since="8.13",note="use infix =? in the uint63_scope instead")]
   Notation "m '==' n" := (m =? n) (at level 70, no associativity) : int63_scope.
  #[deprecated(since="8.13",note="use infix <? in the uint63_scope instead")]
   Notation "m < n" := (m <? n) : int63_scope.
  #[deprecated(since="8.13",note="use infix <=? in the uint63_scope instead")]
   Notation "m <= n" := (m <=? n) : int63_scope.
  #[deprecated(since="8.13",note="use infix ≤? in the uint63_scope instead")]
   Notation "m ≤ n" := (m <=? n) (at level 70, no associativity) : int63_scope.
  Export Int63NotationsInternalB.
  Export Int63NotationsInternalC.
  Export Int63NotationsInternalD.
End Int63Notations.
