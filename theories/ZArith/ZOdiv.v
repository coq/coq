(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Export ZOdiv_def.
Require Import BinInt Zquot.

Notation ZO_div_mod_eq := Z.quot_rem' (only parsing).
Notation ZOmod_lt := Zrem_lt (only parsing).
Notation ZOmod_sgn := Zrem_sgn (only parsing).
Notation ZOmod_sgn2 := Zrem_sgn2 (only parsing).
Notation ZOmod_lt_pos := Zrem_lt_pos (only parsing).
Notation ZOmod_lt_neg := Zrem_lt_neg (only parsing).
Notation ZOmod_lt_pos_pos := Zrem_lt_pos_pos (only parsing).
Notation ZOmod_lt_pos_neg := Zrem_lt_pos_neg (only parsing).
Notation ZOmod_lt_neg_pos := Zrem_lt_neg_pos (only parsing).
Notation ZOmod_lt_neg_neg := Zrem_lt_neg_neg (only parsing).

Notation ZOdiv_opp_l := Zquot_opp_l (only parsing).
Notation ZOdiv_opp_r := Zquot_opp_r (only parsing).
Notation ZOmod_opp_l := Zrem_opp_l (only parsing).
Notation ZOmod_opp_r := Zrem_opp_r (only parsing).
Notation ZOdiv_opp_opp := Zquot_opp_opp (only parsing).
Notation ZOmod_opp_opp := Zrem_opp_opp (only parsing).

Notation Remainder := Remainder (only parsing).
Notation Remainder_alt := Remainder_alt (only parsing).
Notation Remainder_equiv := Remainder_equiv (only parsing).
Notation ZOdiv_mod_unique_full := Zquot_mod_unique_full (only parsing).
Notation ZOdiv_unique_full := Zquot_unique_full (only parsing).
Notation ZOdiv_unique := Zquot_unique (only parsing).
Notation ZOmod_unique_full := Zrem_unique_full (only parsing).
Notation ZOmod_unique := Zrem_unique (only parsing).

Notation ZOmod_0_l := Zrem_0_l (only parsing).
Notation ZOmod_0_r := Zrem_0_r (only parsing).
Notation ZOdiv_0_l := Zquot_0_l (only parsing).
Notation ZOdiv_0_r := Zquot_0_r (only parsing).
Notation ZOmod_1_r := Zrem_1_r (only parsing).
Notation ZOdiv_1_r := Zquot_1_r (only parsing).
Notation ZOdiv_1_l := Zquot_1_l (only parsing).
Notation ZOmod_1_l := Zrem_1_l (only parsing).
Notation ZO_div_same := Z_quot_same (only parsing).
Notation ZO_mod_same := Z_rem_same (only parsing).
Notation ZO_mod_mult := Z_rem_mult (only parsing).
Notation ZO_div_mult := Z_quot_mult (only parsing).

Notation ZO_div_pos := Z_quot_pos (only parsing).
Notation ZO_div_lt := Z_quot_lt (only parsing).
Notation ZOdiv_small := Zquot_small (only parsing).
Notation ZOmod_small := Zrem_small (only parsing).
Notation ZO_div_monotone := Z_quot_monotone (only parsing).
Notation ZO_mult_div_le := Z_mult_quot_le (only parsing).
Notation ZO_mult_div_ge := Z_mult_quot_ge (only parsing).
Definition ZO_div_exact_full_1 a b := proj1 (Z_quot_exact_full a b).
Definition ZO_div_exact_full_2 a b := proj2 (Z_quot_exact_full a b).
Notation ZOmod_le := Zrem_le (only parsing).
Notation ZOdiv_le_upper_bound := Zquot_le_upper_bound (only parsing).
Notation ZOdiv_lt_upper_bound := Zquot_lt_upper_bound (only parsing).
Notation ZOdiv_le_lower_bound := Zquot_le_lower_bound (only parsing).
Notation ZOdiv_sgn := Zquot_sgn (only parsing).

Notation ZO_mod_plus := Z_rem_plus (only parsing).
Notation ZO_div_plus := Z_quot_plus (only parsing).
Notation ZO_div_plus_l := Z_quot_plus_l (only parsing).
Notation ZOdiv_mult_cancel_r := Zquot_mult_cancel_r (only parsing).
Notation ZOdiv_mult_cancel_l := Zquot_mult_cancel_l (only parsing).
Notation ZOmult_mod_distr_l := Zmult_rem_distr_l (only parsing).
Notation ZOmult_mod_distr_r := Zmult_rem_distr_r (only parsing).
Notation ZOmod_mod := Zrem_rem (only parsing).
Notation ZOmult_mod := Zmult_rem (only parsing).
Notation ZOplus_mod := Zplus_rem (only parsing).
Notation ZOplus_mod_idemp_l := Zplus_rem_idemp_l (only parsing).
Notation ZOplus_mod_idemp_r := Zplus_rem_idemp_r (only parsing).
Notation ZOmult_mod_idemp_l := Zmult_rem_idemp_l (only parsing).
Notation ZOmult_mod_idemp_r := Zmult_rem_idemp_r (only parsing).
Notation ZOdiv_ZOdiv := Zquot_Zquot (only parsing).
Notation ZOdiv_mult_le := Zquot_mult_le (only parsing).
Notation ZOmod_divides := Zrem_divides (only parsing).

Notation ZOdiv_eucl_Zdiv_eucl_pos := Zquotrem_Zdiv_eucl_pos (only parsing).
Notation ZOdiv_Zdiv_pos := Zquot_Zdiv_pos (only parsing).
Notation ZOmod_Zmod_pos := Zrem_Zmod_pos (only parsing).
Notation ZOmod_Zmod_zero := Zrem_Zmod_zero (only parsing).
