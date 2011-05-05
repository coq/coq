(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import BinPos BinNat BinInt Zbool Zcompare Zorder Zabs Znat.
Local Open Scope Z_scope.

Notation Zdiv_eucl_POS := Z.pos_div_eucl (only parsing).
Notation Zdiv_eucl := Z.div_eucl (only parsing).
Notation Zdiv := Z.div (only parsing).
Notation Zmod := Z.modulo (only parsing).
Notation Zquotrem := Z.quotrem (only parsing).
Notation Zquot := Z.quot (only parsing).
Notation Zrem := Z.rem (only parsing).

Lemma Zdiv_eucl_POS_eq : forall a b, 0 < b ->
  let (q, r) := Zdiv_eucl_POS a b in Zpos a = b * q + r.
Proof.
 intros a b Hb. generalize (Z.pos_div_eucl_eq a b Hb).
 destruct Z.pos_div_eucl. now rewrite Z.mul_comm.
Qed.

Notation Zdiv_eucl_eq := Z.div_eucl_eq (only parsing).
Notation Z_div_mod_eq_full := Z.div_mod (only parsing).
Notation Zmod_POS_bound := Z.pos_div_eucl_bound (only parsing).
Notation Zmod_pos_bound := Z.mod_pos_bound (only parsing).
Notation Zmod_neg_bound := Z.mod_neg_bound (only parsing).

Notation Zquotrem_eq := Z.quotrem_eq (only parsing).
Notation Z_quot_rem_eq := Z.quot_rem' (only parsing).
Notation Zrem_bound := Z.rem_bound_pos (only parsing).
Notation Zrem_opp_l := Z.rem_opp_l' (only parsing).
Notation Zrem_opp_r := Z.rem_opp_r' (only parsing).
