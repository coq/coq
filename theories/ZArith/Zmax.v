(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** THIS FILE IS DEPRECATED. *)

Require Export BinInt Zcompare Zorder.

Local Open Scope Z_scope.

(** Definition [Z.max] is now [BinInt.Z.max]. *)

(** Exact compatibility *)

Notation Zmax_case := Z.max_case (compat "8.7").
Notation Zmax_case_strong := Z.max_case_strong (compat "8.7").
Notation Zmax_right := Z.max_r (only parsing).
Notation Zle_max_l := Z.le_max_l (compat "8.7").
Notation Zle_max_r := Z.le_max_r (compat "8.7").
Notation Zmax_lub := Z.max_lub (compat "8.7").
Notation Zmax_lub_lt := Z.max_lub_lt (compat "8.7").
Notation Zle_max_compat_r := Z.max_le_compat_r (only parsing).
Notation Zle_max_compat_l := Z.max_le_compat_l (only parsing).
Notation Zmax_idempotent := Z.max_id (only parsing).
Notation Zmax_n_n := Z.max_id (only parsing).
Notation Zmax_comm := Z.max_comm (compat "8.7").
Notation Zmax_assoc := Z.max_assoc (compat "8.7").
Notation Zmax_irreducible_dec := Z.max_dec (only parsing).
Notation Zmax_le_prime := Z.max_le (only parsing).
Notation Zsucc_max_distr := Z.succ_max_distr (compat "8.7").
Notation Zmax_SS := Z.succ_max_distr (only parsing).
Notation Zplus_max_distr_l := Z.add_max_distr_l (only parsing).
Notation Zplus_max_distr_r := Z.add_max_distr_r (only parsing).
Notation Zmax_plus := Z.add_max_distr_r (only parsing).
Notation Zmax1 := Z.le_max_l (only parsing).
Notation Zmax2 := Z.le_max_r (only parsing).
Notation Zmax_irreducible_inf := Z.max_dec (only parsing).
Notation Zmax_le_prime_inf := Z.max_le (only parsing).
Notation Zpos_max := Pos2Z.inj_max (only parsing).
Notation Zpos_minus := Pos2Z.inj_sub_max (only parsing).

(** Slightly different lemmas *)

Lemma Zmax_spec x y :
  x >= y /\ Z.max x y = x  \/ x < y /\ Z.max x y = y.
Proof.
 Z.swap_greater. destruct (Z.max_spec x y); auto.
Qed.

Lemma Zmax_left n m : n>=m -> Z.max n m = n.
Proof. Z.swap_greater. apply Z.max_l. Qed.

Lemma Zpos_max_1 p : Z.max 1 (Z.pos p) = Z.pos p.
Proof.
 now destruct p.
Qed.
