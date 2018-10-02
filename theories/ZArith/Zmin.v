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

Require Import BinInt Zcompare Zorder.

Local Open Scope Z_scope.

(** Definition [Z.min] is now [BinInt.Z.min]. *)

(** Exact compatibility *)

Notation Zmin_case := Z.min_case (compat "8.7").
Notation Zmin_case_strong := Z.min_case_strong (compat "8.7").
Notation Zle_min_l := Z.le_min_l (compat "8.7").
Notation Zle_min_r := Z.le_min_r (compat "8.7").
Notation Zmin_glb := Z.min_glb (compat "8.7").
Notation Zmin_glb_lt := Z.min_glb_lt (compat "8.7").
Notation Zle_min_compat_r := Z.min_le_compat_r (only parsing).
Notation Zle_min_compat_l := Z.min_le_compat_l (only parsing).
Notation Zmin_idempotent := Z.min_id (only parsing).
Notation Zmin_n_n := Z.min_id (only parsing).
Notation Zmin_comm := Z.min_comm (compat "8.7").
Notation Zmin_assoc := Z.min_assoc (compat "8.7").
Notation Zmin_irreducible_inf := Z.min_dec (only parsing).
Notation Zsucc_min_distr := Z.succ_min_distr (compat "8.7").
Notation Zmin_SS := Z.succ_min_distr (only parsing).
Notation Zplus_min_distr_r := Z.add_min_distr_r (only parsing).
Notation Zmin_plus := Z.add_min_distr_r (only parsing).
Notation Zpos_min := Pos2Z.inj_min (only parsing).

(** Slightly different lemmas *)

Lemma Zmin_spec x y :
  x <= y /\ Z.min x y = x  \/  x > y /\ Z.min x y = y.
Proof.
 Z.swap_greater. rewrite Z.min_comm. destruct (Z.min_spec y x); auto.
Qed.

Lemma Zmin_irreducible n m : Z.min n m = n \/ Z.min n m = m.
Proof. destruct (Z.min_dec n m); auto. Qed.

Notation Zmin_or := Zmin_irreducible (only parsing).

Lemma Zmin_le_prime_inf n m p : Z.min n m <= p -> {n <= p} + {m <= p}.
Proof. apply Z.min_case; auto. Qed.

Lemma Zpos_min_1 p : Z.min 1 (Zpos p) = 1.
Proof.
 now destruct p.
Qed.
