(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** THIS FILE IS DEPRECATED. *)

Require Import BinInt Zcompare Zorder.

Local Open Scope Z_scope.

(** Definition [Z.min] is now [BinInt.Z.min]. *)

(** Exact compatibility *)

Notation Zmin_case := Z.min_case (compat "8.3").
Notation Zmin_case_strong := Z.min_case_strong (compat "8.3").
Notation Zle_min_l := Z.le_min_l (compat "8.3").
Notation Zle_min_r := Z.le_min_r (compat "8.3").
Notation Zmin_glb := Z.min_glb (compat "8.3").
Notation Zmin_glb_lt := Z.min_glb_lt (compat "8.3").
Notation Zle_min_compat_r := Z.min_le_compat_r (compat "8.3").
Notation Zle_min_compat_l := Z.min_le_compat_l (compat "8.3").
Notation Zmin_idempotent := Z.min_id (compat "8.3").
Notation Zmin_n_n := Z.min_id (compat "8.3").
Notation Zmin_comm := Z.min_comm (compat "8.3").
Notation Zmin_assoc := Z.min_assoc (compat "8.3").
Notation Zmin_irreducible_inf := Z.min_dec (compat "8.3").
Notation Zsucc_min_distr := Z.succ_min_distr (compat "8.3").
Notation Zmin_SS := Z.succ_min_distr (compat "8.3").
Notation Zplus_min_distr_r := Z.add_min_distr_r (compat "8.3").
Notation Zmin_plus := Z.add_min_distr_r (compat "8.3").
Notation Zpos_min := Pos2Z.inj_min (compat "8.3").

(** Slightly different lemmas *)

Lemma Zmin_spec x y :
  x <= y /\ Z.min x y = x  \/  x > y /\ Z.min x y = y.
Proof.
 Z.swap_greater. rewrite Z.min_comm. destruct (Z.min_spec y x); auto.
Qed.

Lemma Zmin_irreducible n m : Z.min n m = n \/ Z.min n m = m.
Proof. destruct (Z.min_dec n m); auto. Qed.

Notation Zmin_or := Zmin_irreducible (compat "8.3").

Lemma Zmin_le_prime_inf n m p : Z.min n m <= p -> {n <= p} + {m <= p}.
Proof. apply Z.min_case; auto. Qed.

Lemma Zpos_min_1 p : Z.min 1 (Zpos p) = 1.
Proof.
 now destruct p.
Qed.
