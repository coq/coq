(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import BinNat.
Local Open Scope N_scope.

(** Obsolete file, see [BinNat] now,
    only compatibility notations remain here. *)

Definition Pdiv_eucl a b := N.pos_div_eucl a (Npos b).

Definition Pdiv_eucl_correct a b :
  let (q,r) := Pdiv_eucl a b in Npos a = q * Npos b + r
 := N.pos_div_eucl_spec a (Npos b).

Lemma Pdiv_eucl_remainder a b :
  snd (Pdiv_eucl a b) < Npos b.
Proof. now apply (N.pos_div_eucl_remainder a (Npos b)). Qed.

Notation Nmod := N.modulo (only parsing).

Notation Ndiv_eucl_correct := N.div_eucl_spec (only parsing).
Notation Ndiv_mod_eq := N.div_mod' (only parsing).
