(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
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

Notation Ndiv_eucl := N.div_eucl (compat "8.3").
Notation Ndiv := N.div (compat "8.3").
Notation Nmod := N.modulo (compat "8.3").

Notation Ndiv_eucl_correct := N.div_eucl_spec (compat "8.3").
Notation Ndiv_mod_eq := N.div_mod' (compat "8.3").
Notation Nmod_lt := N.mod_lt (compat "8.3").
