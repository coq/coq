(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Compatibility file for making Stdlib act similar to Stdlib v8.18 *)

(* Restore broken behavior of [zify] reported in COQBUG(https://github.com/coq/coq/issues/17936) *)
From Stdlib Require Import Arith BinInt BinNat Znat Nnat PreOmega.

#[local] Open Scope Z_scope.
Ltac Z.euclidean_division_equations_cleanup ::=
  repeat match goal with
         | [ H : ?x = ?x -> _ |- _ ] => specialize (H eq_refl)
         | [ H : ?x <> ?x -> _ |- _ ] => clear H
         | [ H : ?x < ?x -> _ |- _ ] => clear H
         | [ H : ?T -> _, H' : ?T |- _ ] => specialize (H H')
         | [ H : ?T -> _, H' : ~?T |- _ ] => clear H
         | [ H : ~?T -> _, H' : ?T |- _ ] => clear H
         | [ H : ?A -> ?x = ?x -> _ |- _ ] => specialize (fun a => H a eq_refl)
         | [ H : ?A -> ?x <> ?x -> _ |- _ ] => clear H
         | [ H : ?A -> ?x < ?x -> _ |- _ ] => clear H
         | [ H : ?A -> ?B -> _, H' : ?B |- _ ] => specialize (fun a => H a H')
         | [ H : ?A -> ?B -> _, H' : ~?B |- _ ] => clear H
         | [ H : ?A -> ~?B -> _, H' : ?B |- _ ] => clear H
         | [ H : 0 < ?x -> _, H' : ?x < 0 |- _ ] => clear H
         | [ H : ?x < 0 -> _, H' : 0 < ?x |- _ ] => clear H
         | [ H : ?A -> 0 < ?x -> _, H' : ?x < 0 |- _ ] => clear H
         | [ H : ?A -> ?x < 0 -> _, H' : 0 < ?x |- _ ] => clear H
         | [ H : 0 <= ?x -> _, H' : ?x < 0 |- _ ] => clear H
         | [ H : ?x <= 0 -> _, H' : 0 < ?x |- _ ] => clear H
         | [ H : ?A -> 0 <= ?x -> _, H' : ?x < 0 |- _ ] => clear H
         | [ H : ?A -> ?x <= 0 -> _, H' : 0 < ?x |- _ ] => clear H
         | [ H : 0 < ?x -> _, H' : ?x <= 0 |- _ ] => clear H
         | [ H : ?x < 0 -> _, H' : 0 <= ?x |- _ ] => clear H
         | [ H : ?A -> 0 < ?x -> _, H' : ?x <= 0 |- _ ] => clear H
         | [ H : ?A -> ?x < 0 -> _, H' : 0 <= ?x |- _ ] => clear H
         | [ H : 0 <= ?x -> _, H' : ?x <= 0 |- _ ] => specialize (fun pf => H (@Z.eq_le_incl 0 x (eq_sym pf)))
         | [ H : ?A -> 0 <= ?x -> _, H' : ?x <= 0 |- _ ] => specialize (fun a pf => H a (@Z.eq_le_incl 0 x (eq_sym pf)))
         | [ H : ?x <= 0 -> _, H' : 0 <= ?x |- _ ] => specialize (fun pf => H (@Z.eq_le_incl 0 x pf))
         | [ H : ?A -> ?x <= 0 -> _, H' : 0 <= ?x |- _ ] => specialize (fun a pf => H a (@Z.eq_le_incl x 0 pf))
         | [ H : ?x < ?y -> _, H' : ?x = ?y |- _ ] => clear H
         | [ H : ?x < ?y -> _, H' : ?y = ?x |- _ ] => clear H
         | [ H : ?A -> ?x < ?y -> _, H' : ?x = ?y |- _ ] => clear H
         | [ H : ?A -> ?x < ?y -> _, H' : ?y = ?x |- _ ] => clear H
         | [ H : ?x = ?y -> _, H' : ?x < ?y |- _ ] => clear H
         | [ H : ?x = ?y -> _, H' : ?y < ?x |- _ ] => clear H
         | [ H : ?A -> ?x = ?y -> _, H' : ?x < ?y |- _ ] => clear H
         | [ H : ?A -> ?x = ?y -> _, H' : ?y < ?x |- _ ] => clear H
         end.
