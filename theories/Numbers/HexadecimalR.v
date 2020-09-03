(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * HexadecimalR

    Proofs that conversions between hexadecimal numbers and [R]
    are bijections. *)

Require Import Decimal DecimalFacts.
Require Import Hexadecimal HexadecimalFacts HexadecimalPos HexadecimalZ.
Require Import HexadecimalQ Rdefinitions.

Lemma of_to (q:IR) : forall d, to_hexadecimal q = Some d -> of_hexadecimal d = q.
Admitted.

Lemma to_of (d:hexadecimal) : to_hexadecimal (of_hexadecimal d) = Some (dnorm d).
Admitted.

(** Some consequences *)

Lemma to_hexadecimal_inj q q' :
  to_hexadecimal q <> None -> to_hexadecimal q = to_hexadecimal q' -> q = q'.
Proof.
intros Hnone EQ.
generalize (of_to q) (of_to q').
rewrite <-EQ.
revert Hnone; case to_hexadecimal; [|now simpl].
now intros d _ H1 H2; rewrite <-(H1 d eq_refl), <-(H2 d eq_refl).
Qed.

Lemma to_hexadecimal_surj d : exists q, to_hexadecimal q = Some (dnorm d).
Proof.
  exists (of_hexadecimal d). apply to_of.
Qed.

Lemma of_hexadecimal_dnorm d : of_hexadecimal (dnorm d) = of_hexadecimal d.
Proof. now apply to_hexadecimal_inj; rewrite !to_of; [|rewrite dnorm_involutive]. Qed.

Lemma of_inj d d' : of_hexadecimal d = of_hexadecimal d' -> dnorm d = dnorm d'.
Proof.
intro H.
apply (@f_equal _ _ (fun x => match x with Some x => x | _ => d end)
                (Some (dnorm d)) (Some (dnorm d'))).
now rewrite <- !to_of, H.
Qed.

Lemma of_iff d d' : of_hexadecimal d = of_hexadecimal d' <-> dnorm d = dnorm d'.
Proof.
split. apply of_inj. intros E. rewrite <- of_hexadecimal_dnorm, E.
apply of_hexadecimal_dnorm.
Qed.
