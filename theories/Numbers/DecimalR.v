(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * DecimalR

    Proofs that conversions between decimal numbers and [R]
    are bijections. *)

Require Import Decimal DecimalFacts DecimalPos DecimalZ DecimalQ Rdefinitions.

Lemma of_to (q:IR) : forall d, to_decimal q = Some d -> of_decimal d = q.
Admitted.

Lemma to_of (d:decimal) : to_decimal (of_decimal d) = Some (dnorm d).
Admitted.

(** Some consequences *)

Lemma to_decimal_inj q q' :
  to_decimal q <> None -> to_decimal q = to_decimal q' -> q = q'.
Proof.
intros Hnone EQ.
generalize (of_to q) (of_to q').
rewrite <-EQ.
revert Hnone; case to_decimal; [|now simpl].
now intros d _ H1 H2; rewrite <-(H1 d eq_refl), <-(H2 d eq_refl).
Qed.

Lemma to_decimal_surj d : exists q, to_decimal q = Some (dnorm d).
Proof.
  exists (of_decimal d). apply to_of.
Qed.

Lemma of_decimal_dnorm d : of_decimal (dnorm d) = of_decimal d.
Proof. now apply to_decimal_inj; rewrite !to_of; [|rewrite dnorm_involutive]. Qed.

Lemma of_inj d d' : of_decimal d = of_decimal d' -> dnorm d = dnorm d'.
Proof.
intro H.
apply (@f_equal _ _ (fun x => match x with Some x => x | _ => d end)
                (Some (dnorm d)) (Some (dnorm d'))).
now rewrite <- !to_of, H.
Qed.

Lemma of_iff d d' : of_decimal d = of_decimal d' <-> dnorm d = dnorm d'.
Proof.
split. apply of_inj. intros E. rewrite <- of_decimal_dnorm, E.
apply of_decimal_dnorm.
Qed.
