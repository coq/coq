(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * DecimalQ

    Proofs that conversions between decimal numbers and [Q]
    are bijections. *)

Require Import Decimal DecimalFacts DecimalPos DecimalN DecimalZ QArith.

Lemma of_to (q:IQ) : forall d, to_decimal q = Some d -> of_decimal d = q.
Admitted.

Definition dnorm (d:decimal) : decimal :=
  let norm_i i f :=
    match i with
    | Pos i => Pos (unorm i)
    | Neg i => match nzhead (app i f) with Nil => Pos zero | _ => Neg (unorm i) end
    end in
  match d with
  | Decimal i f => Decimal (norm_i i f) f
  | DecimalExp i f e =>
    match norm e with
    | Pos zero => Decimal (norm_i i f) f
    | e => DecimalExp (norm_i i f) f e
    end
  end.

Lemma dnorm_spec_i d :
  let (i, f) :=
    match d with Decimal i f => (i, f) | DecimalExp i f _ => (i, f) end in
  let i' := match dnorm d with Decimal i _ => i | DecimalExp i _ _ => i end in
  match i with
  | Pos i => i' = Pos (unorm i)
  | Neg i =>
    (i' = Neg (unorm i) /\ (nzhead i <> Nil \/ nzhead f <> Nil))
    \/ (i' = Pos zero /\ (nzhead i = Nil /\ nzhead f = Nil))
  end.
Admitted.

Lemma dnorm_spec_f d :
  let f := match d with Decimal _ f => f | DecimalExp _ f _ => f end in
  let f' := match dnorm d with Decimal _ f => f | DecimalExp _ f _ => f end in
  f' = f.
Admitted.

Lemma dnorm_spec_e d :
  match d, dnorm d with
    | Decimal _ _, Decimal _ _ => True
    | DecimalExp _ _ e, Decimal _ _ => norm e = Pos zero
    | DecimalExp _ _ e, DecimalExp _ _ e' => e' = norm e /\ e' <> Pos zero
    | Decimal _ _, DecimalExp _ _ _ => False
  end.
Admitted.

Lemma dnorm_invol d : dnorm (dnorm d) = dnorm d.
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
Proof. now apply to_decimal_inj; rewrite !to_of; [|rewrite dnorm_invol]. Qed.

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
