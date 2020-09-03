(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * HexadecimalQ

    Proofs that conversions between hexadecimal numbers and [Q]
    are bijections. *)

Require Import Decimal DecimalFacts DecimalPos DecimalN DecimalZ.
Require Import Hexadecimal HexadecimalFacts HexadecimalPos HexadecimalN HexadecimalZ QArith.

Lemma of_to (q:IQ) : forall d, to_hexadecimal q = Some d -> of_hexadecimal d = q.
Admitted.

Definition dnorm (d:hexadecimal) : hexadecimal :=
  let norm_i i f :=
    match i with
    | Pos i => Pos (unorm i)
    | Neg i => match nzhead (app i f) with Nil => Pos zero | _ => Neg (unorm i) end
    end in
  match d with
  | Hexadecimal i f => Hexadecimal (norm_i i f) f
  | HexadecimalExp i f e =>
    match Decimal.norm e with
    | Decimal.Pos Decimal.zero => Hexadecimal (norm_i i f) f
    | e => HexadecimalExp (norm_i i f) f e
    end
  end.

Lemma dnorm_spec_i d :
  let (i, f) :=
    match d with Hexadecimal i f => (i, f) | HexadecimalExp i f _ => (i, f) end in
  let i' := match dnorm d with Hexadecimal i _ => i | HexadecimalExp i _ _ => i end in
  match i with
  | Pos i => i' = Pos (unorm i)
  | Neg i =>
    (i' = Neg (unorm i) /\ (nzhead i <> Nil \/ nzhead f <> Nil))
    \/ (i' = Pos zero /\ (nzhead i = Nil /\ nzhead f = Nil))
  end.
Admitted.

Lemma dnorm_spec_f d :
  let f := match d with Hexadecimal _ f => f | HexadecimalExp _ f _ => f end in
  let f' := match dnorm d with Hexadecimal _ f => f | HexadecimalExp _ f _ => f end in
  f' = f.
Admitted.

Lemma dnorm_spec_e d :
  match d, dnorm d with
    | Hexadecimal _ _, Hexadecimal _ _ => True
    | HexadecimalExp _ _ e, Hexadecimal _ _ =>
      Decimal.norm e = Decimal.Pos Decimal.zero
    | HexadecimalExp _ _ e, HexadecimalExp _ _ e' =>
      e' = Decimal.norm e /\ e' <> Decimal.Pos Decimal.zero
    | Hexadecimal _ _, HexadecimalExp _ _ _ => False
  end.
Admitted.

Lemma dnorm_invol d : dnorm (dnorm d) = dnorm d.
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
Proof. now apply to_hexadecimal_inj; rewrite !to_of; [|rewrite dnorm_invol]. Qed.

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
