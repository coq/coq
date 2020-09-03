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

(* normalize without fractional part, for instance norme 12.3e-1 is 123e-2 *)
Definition dnorme (d:decimal) : decimal :=
  let '(i, f, e) :=
    match d with
    | Decimal i f => (i, f, Pos Nil)
    | DecimalExp i f e => (i, f, e)
    end in
  let i := norm (app_int i f) in
  let e := norm (Z.to_int (Z.of_int e - Z.of_nat (nb_digits f))) in
  match e with
  | Pos zero => Decimal i Nil
  | _ => DecimalExp i Nil e
  end.

(* normalize without exponent part, for instance norme 12.3e-1 is 1.23 *)
Definition dnormf (d:decimal) : decimal :=
  match dnorme d with
  | Decimal i _ => Decimal i Nil
  | DecimalExp i _ e =>
    match Z.of_int e with
    | Z0 => Decimal i Nil
    | Zpos e => Decimal (norm (app_int i (Pos.iter D0 Nil e))) Nil
    | Zneg e =>
      let ne := Pos.to_nat e in
      let ai := match i with Pos d | Neg d => d end in
      let ni := nb_digits ai in
      if ne <? ni then
        Decimal (del_tail_int ne i) (del_head (ni - ne) ai)
      else
        let z := match i with Pos _ => Pos zero | Neg _ => Neg zero end in
        Decimal z (Nat.iter (ne - ni) D0 ai)
    end
  end.

Lemma dnorme_spec d :
  match dnorme d with
  | Decimal i Nil => i = norm i
  | DecimalExp i Nil e => i = norm i /\ e = norm e /\ e <> Pos zero
  | _ => False
  end.
Admitted.

Lemma dnormf_spec d :
  match dnormf d with
  | Decimal i f => i = Neg zero \/ i = norm i
  | _ => False
  end.
Admitted.

Lemma dnorme_invol d : dnorme (dnorme d) = dnorme d.
Admitted.

Lemma dnormf_invol d : dnormf (dnormf d) = dnormf d.
Admitted.

Lemma to_of (d:decimal) :
  to_decimal (of_decimal d) = Some (dnorme d)
  \/ to_decimal (of_decimal d) = Some (dnormf d).
Admitted.

(** Some consequences *)

Lemma to_decimal_inj q q' :
  to_decimal q <> None -> to_decimal q = to_decimal q' -> q = q'.
Admitted.

Lemma to_decimal_surj d :
  exists q, to_decimal q = Some (dnorme d) \/ to_decimal q = Some (dnormf d).
Admitted.

Lemma of_decimal_dnorme d : of_decimal (dnorme d) = of_decimal d.
Admitted.

Lemma of_decimal_dnormf d : of_decimal (dnormf d) = of_decimal d.
Admitted.
