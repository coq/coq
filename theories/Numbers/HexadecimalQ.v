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

Lemma of_to (q:Q) : forall d, to_hexadecimal q = Some d -> of_hexadecimal d = q.
Admitted.

(* normalize without fractional part, for instance norme 0x1.2p-1 is 0x12e-5 *)
Definition hnorme (d:hexadecimal) : hexadecimal :=
  let '(i, f, e) :=
    match d with
    | Hexadecimal i f => (i, f, Decimal.Pos Decimal.Nil)
    | HexadecimalExp i f e => (i, f, e)
    end in
  let i := norm (app_int i f) in
  let e := (Z.of_int e - 4 * Z.of_nat (nb_digits f))%Z in
  match e with
  | Z0 => Hexadecimal i Nil
  | Zpos e => Hexadecimal (Pos.iter double i e) Nil
  | Zneg _ => HexadecimalExp i Nil (Decimal.norm (Z.to_int e))
  end.

Lemma hnorme_spec d :
  match hnorme d with
  | Hexadecimal i Nil => i = norm i
  | HexadecimalExp i Nil e =>
    i = norm i /\ e = Decimal.norm e /\ e <> Decimal.Pos Decimal.zero
  | _ => False
  end.
Admitted.

Lemma hnorme_invol d : hnorme (hnorme d) = hnorme d.
Admitted.

Lemma to_of (d:hexadecimal) :
  to_hexadecimal (of_hexadecimal d) = Some (hnorme d).
Admitted.

(** Some consequences *)

Lemma to_hexadecimal_inj q q' :
  to_hexadecimal q <> None -> to_hexadecimal q = to_hexadecimal q' -> q = q'.
Admitted.

Lemma to_hexadecimal_surj d : exists q, to_hexadecimal q = Some (hnorme d).
Admitted.

Lemma of_hexadecimal_hnorme d : of_hexadecimal (hnorme d) = of_hexadecimal d.
Admitted.

Lemma of_inj d d' :
  of_hexadecimal d = of_hexadecimal d' -> hnorme d = hnorme d'.
Admitted.

Lemma of_iff d d' :
  of_hexadecimal d = of_hexadecimal d' <-> hnorme d = hnorme d'.
Admitted.
