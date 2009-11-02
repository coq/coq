(* -*- coding: utf-8 -*- *)
(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

(** Contributed by Laurent Théry (INRIA);
    Adapted to Coq V8 by the Coq Development Team *)

Require Import Bool.
Require Import BinPos.
Declare ML Module "ascii_syntax_plugin".

(** * Definition of ascii characters *)

(** Definition of ascii character as a 8 bits constructor *)

Inductive ascii : Set := Ascii (_ _ _ _ _ _ _ _ : bool).

Delimit Scope char_scope with char.
Bind Scope char_scope with ascii.

Definition zero := Ascii false false false false false false false false.

Definition one := Ascii true false false false false false false false.

Definition app1 (f : bool -> bool) (a : ascii) :=
  match a with
    | Ascii a1 a2 a3 a4 a5 a6 a7 a8 =>
      Ascii (f a1) (f a2) (f a3) (f a4) (f a5) (f a6) (f a7) (f a8)
  end.

Definition app2 (f : bool -> bool -> bool) (a b : ascii) :=
  match a, b with
    | Ascii a1 a2 a3 a4 a5 a6 a7 a8, Ascii b1 b2 b3 b4 b5 b6 b7 b8 =>
      Ascii (f a1 b1) (f a2 b2) (f a3 b3) (f a4 b4)
      (f a5 b5) (f a6 b6) (f a7 b7) (f a8 b8)
  end.

Definition shift (c : bool) (a : ascii) :=
  match a with
    | Ascii a1 a2 a3 a4 a5 a6 a7 a8 => Ascii c a1 a2 a3 a4 a5 a6 a7
  end.

(** Definition of a decidable function that is effective *)

Definition ascii_dec : forall a b : ascii, {a = b} + {a <> b}.
  decide equality; apply bool_dec.
Defined.

(** * Conversion between natural numbers modulo 256 and ascii characters *)

(** Auxillary function that turns a positive into an ascii by
   looking at the last n bits, ie z mod 2^n *)

Fixpoint ascii_of_pos_aux (res acc : ascii) (z : positive)
  (n : nat) : ascii :=
  match n with
    | O => res
    | S n1 =>
      match z with
	| xH => app2 orb res acc
	| xI z' => ascii_of_pos_aux (app2 orb res acc) (shift false acc) z' n1
	| xO z' => ascii_of_pos_aux res (shift false acc) z' n1
      end
  end.


(** Function that turns a positive into an ascii by
    looking at the last 8 bits, ie a mod 8 *)

Definition ascii_of_pos (a : positive) := ascii_of_pos_aux zero one a 8.

(** Function that turns a Peano number into an ascii by converting it
    to positive *)

Definition ascii_of_nat (a : nat) :=
  match a with
    | O => zero
    | S a' => ascii_of_pos (P_of_succ_nat a')
  end.

(** The opposite function *)

Definition nat_of_ascii (a : ascii) : nat :=
  let (a1, a2, a3, a4, a5, a6, a7, a8) := a in
    2 *
    (2 *
      (2 *
        (2 *
          (2 *
            (2 *
              (2 * (if a8 then 1 else 0)
		+ (if a7 then 1 else 0))
              + (if a6 then 1 else 0))
            + (if a5 then 1 else 0))
          + (if a4 then 1 else 0))
        + (if a3 then 1 else 0))
      + (if a2 then 1 else 0))
    + (if a1 then 1 else 0).

Theorem ascii_nat_embedding :
  forall a : ascii, ascii_of_nat (nat_of_ascii a) = a.
Proof.
  destruct a as [[|][|][|][|][|][|][|][|]]; compute; reflexivity.
Qed.

(** * Concrete syntax *)

(**
  Ascii characters can be represented in scope char_scope as follows:
  - ["c"]   represents itself if c is a character of code < 128,
  - [""""]  is an exception: it represents the ascii character 34
            (double quote),
  - ["nnn"] represents the ascii character of decimal code nnn.

  For instance, both ["065"] and ["A"] denote the character `uppercase
  A', and both ["034"] and [""""] denote the character `double quote'.

  Notice that the ascii characters of code >= 128 do not denote
  stand-alone utf8 characters so that only the notation "nnn" is
  available for them (unless your terminal is able to represent them,
  which is typically not the case in coqide).
*)

Open Local Scope char_scope.

Example Space := " ".
Example DoubleQuote := """".
Example Beep := "007".
