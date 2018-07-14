(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * Alternative Binary Numeral Notations *)

(** Faster but less safe parsers and printers of [positive], [N], [Z]. *)

(** By default, literals in types [positive], [N], [Z] are parsed and
    printed via the [Numeral Notation] command, by conversion from/to
    the [Decimal.int] representation. When working with numbers with
    thousands of digits and more, conversion from/to [Decimal.int] can
    become significantly slow. If that becomes a problem for your
    development, this file provides some alternative [Numeral
    Notation] commmands that use [Z] as bridge type. To enable these
    commands, just be sure to [Require] this file after other files
    defining numeral notations.

    Note: up to Coq 8.8, literals in types [positive], [N], [Z] were
    parsed and printed using a native ML library of arbitrary
    precision integers named bigint.ml. From 8.9, the default is to
    parse and print using a Coq library converting sequences of
    digits, hence reducing the amount of ML code to trust. But this
    method is slower. This file then gives access to the legacy
    method, trading efficiency against a larger ML trust base relying
    on bigint.ml. *)

Require Import BinNums.

(** [positive] *)

Definition pos_of_z z :=
  match z with
    | Zpos p => Some p
    | _ => None
  end.

Definition pos_to_z p := Zpos p.

Numeral Notation positive pos_of_z pos_to_z : positive_scope.

(** [N] *)

Definition n_of_z z :=
  match z with
    | Z0 => Some N0
    | Zpos p => Some (Npos p)
    | Zneg _ => None
  end.

Definition n_to_z n :=
 match n with
   | N0 => Z0
   | Npos p => Zpos p
 end.

Numeral Notation N n_of_z n_to_z : N_scope.

(** [Z] *)

Definition z_of_z (z:Z) := z.

Numeral Notation Z z_of_z z_of_z : Z_scope.
