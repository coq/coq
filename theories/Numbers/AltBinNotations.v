(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** * Alternative Binary Numeral Notations *)

(** Faster but less safe parsers and printers of [positive], [N], [Z]. *)

(** Nowadays, literals in types [positive], [N], [Z] are parsed and
    printed via the [Numeral Notation] command, by conversion from/to
    the [Decimal.int] representation. This way, we do not need any
    ML library of arbitrary precision integers (bigint.ml), hence
    reducing the amount of ML code to trust during parsing and printing.
    But this new method is slower than the older code, by a margin that
    may become significant for literals of thousands of digits and more.
    If that becomes a problem for your development, this file provides
    some alternative [Numeral Notation] commmands that use [Z] as
    bridge type : it hence relies on the bigint.ml library, the efficiency
    should be almost the one of the legacy code, at the expense of a
    larger ML trust base. To enable these commands, just be sure to
    [Require] this file after the other files of

    Please note anyway that literals above 10000 digits in [positive],
    [N], [Z] will end up triggering Stack Overlow in various parts of
    the Coq engine (type-checker, reduction, etc). So consider using
    [BigN] or [BigZ] instead...
*)

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
