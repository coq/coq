(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** * Binary Numerical Datatypes *)

Set Implicit Arguments.

(** [positive] is a datatype representing the strictly positive integers
   in a binary way. Starting from 1 (represented by [xH]), one can
   add a new least significant digit via [xO] (digit 0) or [xI] (digit 1).
   Numbers in [positive] can also be denoted using a decimal notation;
   e.g. [6%positive] abbreviates [xO (xI xH)] *)

Inductive positive : Set :=
  | xI : positive -> positive
  | xO : positive -> positive
  | xH : positive.

Delimit Scope positive_scope with positive.
Bind Scope positive_scope with positive.
Arguments xO _%positive.
Arguments xI _%positive.

(** [N] is a datatype representing natural numbers in a binary way,
    by extending the [positive] datatype with a zero.
    Numbers in [N] can also be denoted using a decimal notation;
    e.g. [6%N] abbreviates [Npos (xO (xI xH))] *)

Inductive N : Set :=
  | N0 : N
  | Npos : positive -> N.

Delimit Scope N_scope with N.
Bind Scope N_scope with N.
Arguments Npos _%positive.

(** [Z] is a datatype representing the integers in a binary way.
    An integer is either zero or a strictly positive number
    (coded as a [positive]) or a strictly negative number
    (whose opposite is stored as a [positive] value).
    Numbers in [Z] can also be denoted using a decimal notation;
    e.g. [(-6)%Z] abbreviates [Zneg (xO (xI xH))] *)

Inductive Z : Set :=
  | Z0 : Z
  | Zpos : positive -> Z
  | Zneg : positive -> Z.

Delimit Scope Z_scope with Z.
Bind Scope Z_scope with Z.
Arguments Zpos _%positive.
Arguments Zneg _%positive.

(** Parsing and Printing digits strings as types positive, N and Z *)

Fixpoint pos_of_pos' p' :=
  match p' with
  | x'H => xH
  | x'O p' => xO (pos_of_pos' p')
  | x'I p' => xI (pos_of_pos' p')
  end.

Definition pos_of_Z' z' :=
  match z' with
  | Z'0 => None
  | Z'pos p' => Some (pos_of_pos' p')
  | Z'neg p' => None
  end.

Fixpoint pos'_of_pos p :=
  match p with
  | xH => x'H
  | xO p => x'O (pos'_of_pos p)
  | xI p => x'I (pos'_of_pos p)
  end.

Definition Z_of_Z' z' :=
  match z' with
  | Z'0 => Z0
  | Z'pos p' => Zpos (pos_of_pos' p')
  | Z'neg p' => Zneg (pos_of_pos' p')
  end.

Definition Z'_of_Z z :=
  match z with
  | Z0 => Z'0
  | Zpos p => Z'pos (pos'_of_pos p)
  | Zneg p => Z'neg (pos'_of_pos p)
  end.

Definition Z'_of_pos p := Some (Z'pos (pos'_of_pos p)).

Definition some_Z_of_Z' z' := Some (Z_of_Z' z').
Definition some_Z'_of_Z z := Some (Z'_of_Z z).

Definition N_of_Z' z' :=
  match z' with
  | Z'0 => Some N0
  | Z'pos p' => Some (Npos (pos_of_pos' p'))
  | Z'neg p' => None
  end.

Definition Z'_of_N n :=
  match n with
  | N0 => Some Z'0
  | Npos p => Some (Z'pos (pos'_of_pos p))
  end.

Numeral Notation positive pos_of_Z' Z'_of_pos : positive_scope.
Numeral Notation N N_of_Z' Z'_of_N : N_scope.
Numeral Notation Z some_Z_of_Z' some_Z'_of_Z : Z_scope.
