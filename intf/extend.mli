(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Entry keys for constr notations *)

type side = Left | Right

type gram_assoc = NonA | RightA | LeftA

type gram_position =
  | First
  | Last
  | Before of string
  | After of string
  | Level of string

type production_position =
  | BorderProd of side * gram_assoc option
  | InternalProd

type production_level =
  | NextLevel
  | NumLevel of int

type ('lev,'pos) constr_entry_key_gen =
  | ETName | ETReference | ETBigint
  | ETBinder of bool
  | ETConstr of ('lev * 'pos)
  | ETPattern
  | ETOther of string * string
  | ETConstrList of ('lev * 'pos) * Tok.t list
  | ETBinderList of bool * Tok.t list

(** Entries level (left-hand-side of grammar rules) *)

type constr_entry_key =
    (int,unit) constr_entry_key_gen

(** Entries used in productions (in right-hand-side of grammar rules) *)

type constr_prod_entry_key =
    (production_level,production_position) constr_entry_key_gen

(** Entries used in productions, vernac side (e.g. "x bigint" or "x ident") *)

type simple_constr_prod_entry_key =
    (production_level,unit) constr_entry_key_gen
