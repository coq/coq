(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2011     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

open Util

(**********************************************************************)
(* General entry keys *)

(* This intermediate abstract representation of entries can           *)
(* both be reified into mlexpr for the ML extensions and              *)
(* dynamically interpreted as entries for the Coq level extensions    *)

type 'a prod_entry_key =
  | Alist1 of 'a prod_entry_key
  | Alist1sep of 'a prod_entry_key * string
  | Alist0 of 'a prod_entry_key
  | Alist0sep of 'a prod_entry_key * string
  | Aopt of 'a prod_entry_key
  | Amodifiers of 'a prod_entry_key
  | Aself
  | Anext
  | Atactic of int
  | Agram of 'a Gramext.g_entry
  | Aentry of string * string

(**********************************************************************)
(* Entry keys for constr notations                                    *)

type side = Left | Right

type production_position =
  | BorderProd of side * Gramext.g_assoc option
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
  | ETConstrList of ('lev * 'pos) * Token.pattern list
  | ETBinderList of bool * Token.pattern list

(* Entries level (left-hand-side of grammar rules) *)
type constr_entry_key =
    (int,unit) constr_entry_key_gen

(* Entries used in productions (in right-hand-side of grammar rules) *)
type constr_prod_entry_key =
    (production_level,production_position) constr_entry_key_gen

(* Entries used in productions, vernac side (e.g. "x bigint" or "x ident") *)
type simple_constr_prod_entry_key =
    (production_level,unit) constr_entry_key_gen
