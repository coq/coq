(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

open Util

(**********************************************************************)
(* constr entry keys                                                  *)

type side = Left | Right

type production_position =
  | BorderProd of side * Gramext.g_assoc option  (* true=left; false=right *)
  | InternalProd

type production_level =
  | NextLevel
  | NumLevel of int

type ('lev,'pos) constr_entry_key =
  | ETIdent | ETReference | ETBigint
  | ETConstr of ('lev * 'pos)
  | ETPattern
  | ETOther of string * string
  | ETConstrList of ('lev * 'pos) * Token.pattern list

type constr_production_entry =
    (production_level,production_position) constr_entry_key
type constr_entry =
    (int,unit) constr_entry_key
type simple_constr_production_entry =
    (production_level,unit) constr_entry_key

(**********************************************************************)
(* syntax modifiers                                                   *)

type syntax_modifier =
  | SetItemLevel of string list * production_level
  | SetLevel of int
  | SetAssoc of Gramext.g_assoc
  | SetEntryType of string * simple_constr_production_entry
  | SetOnlyParsing
  | SetFormat of string located

