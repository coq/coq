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

(** {5 Type-safe grammar extension} *)

type ('self, 'a) symbol =
| Atoken : Tok.t -> ('self, Tok.t) symbol
| Alist1 : ('self, 'a) symbol -> ('self, 'a list) symbol
| Alist1sep : ('self, 'a) symbol * string -> ('self, 'a list) symbol
| Alist0 : ('self, 'a) symbol -> ('self, 'a list) symbol
| Alist0sep : ('self, 'a) symbol * string -> ('self, 'a list) symbol
| Aopt : ('self, 'a) symbol -> ('self, 'a option) symbol
| Amodifiers : ('self, 'a) symbol -> ('self, 'a list) symbol
| Aself : ('self, 'self) symbol
| Anext : ('self, 'self) symbol
| Aentry : 'a Entry.t -> ('self, 'a) symbol
| Aentryl : 'a Entry.t * int -> ('self, 'a) symbol

type ('self, _, 'r) rule =
| Stop : ('self, 'r, 'r) rule
| Next : ('self, 'a, 'r) rule * ('self, 'b) symbol -> ('self, 'b -> 'a, 'r) rule

type 'a production_rule =
| Rule : ('a, 'act, Loc.t -> 'a) rule * 'act -> 'a production_rule

type 'a single_extend_statment =
  string option *
  (** Level *)
  gram_assoc option *
  (** Associativity *)
  'a production_rule list
  (** Symbol list with the interpretation function *)

type 'a extend_statment =
  gram_position option *
  'a single_extend_statment list
