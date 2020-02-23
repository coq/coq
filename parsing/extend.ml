(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Entry keys for constr notations *)

type 'a entry = 'a Gramlib.Grammar.GMake(CLexer.Lexer).Entry.e

type side = Left | Right

type production_position =
  | BorderProd of side * Gramlib.Gramext.g_assoc option
  | InternalProd

type production_level =
  | NextLevel
  | NumLevel of int
  | DefaultLevel (** Interpreted differently at the border or inside a rule *)

(** User-level types used to tell how to parse or interpret of the non-terminal *)

type 'a constr_entry_key_gen =
  | ETIdent
  | ETGlobal
  | ETBigint
  | ETString
  | ETBinder of bool  (* open list of binders if true, closed list of binders otherwise *)
  | ETConstr of Constrexpr.notation_entry * Notation_term.constr_as_binder_kind option * 'a
  | ETPattern of bool * int option (* true = strict pattern, i.e. not a single variable *)

(** Entries level (left-hand side of grammar rules) *)

type constr_entry_key =
    (production_level * production_position) constr_entry_key_gen

(** Entries used in productions, vernac side (e.g. "x bigint" or "x ident") *)

type simple_constr_prod_entry_key =
    production_level constr_entry_key_gen

(** Entries used in productions (in right-hand-side of grammar rules), to parse non-terminals *)

type binder_entry_kind = ETBinderOpen | ETBinderClosed of string Tok.p list

type binder_target = ForBinder | ForTerm

type constr_prod_entry_key =
  | ETProdName            (* Parsed as a name (ident or _) *)
  | ETProdReference       (* Parsed as a global reference *)
  | ETProdBigint          (* Parsed as an (unbounded) integer *)
  | ETProdString          (* Parsed as a string *)
  | ETProdConstr of Constrexpr.notation_entry * (production_level * production_position) (* Parsed as constr or pattern, or a subentry of those *)
  | ETProdPattern of int  (* Parsed as pattern as a binder (as subpart of a constr) *)
  | ETProdConstrList of Constrexpr.notation_entry * (production_level * production_position) * string Tok.p list (* Parsed as non-empty list of constr, or subentries of those *)
  | ETProdBinderList of binder_entry_kind  (* Parsed as non-empty list of local binders *)

(** {5 AST for user-provided entries} *)

type 'a user_symbol =
| Ulist1 of 'a user_symbol
| Ulist1sep of 'a user_symbol * string
| Ulist0 of 'a user_symbol
| Ulist0sep of 'a user_symbol * string
| Uopt of 'a user_symbol
| Uentry of 'a
| Uentryl of 'a * int

type ('a,'b,'c) ty_user_symbol =
| TUlist1 : ('a,'b,'c) ty_user_symbol -> ('a list,'b list,'c list) ty_user_symbol
| TUlist1sep : ('a,'b,'c) ty_user_symbol * string -> ('a list,'b list,'c list) ty_user_symbol
| TUlist0 : ('a,'b,'c) ty_user_symbol -> ('a list,'b list,'c list) ty_user_symbol
| TUlist0sep : ('a,'b,'c) ty_user_symbol * string -> ('a list,'b list,'c list) ty_user_symbol
| TUopt : ('a,'b,'c) ty_user_symbol -> ('a option, 'b option, 'c option) ty_user_symbol
| TUentry : ('a, 'b, 'c) Genarg.ArgT.tag -> ('a,'b,'c) ty_user_symbol
| TUentryl : ('a, 'b, 'c) Genarg.ArgT.tag * int -> ('a,'b,'c) ty_user_symbol

(** {5 Type-safe grammar extension} *)

(* Should be merged with gramlib's implementation *)

type norec = Gramlib.Grammar.ty_norec
type mayrec = Gramlib.Grammar.ty_mayrec

type ('self, 'trec, 'a) symbol =
| Atoken : 'c Tok.p -> ('self, norec, 'c) symbol
| Alist1 : ('self, 'trec, 'a) symbol -> ('self, 'trec, 'a list) symbol
| Alist1sep : ('self, 'trec, 'a) symbol * ('self, norec, _) symbol
              -> ('self, 'trec, 'a list) symbol
| Alist0 : ('self, 'trec, 'a) symbol -> ('self, 'trec, 'a list) symbol
| Alist0sep : ('self, 'trec, 'a) symbol * ('self, norec, _) symbol
              -> ('self, 'trec, 'a list) symbol
| Aopt : ('self, 'trec, 'a) symbol -> ('self, 'trec, 'a option) symbol
| Aself : ('self, mayrec, 'self) symbol
| Anext : ('self, mayrec, 'self) symbol
| Aentry : 'a entry -> ('self, norec, 'a) symbol
| Aentryl : 'a entry * string -> ('self, norec, 'a) symbol
| Arules : 'a rules list -> ('self, norec, 'a) symbol

and ('self, 'trec, _, 'r) rule =
| Stop : ('self, norec, 'r, 'r) rule
| Next : ('self, _, 'a, 'r) rule * ('self, _, 'b) symbol -> ('self, mayrec, 'b -> 'a, 'r) rule
| NextNoRec : ('self, norec, 'a, 'r) rule * ('self, norec, 'b) symbol -> ('self, norec, 'b -> 'a, 'r) rule

and 'a rules =
| Rules : (_, norec, 'act, Loc.t -> 'a) rule * 'act -> 'a rules

type 'a production_rule =
| Rule : ('a, _, 'act, Loc.t -> 'a) rule * 'act -> 'a production_rule
