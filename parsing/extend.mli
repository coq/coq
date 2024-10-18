(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Entry keys for constr notations *)

type production_position =
  | BorderProd of Constrexpr.side * Gramlib.Gramext.g_assoc option
  | InternalProd

type production_level =
  | NextLevel
  | NumLevel of int
  | DefaultLevel (** Interpreted differently at the border or inside a rule *)

val production_level_eq : production_level -> production_level -> bool

(** User-level types used to tell how to parse or interpret of the non-terminal *)

type 'a constr_entry_key_gen =
  | ETIdent
  | ETName
  | ETGlobal
  | ETBigint
  | ETBinder of bool  (* open list of binders if true, closed list of binders otherwise *)
  | ETConstr of Constrexpr.notation_entry * Notation_term.notation_binder_kind option * 'a
  | ETPattern of bool * int option (* true = strict pattern, i.e. not a single variable *)

(** Entries level (left-hand side of grammar rules) *)

type constr_entry_key =
    (production_level * production_position) constr_entry_key_gen

val constr_entry_key_eq : constr_entry_key -> constr_entry_key -> bool

val constr_entry_key_eq_ignore_binder_kind : constr_entry_key -> constr_entry_key -> bool

(** Entries used in productions, vernac side (e.g. "x bigint" or "x ident") *)

type simple_constr_prod_entry_key =
    production_level constr_entry_key_gen

(** Entries used in productions (in right-hand-side of grammar rules), to parse non-terminals *)

type binder_target = ForBinder | ForTerm

type binder_entry_kind = ETBinderOpen | ETBinderClosed of constr_prod_entry_key option * (bool * string) list

and constr_prod_entry_key =
  | ETProdIdent           (* Parsed as an ident *)
  | ETProdName            (* Parsed as a name (ident or _) *)
  | ETProdGlobal          (* Parsed as a global reference *)
  | ETProdBigint          (* Parsed as an (unbounded) integer *)
  | ETProdOneBinder of bool (* Parsed as name, or name:type or 'pattern, possibly in closed form *)
  | ETProdConstr of Constrexpr.notation_entry * (production_level * production_position) (* Parsed as constr or pattern, or a subentry of those *)
  | ETProdPattern of int  (* Parsed as pattern as a binder (as subpart of a constr) *)
  | ETProdConstrList of Constrexpr.notation_entry * (production_level * production_position) * (bool * string) list (* Parsed as non-empty list of constr, or subentries of those *)
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
