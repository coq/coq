(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Loc
open Names
open Libnames
open Misctypes
open Decl_kinds

(** {6 Concrete syntax for terms } *)

(** [constr_expr] is the abstract syntax tree produced by the parser *)

type notation = string

type explicitation =
  | ExplByPos of int * identifier option
  | ExplByName of identifier

type binder_kind =
  | Default of binding_kind
  | Generalized of binding_kind * binding_kind * bool
      (** Inner binding, outer bindings, typeclass-specific flag
	 for implicit generalization of superclasses *)

type abstraction_kind = AbsLambda | AbsPi

type proj_flag = int option (** [Some n] = proj of the n-th visible argument *)

type prim_token = Numeral of Bigint.bigint | String of string

type raw_cases_pattern_expr =
  | RCPatAlias of Loc.t * raw_cases_pattern_expr * identifier
  | RCPatCstr of Loc.t * Globnames.global_reference
    * raw_cases_pattern_expr list * raw_cases_pattern_expr list
  (** [CPatCstr (_, Inl c, l1, l2)] represents (@c l1) l2 *)
  | RCPatAtom of Loc.t * identifier option
  | RCPatOr of Loc.t * raw_cases_pattern_expr list

type cases_pattern_expr =
  | CPatAlias of Loc.t * cases_pattern_expr * identifier
  | CPatCstr of Loc.t * reference
    * cases_pattern_expr list * cases_pattern_expr list
  (** [CPatCstr (_, Inl c, l1, l2)] represents (@c l1) l2 *)
  | CPatAtom of Loc.t * reference option
  | CPatOr of Loc.t * cases_pattern_expr list
  | CPatNotation of Loc.t * notation * cases_pattern_notation_substitution
    * cases_pattern_expr list (** CPatNotation (_, n, l1 ,l2) represents
				  (notation n applied with substitution l1)
				  applied to arguments l2 *)
  | CPatPrim of Loc.t * prim_token
  | CPatRecord of Loc.t * (reference * cases_pattern_expr) list
  | CPatDelimiters of Loc.t * string * cases_pattern_expr

and cases_pattern_notation_substitution =
    cases_pattern_expr list *     (** for constr subterms *)
    cases_pattern_expr list list  (** for recursive notations *)

type constr_expr =
  | CRef of reference
  | CFix of Loc.t * identifier located * fix_expr list
  | CCoFix of Loc.t * identifier located * cofix_expr list
  | CProdN of Loc.t * (name located list * binder_kind * constr_expr) list * constr_expr
  | CLambdaN of Loc.t * (name located list * binder_kind * constr_expr) list * constr_expr
  | CLetIn of Loc.t * name located * constr_expr * constr_expr
  | CAppExpl of Loc.t * (proj_flag * reference) * constr_expr list
  | CApp of Loc.t * (proj_flag * constr_expr) *
      (constr_expr * explicitation located option) list
  | CRecord of Loc.t * constr_expr option * (reference * constr_expr) list
  | CCases of Loc.t * case_style * constr_expr option *
      (constr_expr * (name located option * cases_pattern_expr option)) list *
      (Loc.t * cases_pattern_expr list located list * constr_expr) list
  | CLetTuple of Loc.t * name located list * (name located option * constr_expr option) *
      constr_expr * constr_expr
  | CIf of Loc.t * constr_expr * (name located option * constr_expr option)
      * constr_expr * constr_expr
  | CHole of Loc.t * Evar_kinds.t option
  | CPatVar of Loc.t * (bool * patvar)
  | CEvar of Loc.t * existential_key * constr_expr list option
  | CSort of Loc.t * glob_sort
  | CCast of Loc.t * constr_expr * constr_expr cast_type
  | CNotation of Loc.t * notation * constr_notation_substitution
  | CGeneralization of Loc.t * binding_kind * abstraction_kind option * constr_expr
  | CPrim of Loc.t * prim_token
  | CDelimiters of Loc.t * string * constr_expr

and fix_expr =
    identifier located * (identifier located option * recursion_order_expr) *
      local_binder list * constr_expr * constr_expr

and cofix_expr =
    identifier located * local_binder list * constr_expr * constr_expr

and recursion_order_expr =
  | CStructRec
  | CWfRec of constr_expr
  | CMeasureRec of constr_expr * constr_expr option (** measure, relation *)

(** Anonymous defs allowed ?? *)
and local_binder =
  | LocalRawDef of name located * constr_expr
  | LocalRawAssum of name located list * binder_kind * constr_expr

and constr_notation_substitution =
    constr_expr list *      (** for constr subterms *)
    constr_expr list list * (** for recursive notations *)
    local_binder list list (** for binders subexpressions *)

type typeclass_constraint = name located * binding_kind * constr_expr

and typeclass_context = typeclass_constraint list

type constr_pattern_expr = constr_expr

(** Concrete syntax for modules and module types *)

type with_declaration_ast =
  | CWith_Module of identifier list located * qualid located
  | CWith_Definition of identifier list located * constr_expr

type module_ast =
  | CMident of qualid located
  | CMapply of Loc.t * module_ast * module_ast
  | CMwith of Loc.t * module_ast * with_declaration_ast
