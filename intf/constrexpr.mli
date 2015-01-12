(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
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
  | ExplByPos of int * Id.t option
  | ExplByName of Id.t

type binder_kind =
  | Default of binding_kind
  | Generalized of binding_kind * binding_kind * bool
      (** Inner binding, outer bindings, typeclass-specific flag
	 for implicit generalization of superclasses *)

type abstraction_kind = AbsLambda | AbsPi

type proj_flag = int option (** [Some n] = proj of the n-th visible argument *)

type prim_token = Numeral of Bigint.bigint | String of string

type raw_cases_pattern_expr =
  | RCPatAlias of Loc.t * raw_cases_pattern_expr * Id.t
  | RCPatCstr of Loc.t * Globnames.global_reference
    * raw_cases_pattern_expr list * raw_cases_pattern_expr list
  (** [CPatCstr (_, Inl c, l1, l2)] represents (@c l1) l2 *)
  | RCPatAtom of Loc.t * Id.t option
  | RCPatOr of Loc.t * raw_cases_pattern_expr list

type cases_pattern_expr =
  | CPatAlias of Loc.t * cases_pattern_expr * Id.t
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

type instance_expr = Misctypes.glob_level list

type constr_expr =
  | CRef of reference * instance_expr option
  | CFix of Loc.t * Id.t located * fix_expr list
  | CCoFix of Loc.t * Id.t located * cofix_expr list
  | CProdN of Loc.t * binder_expr list * constr_expr
  | CLambdaN of Loc.t * binder_expr list * constr_expr
  | CLetIn of Loc.t * Name.t located * constr_expr * constr_expr
  | CAppExpl of Loc.t * (proj_flag * reference * instance_expr option) * constr_expr list
  | CApp of Loc.t * (proj_flag * constr_expr) *
      (constr_expr * explicitation located option) list
  | CRecord of Loc.t * constr_expr option * (reference * constr_expr) list
  | CCases of Loc.t * case_style * constr_expr option *
      case_expr list * branch_expr list
  | CLetTuple of Loc.t * Name.t located list * (Name.t located option * constr_expr option) *
      constr_expr * constr_expr
  | CIf of Loc.t * constr_expr * (Name.t located option * constr_expr option)
      * constr_expr * constr_expr
  | CHole of Loc.t * Evar_kinds.t option * intro_pattern_naming_expr * Genarg.raw_generic_argument option
  | CPatVar of Loc.t * patvar
  | CEvar of Loc.t * Glob_term.existential_name * (Id.t * constr_expr) list
  | CSort of Loc.t * glob_sort
  | CCast of Loc.t * constr_expr * constr_expr cast_type
  | CNotation of Loc.t * notation * constr_notation_substitution
  | CGeneralization of Loc.t * binding_kind * abstraction_kind option * constr_expr
  | CPrim of Loc.t * prim_token
  | CDelimiters of Loc.t * string * constr_expr

and case_expr =
  constr_expr * (Name.t located option * cases_pattern_expr option)

and branch_expr =
  Loc.t * cases_pattern_expr list located list * constr_expr

and binder_expr =
  Name.t located list * binder_kind * constr_expr

and fix_expr =
    Id.t located * (Id.t located option * recursion_order_expr) *
      local_binder list * constr_expr * constr_expr

and cofix_expr =
    Id.t located * local_binder list * constr_expr * constr_expr

and recursion_order_expr =
  | CStructRec
  | CWfRec of constr_expr
  | CMeasureRec of constr_expr * constr_expr option (** measure, relation *)

(** Anonymous defs allowed ?? *)
and local_binder =
  | LocalRawDef of Name.t located * constr_expr
  | LocalRawAssum of Name.t located list * binder_kind * constr_expr

and constr_notation_substitution =
    constr_expr list *      (** for constr subterms *)
    constr_expr list list * (** for recursive notations *)
    local_binder list list (** for binders subexpressions *)

type typeclass_constraint = Name.t located * binding_kind * constr_expr

and typeclass_context = typeclass_constraint list

type constr_pattern_expr = constr_expr

(** Concrete syntax for modules and module types *)

type with_declaration_ast =
  | CWith_Module of Id.t list located * qualid located
  | CWith_Definition of Id.t list located * constr_expr

type module_ast =
  | CMident of qualid located
  | CMapply of Loc.t * module_ast * module_ast
  | CMwith of Loc.t * module_ast * with_declaration_ast
