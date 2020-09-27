(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Libnames

(** {6 Concrete syntax for terms } *)

(** [constr_expr] is the abstract syntax tree produced by the parser *)
type universe_decl_expr = (lident list, Glob_term.glob_constraint list) UState.gen_universe_decl

type ident_decl = lident * universe_decl_expr option
type name_decl = lname * universe_decl_expr option

type notation_with_optional_scope = LastLonelyNotation | NotationInScope of string

type entry_level = int
type entry_relative_level = LevelLt of entry_level | LevelLe of entry_level | LevelSome

type notation_entry = InConstrEntry | InCustomEntry of string
type notation_entry_level = InConstrEntrySomeLevel | InCustomEntryLevel of string * entry_level
type notation_key = string

(* A notation associated to a given parsing rule *)
type notation = notation_entry * notation_key

(* A notation associated to a given interpretation *)
type specific_notation = notation_with_optional_scope * (notation_entry * notation_key)

type 'a or_by_notation_r =
  | AN of 'a
  | ByNotation of (string * string option)

type 'a or_by_notation = 'a or_by_notation_r CAst.t

(* NB: the last string in [ByNotation] is actually a [Notation.delimiters],
   but this formulation avoids a useless dependency. *)

type explicitation =
  | ExplByPos of int * Id.t option (* a reference to the n-th product starting from left *)
  | ExplByName of Id.t

type binder_kind =
  | Default of Glob_term.binding_kind
  | Generalized of Glob_term.binding_kind * bool
      (** (Inner binding always Implicit) Outer bindings, typeclass-specific flag
         for implicit generalization of superclasses *)

type abstraction_kind = AbsLambda | AbsPi

type proj_flag = int option (** [Some n] = proj of the n-th visible argument *)

type prim_token =
  | Numeral of NumTok.Signed.t
  | String of string

type instance_expr = Glob_term.glob_level list

type cases_pattern_expr_r =
  | CPatAlias of cases_pattern_expr * lname
  | CPatCstr  of qualid
    * cases_pattern_expr list option * cases_pattern_expr list
  (** [CPatCstr (_, c, Some l1, l2)] represents [(@ c l1) l2] *)
  | CPatAtom of qualid option
  | CPatOr   of cases_pattern_expr list
  | CPatNotation of notation_with_optional_scope option * notation * cases_pattern_notation_substitution
    * cases_pattern_expr list (** CPatNotation (_, n, l1 ,l2) represents
                                  (notation n applied with substitution l1)
                                  applied to arguments l2 *)
  | CPatPrim   of prim_token
  | CPatRecord of (qualid * cases_pattern_expr) list
  | CPatDelimiters of string * cases_pattern_expr
  | CPatCast   of cases_pattern_expr * constr_expr
and cases_pattern_expr = cases_pattern_expr_r CAst.t

and cases_pattern_notation_substitution =
    cases_pattern_expr list *     (* for constr subterms *)
    cases_pattern_expr list list  (* for recursive notations *)

and constr_expr_r =
  | CRef     of qualid * instance_expr option
  | CFix     of lident * fix_expr list
  | CCoFix   of lident * cofix_expr list
  | CProdN   of local_binder_expr list * constr_expr
  | CLambdaN of local_binder_expr list * constr_expr
  | CLetIn   of lname * constr_expr * constr_expr option * constr_expr
  | CAppExpl of (proj_flag * qualid * instance_expr option) * constr_expr list
  | CApp     of (proj_flag * constr_expr) *
                (constr_expr * explicitation CAst.t option) list
  | CRecord  of (qualid * constr_expr) list

  (* representation of the "let" and "match" constructs *)
  | CCases of Constr.case_style   (* determines whether this value represents "let" or "match" construct *)
            * constr_expr option  (* return-clause *)
            * case_expr list
            * branch_expr list    (* branches *)

  | CLetTuple of lname list * (lname option * constr_expr option) *
                 constr_expr * constr_expr
  | CIf of constr_expr * (lname option * constr_expr option)
         * constr_expr * constr_expr
  | CHole   of Evar_kinds.t option * Namegen.intro_pattern_naming_expr * Genarg.raw_generic_argument option
  | CPatVar of Pattern.patvar
  | CEvar   of Glob_term.existential_name CAst.t * (lident * constr_expr) list
  | CSort   of Glob_term.glob_sort
  | CCast   of constr_expr * constr_expr Glob_term.cast_type
  | CNotation of notation_with_optional_scope option * notation * constr_notation_substitution
  | CGeneralization of Glob_term.binding_kind * abstraction_kind option * constr_expr
  | CPrim of prim_token
  | CDelimiters of string * constr_expr
  | CArray of instance_expr option * constr_expr array * constr_expr * constr_expr
and constr_expr = constr_expr_r CAst.t

and case_expr = constr_expr                 (* expression that is being matched *)
              * lname option                (* as-clause *)
              * cases_pattern_expr option   (* in-clause *)

and branch_expr =
  (cases_pattern_expr list list * constr_expr) CAst.t

and fix_expr =
    lident * recursion_order_expr option *
      local_binder_expr list * constr_expr * constr_expr

and cofix_expr =
    lident * local_binder_expr list * constr_expr * constr_expr

and recursion_order_expr_r =
  | CStructRec of lident
  | CWfRec of lident * constr_expr
  | CMeasureRec of lident option * constr_expr * constr_expr option (** argument, measure, relation *)
and recursion_order_expr = recursion_order_expr_r CAst.t

(* Anonymous defs allowed ?? *)
and local_binder_expr =
  | CLocalAssum   of lname list * binder_kind * constr_expr
  | CLocalDef     of lname * constr_expr * constr_expr option
  | CLocalPattern of (cases_pattern_expr * constr_expr option) CAst.t

and constr_notation_substitution =
    constr_expr list *      (* for constr subterms *)
    constr_expr list list * (* for recursive notations *)
    cases_pattern_expr list *   (* for binders *)
    local_binder_expr list list (* for binder lists (recursive notations) *)

type constr_pattern_expr = constr_expr

(** Concrete syntax for modules and module types *)

type with_declaration_ast =
  | CWith_Module of Id.t list CAst.t * qualid
  | CWith_Definition of Id.t list CAst.t * universe_decl_expr option * constr_expr

type module_ast_r =
  | CMident of qualid
  | CMapply of module_ast * module_ast
  | CMwith  of module_ast * with_declaration_ast
and module_ast = module_ast_r CAst.t
