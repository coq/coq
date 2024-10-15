(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
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

(** Universes *)
type sort_name_expr =
  | CSProp | CProp | CSet
  | CType of qualid
  | CRawType of Univ.Level.t (** Universes like "foo.1" have no qualid form *)

type univ_level_expr  = sort_name_expr Glob_term.glob_sort_gen

type qvar_expr =
  | CQVar of qualid
  | CQAnon of Loc.t option
  | CRawQVar of Sorts.QVar.t

type quality_expr =
  | CQConstant of Sorts.Quality.constant
  | CQualVar of qvar_expr

type relevance_expr =
  | CRelevant | CIrrelevant
  | CRelevanceVar of qvar_expr

type relevance_info_expr = relevance_expr option

type sort_expr = (qvar_expr option * (sort_name_expr * int) list Glob_term.glob_sort_gen)

type instance_expr = quality_expr list * univ_level_expr list

(** Constraints don't have anonymous universes *)
type univ_constraint_expr = sort_name_expr * Univ.constraint_type * sort_name_expr

type universe_decl_expr = (lident list, lident list, univ_constraint_expr list) UState.gen_universe_decl
type cumul_univ_decl_expr =
  (lident list, (lident * UVars.Variance.t option) list, univ_constraint_expr list) UState.gen_universe_decl

type ident_decl = lident * universe_decl_expr option
type cumul_ident_decl = lident * cumul_univ_decl_expr option
type name_decl = lname * universe_decl_expr option

type notation_with_optional_scope = LastLonelyNotation | NotationInScope of string

type side = Left | Right
type entry_level = int
type entry_relative_level = LevelLt of entry_level | LevelLe of entry_level | LevelSome

(* The entry in which a notation is declared *)
type notation_entry = InConstrEntry | InCustomEntry of string

(* A notation entry with the level where the notation lives *)
type notation_entry_level = {
  notation_entry : notation_entry;
  notation_level : entry_level;
}

(* Notation subentries, to be associated to the variables of the notation *)
type notation_entry_relative_level = {
  notation_subentry : notation_entry;
  notation_relative_level : entry_relative_level;
  notation_position : side option;
}

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
  | ExplByName of Id.t
  | ExplByPos of int (* a reference to the n-th non-dependent implicit starting from left *)

type binder_kind =
  | Default of Glob_term.binding_kind
  | Generalized of Glob_term.binding_kind * bool
      (** (Inner binding always Implicit) Outer bindings, typeclass-specific flag
         for implicit generalization of superclasses *)

type explicit_flag = bool (** true = with "@" *)

type delimiter_depth = DelimOnlyTmpScope | DelimUnboundedScope
(** shallow (%_) vs. deep (%) scope opening *)

type prim_token =
  | Number of NumTok.Signed.t
  | String of string

(** [constr_expr] is the abstract syntax tree produced by the parser *)
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
  | CPatDelimiters of delimiter_depth * string * cases_pattern_expr
  | CPatCast   of cases_pattern_expr * constr_expr
and cases_pattern_expr = cases_pattern_expr_r CAst.t

and kinded_cases_pattern_expr = cases_pattern_expr * Glob_term.binding_kind

and cases_pattern_notation_substitution =
    cases_pattern_expr list *      (* for cases_pattern subterms parsed as terms *)
    cases_pattern_expr list list * (* for recursive notations parsed as terms*)
    kinded_cases_pattern_expr list (* for cases_pattern subterms parsed as binders *)

and constr_expr_r =
  | CRef     of qualid * instance_expr option
  | CFix     of lident * fix_expr list
  | CCoFix   of lident * cofix_expr list
  | CProdN   of local_binder_expr list * constr_expr
  | CLambdaN of local_binder_expr list * constr_expr
  | CLetIn   of lname * constr_expr * constr_expr option * constr_expr
  | CAppExpl of (qualid * instance_expr option) * constr_expr list
  | CApp     of constr_expr * (constr_expr * explicitation CAst.t option) list
  | CProj    of explicit_flag * (qualid * instance_expr option)
              * (constr_expr * explicitation CAst.t option) list * constr_expr
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
  | CHole   of Evar_kinds.glob_evar_kind option
  | CGenarg of Genarg.raw_generic_argument

  (* because print for genargs wants to print directly the glob without an extern phase (??) *)
  | CGenargGlob of Genarg.glob_generic_argument

  | CPatVar of Pattern.patvar
  | CEvar   of Glob_term.existential_name CAst.t * (lident * constr_expr) list
  | CSort   of sort_expr
  | CCast   of constr_expr * Constr.cast_kind option * constr_expr
  | CNotation of notation_with_optional_scope option * notation * constr_notation_substitution
  | CGeneralization of Glob_term.binding_kind * constr_expr
  | CPrim of prim_token
  | CDelimiters of delimiter_depth * string * constr_expr
  | CArray of instance_expr option * constr_expr array * constr_expr * constr_expr
and constr_expr = constr_expr_r CAst.t

and case_expr = constr_expr                 (* expression that is being matched *)
              * lname option                (* as-clause *)
              * cases_pattern_expr option   (* in-clause *)

and branch_expr =
  (cases_pattern_expr list list * constr_expr) CAst.t

and fix_expr =
  lident * relevance_info_expr
  * fixpoint_order_expr option *
  local_binder_expr list * constr_expr * constr_expr

and cofix_expr =
    lident * relevance_info_expr * local_binder_expr list * constr_expr * constr_expr

and fixpoint_order_expr_r =
  | CStructRec of lident
  | CWfRec of lident * constr_expr
  | CMeasureRec of lident option * constr_expr * constr_expr option (** argument, measure, relation *)
and fixpoint_order_expr = fixpoint_order_expr_r CAst.t

(* Anonymous defs allowed ?? *)
and local_binder_expr =
  | CLocalAssum   of lname list * relevance_info_expr * binder_kind * constr_expr
  | CLocalDef     of lname * relevance_info_expr * constr_expr * constr_expr option
  | CLocalPattern of cases_pattern_expr

and constr_notation_substitution =
    constr_expr list *      (* for constr subterms *)
    constr_expr list list * (* for recursive notations *)
    kinded_cases_pattern_expr list *   (* for binders *)
    local_binder_expr list list (* for binder lists (recursive notations) *)

type constr_pattern_expr = constr_expr

(** Concrete syntax for modules and module types *)

type with_declaration_ast =
  | CWith_Module of Id.t list CAst.t * qualid
  | CWith_Definition of Id.t list CAst.t * universe_decl_expr option * constr_expr

type module_ast_r =
  | CMident of qualid
  | CMapply of module_ast * qualid
  | CMwith  of module_ast * with_declaration_ast
and module_ast = module_ast_r CAst.t
