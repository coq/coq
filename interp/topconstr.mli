(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

(*i*)
open Pp
open Util
open Names
open Libnames
open Rawterm
open Term
(*i*)

(*s This is the subtype of rawconstr allowed in syntactic extensions *)
(* No location since intended to be substituted at any place of a text *)
(* Complex expressions such as fixpoints, cofixpoints and pattern-matching *)
(* are excluded; non global expressions such as existential variables also *)

type aconstr =
  | ARef of global_reference
  | AVar of identifier
  | AApp of aconstr * aconstr list
  | ALambda of name * aconstr * aconstr
  | AProd of name * aconstr * aconstr
  | ALetIn of name * aconstr * aconstr
  | ACases of aconstr option * aconstr list *
      (identifier list * cases_pattern list * aconstr) list
  | AOldCase of case_style * aconstr option * aconstr * aconstr array
  | ASort of rawsort
  | AHole of hole_kind
  | AMeta of int
  | ACast of aconstr * aconstr

val map_aconstr_with_binders_loc : loc -> 
  (identifier -> 'a -> identifier * 'a) ->
  ('a -> aconstr -> rawconstr) -> 'a -> aconstr -> rawconstr

val subst_aconstr : Names.substitution -> aconstr -> aconstr

val aconstr_of_rawconstr : rawconstr -> aconstr

(*s Concrete syntax for terms *)

type scope_name = string

type notation = string

type explicitation = int

type cases_pattern_expr =
  | CPatAlias of loc * cases_pattern_expr * identifier
  | CPatCstr of loc * reference * cases_pattern_expr list
  | CPatAtom of loc * reference option
  | CPatNumeral of loc * Bignat.bigint
  | CPatDelimiters of loc * scope_name * cases_pattern_expr

type constr_expr =
  | CRef of reference
  | CFix of loc * identifier located * fixpoint_expr list
  | CCoFix of loc * identifier located * cofixpoint_expr list
  | CArrow of loc * constr_expr * constr_expr
  | CProdN of loc * (name located list * constr_expr) list * constr_expr
  | CLambdaN of loc * (name located list * constr_expr) list * constr_expr
  | CLetIn of loc * name located * constr_expr * constr_expr
  | CAppExpl of loc * reference * constr_expr list
  | CApp of loc * constr_expr * (constr_expr * explicitation option) list
  | CCases of loc * constr_expr option * constr_expr list *
      (loc * cases_pattern_expr list * constr_expr) list
  | COrderedCase of loc * case_style * constr_expr option * constr_expr
      * constr_expr list
  | CHole of loc
  | CMeta of loc * int
  | CSort of loc * rawsort
  | CCast of loc * constr_expr * constr_expr
  | CNotation of loc * notation * (identifier * constr_expr) list
  | CGrammar of loc * aconstr * (identifier * constr_expr) list
  | CNumeral of loc * Bignat.bigint
  | CDelimiters of loc * scope_name * constr_expr
  | CDynamic of loc * Dyn.t

and fixpoint_expr = identifier * int * constr_expr * constr_expr

and cofixpoint_expr = identifier * constr_expr * constr_expr

val constr_loc : constr_expr -> loc

val cases_pattern_loc : cases_pattern_expr -> loc

val replace_vars_constr_expr :
  (identifier * identifier) list -> constr_expr -> constr_expr

val occur_var_constr_expr : identifier -> constr_expr -> bool

val mkIdentC : identifier -> constr_expr
val mkRefC : reference -> constr_expr
val mkAppC : constr_expr * constr_expr list -> constr_expr
val mkCastC : constr_expr * constr_expr -> constr_expr
val mkLambdaC : name located list * constr_expr * constr_expr -> constr_expr
val mkLetInC : name located * constr_expr * constr_expr -> constr_expr
val mkProdC : name located list * constr_expr * constr_expr -> constr_expr

(* Used in correctness and interface; absence of var capture not guaranteed *)
(* in pattern-matching clauses and in binders of the form [x,y:T(x)] *)

val map_constr_expr_with_binders :
  ('a -> constr_expr -> constr_expr) ->
      (identifier -> 'a -> 'a) -> 'a -> constr_expr -> constr_expr

(* For binders parsing *)

type local_binder =
  | LocalRawDef of name located * constr_expr
  | LocalRawAssum of name located list * constr_expr

(* Concrete syntax for modules and modules types *)

type with_declaration_ast = 
  | CWith_Module of identifier * qualid located
  | CWith_Definition of identifier * constr_expr

type module_type_ast = 
  | CMTEident of qualid located
  | CMTEwith of module_type_ast * with_declaration_ast

type module_ast = 
  | CMEident of qualid located
  | CMEapply of module_ast * module_ast
