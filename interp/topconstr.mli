(***********************************************************************
    v      *   The Coq Proof Assistant  /  The Coq Development Team     
   <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud 
     \VV/  *************************************************************
      //   *      This file is distributed under the terms of the       
           *       GNU Lesser General Public License Version 2.1        
  ***********************************************************************)

(*i $Id$ i*)

open Pp
open Util
open Names
open Libnames
open Rawterm
open Term
open Mod_subst

(** {6 Sect } *)
(** This is the subtype of rawconstr allowed in syntactic extensions 
   No location since intended to be substituted at any place of a text 
   Complex expressions such as fixpoints and cofixpoints are excluded, 
   non global expressions such as existential variables also *)

type aconstr =
  (** Part common to [rawconstr] and [cases_pattern] *)
  | ARef of global_reference
  | AVar of identifier
  | AApp of aconstr * aconstr list
  | AList of identifier * identifier * aconstr * aconstr * bool
  (** Part only in [rawconstr] *)
  | ALambda of name * aconstr * aconstr
  | AProd of name * aconstr * aconstr
  | ALetIn of name * aconstr * aconstr
  | ACases of case_style * aconstr option *
      (aconstr * (name * (inductive * int * name list) option)) list *
      (cases_pattern list * aconstr) list
  | ALetTuple of name list * (name * aconstr option) * aconstr * aconstr
  | AIf of aconstr * (name * aconstr option) * aconstr * aconstr
  | ARec of fix_kind * identifier array *
      (name * aconstr option * aconstr) list array * aconstr array *
      aconstr array
  | ASort of rawsort
  | AHole of Evd.hole_kind
  | APatVar of patvar
  | ACast of aconstr * aconstr cast_type

(*********************************************************************
   Translate a rawconstr into a notation given the list of variables  
   bound by the notation; also interpret recursive patterns           *)

val aconstr_of_rawconstr : identifier list -> rawconstr -> aconstr

(** Name of the special identifier used to encode recursive notations  *)
val ldots_var : identifier

(** Equality of rawconstr (warning: only partially implemented) *)
val eq_rawconstr : rawconstr -> rawconstr -> bool

(*********************************************************************
   Re-interpret a notation as a rawconstr, taking care of binders     *)

val rawconstr_of_aconstr_with_binders : loc ->
  ('a -> name -> 'a * name) ->
  ('a -> aconstr -> rawconstr) -> 'a -> aconstr -> rawconstr

val rawconstr_of_aconstr : loc -> aconstr -> rawconstr

(*********************************************************************
   [match_aconstr metas] matches a rawconstr against an aconstr with  
   metavariables in [metas]; raise [No_match] if the matching fails   *)

exception No_match

type scope_name = string

type tmp_scope_name = scope_name

type subscopes = tmp_scope_name option * scope_name list

type interpretation =
    (** regular vars of notation    / recursive parts of notation    / body *)
    ((identifier * subscopes) list * (identifier * subscopes) list) * aconstr

val match_aconstr : rawconstr -> interpretation ->
      (rawconstr * subscopes) list * (rawconstr list * subscopes) list

(*********************************************************************
   Substitution of kernel names in interpretation data                *)

val subst_interpretation : substitution -> interpretation -> interpretation

(*********************************************************************
  s Concrete syntax for terms                                         *)

type notation = string

type explicitation = ExplByPos of int * identifier option | ExplByName of identifier

type binder_kind =
  | Default of binding_kind
  | Generalized of binding_kind * binding_kind * bool
      (** Inner binding, outer bindings, typeclass-specific flag
	 for implicit generalization of superclasses *)

type abstraction_kind = AbsLambda | AbsPi

type proj_flag = int option (** [Some n] = proj of the n-th visible argument *)

type prim_token = Numeral of Bigint.bigint | String of string

type 'a notation_substitution =
    'a list * (** for recursive notations: *) 'a list list

type cases_pattern_expr =
  | CPatAlias of loc * cases_pattern_expr * identifier
  | CPatCstr of loc * reference * cases_pattern_expr list
  | CPatAtom of loc * reference option
  | CPatOr of loc * cases_pattern_expr list
  | CPatNotation of loc * notation * cases_pattern_expr notation_substitution
  | CPatPrim of loc * prim_token
  | CPatRecord of Util.loc * (reference * cases_pattern_expr) list
  | CPatDelimiters of loc * string * cases_pattern_expr

type constr_expr =
  | CRef of reference
  | CFix of loc * identifier located * fix_expr list
  | CCoFix of loc * identifier located * cofix_expr list
  | CArrow of loc * constr_expr * constr_expr
  | CProdN of loc * (name located list * binder_kind * constr_expr) list * constr_expr
  | CLambdaN of loc * (name located list * binder_kind * constr_expr) list * constr_expr
  | CLetIn of loc * name located * constr_expr * constr_expr
  | CAppExpl of loc * (proj_flag * reference) * constr_expr list
  | CApp of loc * (proj_flag * constr_expr) *
      (constr_expr * explicitation located option) list
  | CRecord of loc * constr_expr option * (reference * constr_expr) list
  | CCases of loc * case_style * constr_expr option *
      (constr_expr * (name option * constr_expr option)) list *
      (loc * cases_pattern_expr list located list * constr_expr) list
  | CLetTuple of loc * name list * (name option * constr_expr option) *
      constr_expr * constr_expr
  | CIf of loc * constr_expr * (name option * constr_expr option)
      * constr_expr * constr_expr
  | CHole of loc * Evd.hole_kind option
  | CPatVar of loc * (bool * patvar)
  | CEvar of loc * existential_key * constr_expr list option
  | CSort of loc * rawsort
  | CCast of loc * constr_expr * constr_expr cast_type
  | CNotation of loc * notation * constr_expr notation_substitution
  | CGeneralization of loc * binding_kind * abstraction_kind option * constr_expr
  | CPrim of loc * prim_token
  | CDelimiters of loc * string * constr_expr
  | CDynamic of loc * Dyn.t

and fix_expr =
    identifier located * (identifier located option * recursion_order_expr) * local_binder list * constr_expr * constr_expr

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

type typeclass_constraint = name located * binding_kind * constr_expr

and typeclass_context = typeclass_constraint list

type constr_pattern_expr = constr_expr

(*********************************************************************
   Utilities on constr_expr                                           *)

val constr_loc : constr_expr -> loc

val cases_pattern_expr_loc : cases_pattern_expr -> loc

val replace_vars_constr_expr :
  (identifier * identifier) list -> constr_expr -> constr_expr

val free_vars_of_constr_expr : constr_expr -> Idset.t
val occur_var_constr_expr : identifier -> constr_expr -> bool

val default_binder_kind : binder_kind

(** Specific function for interning "in indtype" syntax of "match" *)
val ids_of_cases_indtype : constr_expr -> identifier list

val mkIdentC : identifier -> constr_expr
val mkRefC : reference -> constr_expr
val mkAppC : constr_expr * constr_expr list -> constr_expr
val mkCastC : constr_expr * constr_expr cast_type -> constr_expr
val mkLambdaC : name located list * binder_kind * constr_expr * constr_expr -> constr_expr
val mkLetInC : name located * constr_expr * constr_expr -> constr_expr
val mkProdC : name located list * binder_kind * constr_expr * constr_expr -> constr_expr

val coerce_reference_to_id : reference -> identifier
val coerce_to_id : constr_expr -> identifier located
val coerce_to_name : constr_expr -> name located

val index_of_annot : local_binder list -> identifier located option -> int option

val abstract_constr_expr : constr_expr -> local_binder list -> constr_expr
val prod_constr_expr : constr_expr -> local_binder list -> constr_expr

(** Same as [abstract_constr_expr] and [prod_constr_expr], with location *)
val mkCLambdaN : loc -> local_binder list -> constr_expr -> constr_expr
val mkCProdN : loc -> local_binder list -> constr_expr -> constr_expr

(** For binders parsing *)

(** With let binders *)
val names_of_local_binders : local_binder list -> name located list

(** Does not take let binders into account *)
val names_of_local_assums : local_binder list -> name located list

(** Used in typeclasses *)

val fold_constr_expr_with_binders : (identifier -> 'a -> 'a) ->
   ('a -> 'b -> constr_expr -> 'b) -> 'a -> 'b -> constr_expr -> 'b

(** Used in correctness and interface; absence of var capture not guaranteed 
   in pattern-matching clauses and in binders of the form [x,y:T(x)] *)

val map_constr_expr_with_binders :
  (identifier -> 'a -> 'a) -> ('a -> constr_expr -> constr_expr) ->
      'a -> constr_expr -> constr_expr

(*********************************************************************
   Concrete syntax for modules and module types                       *)

type with_declaration_ast =
  | CWith_Module of identifier list located * qualid located
  | CWith_Definition of identifier list located * constr_expr

type module_ast =
  | CMident of qualid located
  | CMapply of module_ast * module_ast
  | CMwith of module_ast * with_declaration_ast

type module_ast_inl = module_ast * bool (** honor the inline annotations or not *)

type 'a module_signature =
  | Enforce of 'a (** ... : T *)
  | Check of 'a list (** ... <: T1 <: T2, possibly empty *)

val ntn_loc :
  Util.loc -> constr_expr notation_substitution -> string -> (int * int) list
val patntn_loc :
  Util.loc -> cases_pattern_expr notation_substitution -> string ->
  (int * int) list
