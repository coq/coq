(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(*i*)
open Names
open Libnames
(*i*)

(* Abstract syntax trees. *)

type loc = int * int

type t =
  | Node of loc * string * t list
  | Nmeta of loc * string
  | Nvar of loc * identifier
  | Slam of loc * identifier option * t
  | Smetalam of loc * string * t
  | Num of loc * int
  | Str of loc * string
  | Id of loc * string
  | Path of loc * kernel_name
  | Dynamic of loc * Dyn.t

(* returns the list of metas occuring in the ast *)
val collect_metas : t -> int list

(* [subst_meta bl ast]: for each binding [(i,c_i)] in [bl], 
   replace the metavar [?i] by [c_i] in [ast] *)
val subst_meta : (int * t) list -> t -> t

(* hash-consing function *)
val hcons_ast: 
  (string -> string) * (Names.identifier -> Names.identifier)
  * (kernel_name -> kernel_name)
  -> (t -> t) * (loc -> loc)

val subst_ast: Names.substitution -> t -> t

(*
val map_tactic_expr : (t -> t) -> (tactic_expr -> tactic_expr) -> tactic_expr -> tactic_expr
val fold_tactic_expr :
  ('a -> t -> 'a) -> ('a -> tactic_expr -> 'a) -> 'a -> tactic_expr -> 'a
val iter_tactic_expr : (tactic_expr -> unit) -> tactic_expr -> unit
*)


open Util
open Rawterm
open Term

type scope_name = string

type reference_expr = 
  | RQualid of qualid located
  | RIdent of identifier located

type explicitation = int

type cases_pattern =
  | CPatAlias of loc * cases_pattern * identifier
  | CPatCstr of loc * reference_expr * cases_pattern list
  | CPatAtom of loc * reference_expr option
  | CPatNumeral of loc * Bignat.bigint

type ordered_case_style = CIf | CLet | CMatch | CCase

type constr_ast =
  | CRef of reference_expr
  | CFix of loc * identifier located * fixpoint_expr list
  | CCoFix of loc * identifier located * cofixpoint_expr list
  | CArrow of loc * constr_ast * constr_ast
  | CProdN of loc * (name located list * constr_ast) list * constr_ast
  | CLambdaN of loc * (name located list * constr_ast) list * constr_ast
  | CLetIn of loc * identifier located * constr_ast * constr_ast
  | CAppExpl of loc * reference_expr * constr_ast list
  | CApp of loc * constr_ast * (constr_ast * explicitation option) list
  | CCases of loc * case_style * constr_ast option * constr_ast list *
      (loc * cases_pattern list * constr_ast) list
  | COrderedCase of loc * ordered_case_style * constr_ast option * constr_ast * constr_ast list
  | CHole of loc
  | CMeta of loc * int
  | CSort of loc * rawsort
  | CCast of loc * constr_ast * constr_ast
  | CNotation of loc * string * constr_ast list
  | CNumeral of loc * Bignat.bigint
  | CDelimiters of loc * scope_name * constr_ast
  | CDynamic of loc * Dyn.t

and local_binder = name located list * constr_ast 

and fixpoint_expr = identifier * local_binder list * constr_ast * constr_ast

and cofixpoint_expr = identifier * constr_ast * constr_ast

val constr_loc : constr_ast -> loc

val cases_pattern_loc : cases_pattern -> loc

val replace_vars_constr_ast :
  (identifier * identifier) list -> constr_ast -> constr_ast

val occur_var_constr_ast : identifier -> constr_ast -> bool
