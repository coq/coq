(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(*i*)
open Util
open Names
open Sign
open Term
open Libnames
open Nametab
(*i*)

(* Untyped intermediate terms, after ASTs and before constr. *)

(* locs here refers to the ident's location, not whole pat *)
(* the last argument of PatCstr is a possible alias ident for the pattern *)
type cases_pattern =
  | PatVar of loc * name
  | PatCstr of loc * constructor * cases_pattern list * name

val pattern_loc : cases_pattern -> loc

type patvar = identifier

type rawsort = RProp of Term.contents | RType of Univ.universe option

type fix_kind = RFix of (int array * int) | RCoFix of int

type binder_kind = BProd | BLambda | BLetIn

type quantified_hypothesis = AnonHyp of int | NamedHyp of identifier

type 'a explicit_bindings = (loc * quantified_hypothesis * 'a) list

type 'a bindings = 
  | ImplicitBindings of 'a list
  | ExplicitBindings of 'a explicit_bindings
  | NoBindings

type 'a with_bindings = 'a * 'a bindings

type hole_kind =
  | ImplicitArg of global_reference * (int * identifier option)
  | BinderType of name
  | QuestionMark
  | CasesType
  | InternalHole
  | TomatchTypeParameter of inductive * int

type rawconstr = 
  | RRef of (loc * global_reference)
  | RVar of (loc * identifier)
  | REvar of loc * existential_key * rawconstr list option
  | RPatVar of loc * (bool * patvar) (* Used for patterns only *)
  | RApp of loc * rawconstr * rawconstr list
  | RLambda of loc * name * rawconstr * rawconstr
  | RProd of loc * name * rawconstr * rawconstr
  | RLetIn of loc * name * rawconstr * rawconstr
  | RCases of loc * (rawconstr option * rawconstr option ref) *
      (rawconstr * (name * (loc * inductive * name list) option) ref) list * 
      (loc * identifier list * cases_pattern list * rawconstr) list
  | ROrderedCase of loc * case_style * rawconstr option * rawconstr * 
      rawconstr array * rawconstr option ref
  | RLetTuple of loc * name list * (name * rawconstr option) * 
      rawconstr * rawconstr
  | RIf of loc * rawconstr * (name * rawconstr option) * rawconstr * rawconstr
  | RRec of loc * fix_kind * identifier array * rawdecl list array *
      rawconstr array * rawconstr array
  | RSort of loc * rawsort
  | RHole of (loc * hole_kind)
  | RCast of loc * rawconstr * rawconstr
  | RDynamic of loc * Dyn.t

and rawdecl = name * rawconstr option * rawconstr

val cases_predicate_names : 
  (rawconstr * (name * (loc * inductive * name list) option) ref) list ->
      name list

(*i - if PRec (_, names, arities, bodies) is in env then arities are
   typed in env too and bodies are typed in env enriched by the
   arities incrementally lifted 

  [On pourrait plutot mettre les arités aves le type qu'elles auront
   dans le contexte servant à typer les body ???]

   - boolean in POldCase means it is recursive
   - option in PHole tell if the "?" was apparent or has been implicitely added
i*)

val map_rawconstr : (rawconstr -> rawconstr) -> rawconstr -> rawconstr

(*
val map_rawconstr_with_binders_loc : loc -> 
  (identifier -> 'a -> identifier * 'a) ->
  ('a -> rawconstr -> rawconstr) -> 'a -> rawconstr -> rawconstr
*)

val occur_rawconstr : identifier -> rawconstr -> bool

val loc_of_rawconstr : rawconstr -> loc

val subst_raw : Names.substitution -> rawconstr -> rawconstr

type 'a raw_red_flag = {
  rBeta : bool;
  rIota : bool;
  rZeta : bool;
  rDelta : bool; (* true = delta all but rConst; false = delta only on rConst*)
  rConst : 'a list
}

val all_flags : 'a raw_red_flag

type 'a occurrences = int list * 'a

type ('a,'b) red_expr_gen =
  | Red of bool
  | Hnf
  | Simpl of 'a occurrences option
  | Cbv of 'b raw_red_flag
  | Lazy of 'b raw_red_flag
  | Unfold of 'b occurrences list
  | Fold of 'a list
  | Pattern of 'a occurrences list
  | ExtraRedExpr of string * 'a

type ('a,'b) may_eval =
  | ConstrTerm of 'a
  | ConstrEval of ('a, 'b) red_expr_gen * 'a
  | ConstrContext of (loc * identifier) * 'a
  | ConstrTypeOf of 'a
