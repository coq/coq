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
open Sign
open Term
open Libnames
open Nametab
(*i*)

(* Untyped intermediate terms, after ASTs and before constr. *)

type loc = int * int

(* locs here refers to the ident's location, not whole pat *)
(* the last argument of PatCstr is a possible alias ident for the pattern *)
type cases_pattern =
  | PatVar of loc * name
  | PatCstr of loc * constructor * cases_pattern list * name

type rawsort = RProp of Term.contents | RType of Univ.universe option

type fix_kind = RFix of (int array * int) | RCoFix of int

type binder_kind = BProd | BLambda | BLetIn

type quantified_hypothesis = AnonHyp of int | NamedHyp of identifier

type 'a explicit_substitution = (quantified_hypothesis * 'a) list

type 'a substitution = 
  | ImplicitBindings of 'a list
  | ExplicitBindings of 'a explicit_substitution
  | NoBindings

type 'a with_bindings = 'a * 'a substitution

type hole_kind =
  | ImplicitArg of global_reference * int
  | AbstractionType of name
  | QuestionMark
  | CasesType
  | InternalHole

type 'ctxt reference =
  | RConst of constant * 'ctxt
  | RInd of inductive * 'ctxt
  | RConstruct of constructor * 'ctxt
  | RVar of identifier
  | REVar of int * 'ctxt

type rawconstr = 
  | RRef of loc * Libnames.global_reference
  | RVar of loc * identifier
  | REvar of loc * existential_key
  | RMeta of loc * int
  | RApp of loc * rawconstr * rawconstr list
  | RLambda of loc * name * rawconstr * rawconstr
  | RProd of loc * name * rawconstr * rawconstr
  | RLetIn of loc * name * rawconstr * rawconstr
  | RCases of loc * Term.case_style * rawconstr option * rawconstr list * 
      (loc * identifier list * cases_pattern list * rawconstr) list
  | ROldCase of loc * bool * rawconstr option * rawconstr * 
      rawconstr array
  | RRec of loc * fix_kind * identifier array * 
      rawconstr array * rawconstr array
  | RSort of loc * rawsort
  | RHole of (loc * hole_kind)
  | RCast of loc * rawconstr * rawconstr
  | RDynamic of loc * Dyn.t


(*i - if PRec (_, names, arities, bodies) is in env then arities are
   typed in env too and bodies are typed in env enriched by the
   arities incrementally lifted 

  [On pourrait plutot mettre les arités aves le type qu'elles auront
   dans le contexte servant à typer les body ???]

   - boolean in POldCase means it is recursive
   - option in PHole tell if the "?" was apparent or has been implicitely added
i*)

val dummy_loc : loc
val loc_of_rawconstr : rawconstr -> loc
val set_loc_of_rawconstr : loc -> rawconstr -> rawconstr
val join_loc : loc -> loc -> loc

val subst_raw : Names.substitution -> rawconstr -> rawconstr

type 'a raw_red_flag = {
  rBeta : bool;
  rIota : bool;
  rZeta : bool;
  rDelta : bool; (* true = delta all but rConst; false = delta only on rConst*)
  rConst : 'a list
}

type ('a,'b) red_expr_gen =
  | Red of bool
  | Hnf
  | Simpl
  | Cbv of 'b raw_red_flag
  | Lazy of 'b raw_red_flag
  | Unfold of (int list * 'b) list
  | Fold of 'a list
  | Pattern of (int list * 'a) list
  | ExtraRedExpr of string * 'a list

type 'a or_metanum = AN of loc * 'a | MetaNum of loc * int

type 'a may_eval =
  | ConstrTerm of 'a
  | ConstrEval of ('a, qualid or_metanum) red_expr_gen * 'a
  | ConstrContext of (loc * identifier) * 'a
  | ConstrTypeOf of 'a
