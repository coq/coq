(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

(*i*)
open Util
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
  | RRef of loc * global_reference
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
i*)

let dummy_loc = (0,0)

let loc_of_rawconstr = function
  | RRef (loc,_) -> loc
  | RVar (loc,_) -> loc
  | REvar (loc,_) -> loc
  | RMeta (loc,_) -> loc
  | RApp (loc,_,_) -> loc
  | RLambda (loc,_,_,_) -> loc
  | RProd (loc,_,_,_) -> loc
  | RLetIn (loc,_,_,_) -> loc
  | RCases (loc,_,_,_,_) -> loc
  | ROldCase (loc,_,_,_,_) -> loc
  | RRec (loc,_,_,_,_) -> loc
  | RSort (loc,_) -> loc
  | RHole (loc,_) -> loc
  | RCast (loc,_,_) -> loc
  | RDynamic (loc,_) -> loc

let set_loc_of_rawconstr loc = function
  | RRef (_,a)      -> RRef (loc,a)
  | RVar (_,a)      -> RVar (loc,a)
  | REvar (_,a)      -> REvar (loc,a)
  | RMeta (_,a)     -> RMeta (loc,a) 
  | RApp (_,a,b)    -> RApp (loc,a,b)
  | RLambda (_,a,b,c) -> RLambda (loc,a,b,c)
  | RProd (_,a,b,c)   -> RProd (loc,a,b,c)
  | RLetIn (_,a,b,c)  -> RLetIn (loc,a,b,c)
  | RCases (_,a,b,c,d) -> RCases (loc,a,b,c,d) 
  | ROldCase (_,a,b,c,d) -> ROldCase (loc,a,b,c,d) 
  | RRec (_,a,b,c,d) -> RRec (loc,a,b,c,d) 
  | RSort (_,a)      -> RSort (loc,a) 
  | RHole (_,a)      -> RHole (loc,a)
  | RCast (_,a,b)    -> RCast (loc,a,b) 
  | RDynamic (_,d)   -> RDynamic (loc,d)

let join_loc (deb1,_) (_,fin2) = (deb1,fin2)

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
