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
(*i*)

(* Untyped intermediate terms, after ASTs and before constr. *)

type loc = int * int

(* locs here refers to the ident's location, not whole pat *)
(* the last argument of PatCstr is a possible alias ident for the pattern *)
type cases_pattern =
  | PatVar of loc * name
  | PatCstr of
      loc * (constructor_path * identifier list) * cases_pattern list * name

type rawsort = RProp of Term.contents | RType

type binder_kind = BProd | BLambda | BLetIn

type 'ctxt reference =
  | RConst of section_path * 'ctxt
  | RInd of inductive_path * 'ctxt
  | RConstruct of constructor_path * 'ctxt
  | RVar of identifier
  | REVar of int * 'ctxt

(*i Pas beau ce constr dans rawconstr, mais mal compris ce ctxt des ref i*)
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
  | RHole of loc option
  | RCast of loc * rawconstr * rawconstr


(*i - if PRec (_, names, arities, bodies) is in env then arities are
   typed in env too and bodies are typed in env enriched by the
   arities incrementally lifted 

  [On pourrait plutot mettre les arités aves le type qu'elles auront
   dans le contexte servant à typer les body ???]

   - boolean in POldCase means it is recursive
   - option in PHole tell if the "?" was apparent or has been implicitely added
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
  | RHole (Some loc) -> loc
  | RHole (None) -> dummy_loc
  | RCast (loc,_,_) -> loc

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
  | RHole _          -> RHole (Some loc)
  | RCast (_,a,b)    -> RCast (loc,a,b) 

let join_loc (deb1,_) (_,fin2) = (deb1,fin2)




