
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

(*i Pas beau ce constr dans rawconstr, mais mal compris ce ctxt des ref i*)
type rawconstr = 
  | RRef of loc * rawconstr array reference
  | RMeta of loc * int
  | RApp of loc * rawconstr * rawconstr list
  | RBinder of loc * binder_kind * name * rawconstr * rawconstr
  | RCases of loc * Term.case_style * rawconstr option * rawconstr list * 
      (identifier list * cases_pattern list * rawconstr) list
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
  | RMeta (loc,_) -> loc
  | RApp (loc,_,_) -> loc
  | RBinder (loc,_,_,_,_) -> loc
  | RCases (loc,_,_,_,_) -> loc
  | ROldCase (loc,_,_,_,_) -> loc
  | RRec (loc,_,_,_,_) -> loc
  | RSort (loc,_) -> loc
  | RHole (Some loc) -> loc
  | RHole (None) -> dummy_loc
  | RCast (loc,_,_) -> loc



