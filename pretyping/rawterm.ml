
(* $Id$ *)

(*i*)
open Util
open Names
open Sign
open Type_errors
(*i*)

(* Untyped intermediate terms, after ASTs and before constr. *)

type loc = int * int

(* locs here refers to the ident's location, not whole pat *)
(* the last argument of PatCstr is a possible alias ident for the pattern *)
type cases_pattern =
  | PatVar of loc * name
  | PatCstr of
      loc * (constructor_path * identifier list) * cases_pattern list * name

type binder_kind = BProd | BLambda
type fix_kind = RFix of int array * int | RCofix of int
type rawsort = RProp of Term.contents | RType

type 'ctxt reference =
  | RConst of section_path * 'ctxt
  | RInd of inductive_path * 'ctxt
  | RConstruct of constructor_path * 'ctxt
  | RAbst of section_path
  | RVar of identifier
  | REVar of int * 'ctxt
  | RMeta of int

type rawconstr = 
  | RRef of loc * rawconstr array reference
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
  | RApp (loc,_,_) -> loc
  | RBinder (loc,_,_,_,_) -> loc
  | RCases (loc,_,_,_,_) -> loc
  | ROldCase (loc,_,_,_,_) -> loc
  | RRec (loc,_,_,_,_) -> loc
  | RSort (loc,_) -> loc
  | RHole (Some loc) -> loc
  | RHole (None) -> dummy_loc
  | RCast (loc,_,_) -> loc

type constr_pattern =
  | PRef of constr_pattern array reference
  | PRel of int
  | PApp of constr_pattern * constr_pattern array
  | PSoApp of int * int list
  | PBinder of binder_kind * name * constr_pattern * constr_pattern
  | PSort of rawsort
  | PMeta of int
(*
  | PCast of loc * constr_pattern * constr_pattern
  | PCases of loc * Term.case_style * constr_pattern option * constr_pattern list * 
      (identifier list * pattern list * constr_pattern) list
  | POldCase of loc * bool * constr_pattern option * constr_pattern * 
      constr_pattern array
  | Pec of loc * fix_kind * identifier array * 
      constr_pattern array * constr_pattern array
*)

let rec occur_meta_pattern = function
  | PApp (f,args) ->
      (occur_meta_pattern f) or (array_exists occur_meta_pattern args)
  | PBinder(_,na,t,c)  -> (occur_meta_pattern t) or (occur_meta_pattern c)
  | PMeta _ | PSoApp _ -> true
  | PRel _ | PSort _   -> false

  (* On suppose que les ctxt des cstes ne contient pas de meta *)
  | PRef _             -> false

type constr_label =
  | ConstNode of section_path
  | IndNode of inductive_path
  | CstrNode of constructor_path
  | VarNode of identifier
(*
  | ... 
*)

exception BoundPattern;;

let label_of_ref = function
  | RConst (sp,_)     -> ConstNode sp
  | RInd (sp,_)       -> IndNode sp
  | RConstruct (sp,_) -> CstrNode sp
  | RVar id           -> VarNode id
  | RAbst _           -> error "Obsolète"
  | REVar _ | RMeta _ -> raise BoundPattern

let rec head_pattern_bound t =
  match t with
    | PBinder (BProd,_,_,b) -> head_pattern_bound b 
    | PApp (f,args)         -> head_pattern_bound f
    | PRef r                -> label_of_ref r
    | PRel _ | PMeta _ | PSoApp _  | PSort _ -> raise BoundPattern
    | PBinder(BLambda,_,_,_) -> anomaly "head_pattern_bound: not a type"

open Generic
open Term

let head_of_constr_reference = function
  | DOPN (Const sp,_) -> ConstNode sp
  | DOPN (MutConstruct sp,_) -> CstrNode sp
  | DOPN (MutInd sp,_) -> IndNode sp
  | VAR id -> VarNode id
  | _ -> anomaly "Not a rigid reference"


