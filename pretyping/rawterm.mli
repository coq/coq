
(* $Id$ *)

(*i*)
open Names
open Sign
open Type_errors
(*i*)

(* Untyped intermediate terms, after ASTs and before constr. *)

type loc = int * int

type inductive_key = section_path * int
type constructor_key = inductive_key * int

type pattern =  (* locs here refers to the ident's location, not whole pat *)
  | PatVar of loc * name
  | PatCstr of loc * (constructor_key * identifier list) * pattern list
  | PatAs of loc * identifier * pattern

type binder_kind = BProd | BLambda
type fix_kind = RFix of int array * int | RCofix of int
type rawsort = RProp of Term.contents | RType

type reference =
  | RConst of section_path * identifier list
  | RInd of inductive_key * identifier list
  | RConstruct of constructor_key * identifier list
  | RAbst of section_path
  | RVar of identifier
  | REVar of int * identifier list
  | RMeta of int

type cases_style = PrintLet | PrintIf | PrintCases

type rawconstr = 
  | RRef of loc * reference
  | RRel of loc * int
  | RApp of loc * rawconstr * rawconstr list
  | RBinder of loc * binder_kind * name * rawconstr * rawconstr
  | RCases of loc * cases_style * rawconstr option * rawconstr list * 
      (identifier list * pattern list * rawconstr) list
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
