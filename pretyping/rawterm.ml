open Names
open CoqAst

type constructor_id = ((section_path * int) * int) * identifier list

type pattern =  (* locs here refers to the ident's location, not whole pat *)
    PatVar of loc * name
  | PatCstr of loc * constructor_id * pattern list
  | PatAs of loc * identifier * pattern;;

type binder_kind = BProd | BLambda
type fix_kind = RFix of int array * int | RCofix of int
type rawsort = RProp of Term.contents | RType

type reference =
  | RConst of section_path * identifier list
  | Ind of section_path * int * identifier list
  | Construct of constructor_id
  | RAbst of section_path
  | RRel of int
  | Var of identifier
  | EVar of section_path * identifier list
  | RMeta of int

type rawconstr = 
  | RRef of loc * reference
  | RApp of loc * rawconstr * rawconstr list
  | RBinder of loc * binder_kind * name * rawconstr * rawconstr
  | RCases of loc * rawconstr option * rawconstr list * 
      (identifier list * pattern list * rawconstr) list
  | ROldCase of loc * bool * rawconstr option * rawconstr * 
      rawconstr array
  | RRec of loc * fix_kind * identifier array * 
      rawconstr array * rawconstr array
  | RSort of loc * rawsort
  | RHole of loc option

(* - if PRec (_, names, arities, bodies) is in env then arities are
   typed in env too and bodies are typed in env enriched by the
   arities incrementally lifted 

  [On pourrait plutot mettre les arités aves le type qu'elles auront
   dans le contexte servant à typer les body ???]

   - boolean in PApp means local turn off of implicit arg mode
   - option in PHole tell if the "?" was apparent or has been implicitely added
*)


