open Names
open Util

type const = CNat of int | CInt of int | CBool of bool
  
type term = 
    SIdent of identifier located
  | SLambda of (identifier located * type_ located) * term located
  | SApp of term located * term located
  | SLetIn of (name located) * (term located) * term located
  | SLetTuple of (name located) list * term located * term located
  | SIfThenElse of (term located) * (term located) * (term located)
  | SSumInf of (term located) * (term located)
  | SSumDep of (identifier located * term located) * (term located * type_ located)
and lettuple_el = (identifier located) option * term_loc * type_loc option
and term_loc = term located
and type_ =     
  | TApp of type_loc * type_loc
  | TPi of (name located * type_loc) * type_loc
  | TSigma of (name located * type_loc) * type_loc
  | TSubset of (identifier located * type_loc) * type_loc
  | TIdent of identifier located
  | TTerm of term_loc

and type_loc = type_ located
