
type typ =   Base of string
	   | Arrow of typ * typ
	   | Tuple of typ list

type term =   Cst of int
	    | Db of int
            | Tvar of string
            | Plus of term * term
	    | Moins of term * term
	    | Mult of term * term
	    | Div of term * term
	    | App of string * (term list)
and
     atom =   Eq of term * term
	    | Le of term * term
	    | Lt of term * term
	    | Ge of term * term
	    | Gt of term * term
            | Pred of string * (term list)
and
     form =   Fatom of atom
            | Fvar of string
	    | Imp of form * form
	    | And of form * form
	    | Or of form * form
	    | Not of form
	    | Forall of form
	    | Exists of form

type decl =
  | Assert of form
(*  | ...*)

type query = decl list * form


