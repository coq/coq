
type typ = string
(***
  | Base of string
  | Arrow of typ * typ
  | Tuple of typ list
***)

type term =   
  | Cst of int
  | Tvar of string
  | Plus of term * term
  | Moins of term * term
  | Mult of term * term
  | Div of term * term
  | App of string * term list

and atom =   
  | Eq of term * term
  | Le of term * term
  | Lt of term * term
  | Ge of term * term
  | Gt of term * term
  | Pred of string * term list

and form = 
  | Fatom of atom
  | Imp of form * form
  | And of form * form
  | Or of form * form
  | Not of form
  | Forall of string * typ * form
  | Exists of string * typ * form
  | True
  | False

type hyp =
  | Assert of string * form
  | DeclVar of string * typ list * typ
  | DeclPred of string * typ list
  | DeclType of string

type query = hyp list * form


(* prover result *)

type prover_answer = Valid | Invalid | DontKnow | Timeout
