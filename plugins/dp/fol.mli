
(* Polymorphic First-Order Logic (that is Why's input logic) *)

type typ =
  | Tvar of string
  | Tid of string * typ list

type term =
  | Cst of Big_int.big_int
  | RCst of Big_int.big_int
  | Power2 of Big_int.big_int
  | Plus of term * term
  | Moins of term * term
  | Mult of term * term
  | Div of term * term
  | Opp of term
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
  | Iff of form * form
  | And of form * form
  | Or of form * form
  | Not of form
  | Forall of string * typ * form
  | Exists of string * typ * form
  | True
  | False

(* the integer indicates the number of type variables *)
type decl =
  | DeclType of string * int
  | DeclFun of string * int * typ list * typ
  | DeclPred of string * int * typ list
  | Axiom of string * form

type query = decl list * form


(* prover result *)

type prover_answer =
  | Valid of string option
  | Invalid
  | DontKnow
  | Timeout
  | NoAnswer
  | Failure of string

