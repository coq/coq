
type expr =
  | Cte of Numbers.t
  | Var of string
  | Plus of expr * expr
  | Mult of expr * expr
  | Sub of expr * expr
  | Minus of expr
  | Quotient of expr * expr
;;

val plus : expr -> expr -> expr
val mult : expr -> expr -> expr
val minus : expr -> expr
val power : expr -> int -> expr

type formula =
  | True
  | False
  | Comp of expr * string * expr    (*r <,>,=,>=,<= or <> or | *)
  | And of formula list             (*r length at least 2 *)
  | Or of formula list              (*r length at least 2 *)
  | Neg of formula
  | Implies of formula * formula 
  | Equiv of formula * formula 
  | Exists of string list * formula (*r length at least 1 *)
  | Forall of string list * formula (*r length at least 1 *)
;;

val divisible : expr -> expr -> formula;;

val neg : formula -> formula;;

val exists : string list -> formula -> formula 

val forall : string list -> formula -> formula 

val conj : formula -> formula -> formula

val conj_all : formula list -> formula

val disj : formula -> formula -> formula

val disj_all : formula list -> formula

val free_vars : formula -> string list

val print_formula : formula -> unit

val print_expr : expr -> unit


(* Rename all variables in a formula. *)

val rename_formula :  (string*string) list -> formula -> formula

(* Rename all variables in an expression.*)
val rename_expr :  (string*string) list -> expr -> expr

(* [build_renaming l] builds an association list from elements of [l]
to fresh strings, that is never used before for renaming strings. *) 
 
val build_renaming : string list -> (string*string) list

(*i
val new_var : string -> string

val normalize : expr -> expr*expr

val compact : formula -> formula
i*)
