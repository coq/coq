
(* $Id$ *)

(*i*)
open Names
open Univ
open Term
open Inductive
open Environ
(*i*)


(*s The different kinds of errors that may result of a malformed inductive
  definition. *)

type inductive_error =
  | NonPos of name list * constr * constr
  | NotEnoughArgs of name list * constr * constr
  | NotConstructor of name list * constr * constr
  | NonPar of name list * constr * int * constr * constr
  | SameNamesTypes of identifier
  | SameNamesConstructors of identifier * identifier
  | NotAnArity of identifier
  | BadEntry

exception InductiveError of inductive_error

(*s The following functions are utility functions to check and to
  decompose a declaration. *)

(* [mind_check_names] checks the names of an inductive types declaration
   i.e. that all the types and constructors names are distinct. 
   It raises an exception [InductiveError _] if it is not the case. *)

val mind_check_names : mutual_inductive_entry -> unit

(* [mind_extract_and_check_params] extracts the parameters of an inductive
   types declaration. It raises an exception [InductiveError _] if there is
   not enough abstractions in any of the terms of the field 
   [mind_entry_inds]. *)

val mind_extract_and_check_params : 
  mutual_inductive_entry -> (name * constr) list

val mind_extract_params : int -> constr -> (name * constr) list * constr

val mind_check_lc : (name * constr) list -> mutual_inductive_entry -> unit

(* [mind_check_arities] checks that the types declared for all the
   inductive types are some arities. *)

val mind_check_arities : env -> mutual_inductive_entry -> unit

(* [cci_inductive] checks positivity and builds an inductive body *)

val cci_inductive : 
  env -> env -> path_kind -> int -> bool -> 
    (identifier * typed_type * identifier list * bool * bool * constr) list ->
      constraints ->
      	mutual_inductive_body
