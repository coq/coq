
(* $Id$ *)

(*i*)
open Names
open Univ
open Term
open Inductive
open Environ
(*i*)

(* [mind_check_arities] checks that the types declared for all the
   inductive types are some arities. *)

val mind_check_arities : 'a unsafe_env -> mutual_inductive_entry -> unit

val sort_of_arity : 'a unsafe_env -> constr -> sorts

val cci_inductive : 
  'a unsafe_env -> 'a unsafe_env -> path_kind -> int -> bool -> 
    (identifier * typed_type * identifier list * bool * bool * constr) list ->
      constraints ->
      	mutual_inductive_body
