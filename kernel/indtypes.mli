
(* $Id$ *)

open Inductive
open Environ

(* [mind_check_arities] checks that the types declared for all the
   inductive types are some arities. *)

val mind_check_arities : 'a unsafe_env -> mutual_inductive_entry -> unit
