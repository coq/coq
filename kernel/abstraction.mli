
(* $Id$ *)

(*i*)
open Names
open Term
(*i*)

(* Abstractions. *)

type abstraction_body = { 
  abs_kind : path_kind;
  abs_arity : int array;
  abs_rhs : constr }

val contract_abstraction : abstraction_body -> constr array -> constr
