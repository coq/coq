
(* $Id$ *)

(*i*)
open Names
open Term
open Declare
(*i*)

(* Declaration functions. The following functions take ASTs, transform them
   into [constr] and then call the corresponding functions of [Declare]. *)

val definition_body : identifier -> strength -> 
  Coqast.t -> Coqast.t option -> unit

val definition_body_red : identifier -> strength ->
  Coqast.t -> Coqast.t option -> Tacred.red_expr option -> unit

val syntax_definition : identifier -> Coqast.t -> unit

(*i
val abstraction_definition : identifier -> int array -> Coqast.t -> unit
i*)

val hypothesis_def_var : bool -> string -> strength -> Coqast.t -> unit

val parameter_def_var : string -> Coqast.t -> unit

val build_mutual : 
  (identifier * Coqast.t) list -> 
    (identifier * Coqast.t * (identifier * Coqast.t) list) list -> bool -> unit

val build_recursive :
  (identifier * ((identifier * Coqast.t) list) * Coqast.t * Coqast.t) list 
  -> unit

val build_corecursive :  (identifier * Coqast.t * Coqast.t) list -> unit

val build_scheme : (identifier * bool * identifier * Coqast.t) list -> unit

val start_proof_com : string -> strength -> Coqast.t -> unit

val get_current_context : unit -> Proof_type.evar_declarations * Environ.env
