
(*i $Id$ i*)

(*i*)
open Names
open Term
open Declare
(*i*)

(* Declaration functions. The following functions take ASTs, transform them
   into [constr] and then call the corresponding functions of [Declare]. *)

val definition_body : identifier -> bool * strength -> 
  Coqast.t -> Coqast.t option -> unit

val definition_body_red : Tacred.red_expr option ->  
  identifier -> bool * strength -> Coqast.t -> Coqast.t option -> unit

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

val start_proof_com : identifier option -> strength -> Coqast.t -> unit

(*s [save_named b] saves the current completed proof under the name it
was started; boolean [b] tells if the theorem is declared opaque; it
fails if the proof is not completed *)

val save_named : bool -> unit

(* [save_anonymous_thm b name] behaves as [save_named] but declares the
theorem under the name [name] and gives it the strength of a theorem *)

val save_anonymous_thm : bool -> string -> unit

(* [save_anonymous_remark b name] behaves as [save_named] but declares the
theorem under the name [name] and gives it the strength of a remark *)

val save_anonymous_remark : bool -> string -> unit

val get_current_context : unit -> Proof_type.enamed_declarations * Environ.env
