
(* $Id$ *)

(*i*)
open Names
open Proof_type
(*i*)

(* Interpretation of vernac phrases. *)
 
exception Drop
exception ProtectedLoop
exception Quit

val disable_drop : exn -> exn

type vernac_arg = 
  | VARG_VARGLIST of vernac_arg list
  | VARG_STRING of string
  | VARG_NUMBER of int
  | VARG_NUMBERLIST of int list
  | VARG_IDENTIFIER of identifier
  | VCALL of string * vernac_arg list
  | VARG_CONSTR of Coqast.t
  | VARG_CONSTRLIST of Coqast.t list
  | VARG_TACTIC of Coqast.t
  | VARG_TACTIC_ARG of tactic_arg
  | VARG_BINDER of identifier list * Coqast.t
  | VARG_BINDERLIST of (identifier list * Coqast.t) list
  | VARG_AST of Coqast.t
  | VARG_ASTLIST of Coqast.t list
  | VARG_UNIT
  | VARG_DYN of Dyn.t   (* to put whatever you want *)

val vinterp_add : string -> (vernac_arg list -> unit -> unit) -> unit
val overwriting_vinterp_add : 
  string -> (vernac_arg list -> unit -> unit) -> unit

val vinterp_map : string -> vernac_arg list -> unit -> unit
val vinterp_init : unit -> unit
val cvt_varg : Coqast.t -> vernac_arg
val call : string * vernac_arg list -> unit
val interp : Coqast.t -> unit

(* raises an user error telling that the vernac command was called
   with bad arguments *)
val bad_vernac_args : string -> 'a
