
(* $Id$ *)

(*i*)
open Pp
open Names
open Proof_type
open Tacmach
open Term
(*i*)

(* Values for interpretation *)
type value =
  | VTactic of tactic
  | VFTactic of tactic_arg list * (tactic_arg list -> tactic)
  | VRTactic of (goal list sigma * validation)
  | VArg of tactic_arg
  | VFun of (string * value) list * string option list * Coqast.t
  | VVoid
  | VRec of value ref

(* Gives the constr corresponding to a CONSTR [tactic_arg] *)
val constr_of_Constr : tactic_arg -> constr

(* Signature for interpretation: [val_interp] and interpretation functions *)
type interp_sign =
  evar_declarations * Environ.env * (string * value) list * 
    (int * constr) list * goal sigma option

(* Adds a Tactic Definition in the table *)
val add_tacdef : string -> value -> unit

(* Interprets any expression *)
val val_interp : interp_sign -> Coqast.t -> value

(* Interprets tactic arguments *)
val interp_tacarg : interp_sign -> Coqast.t -> tactic_arg

val interp               : Coqast.t -> tactic
(*i val vernac_interp        : Coqast.t -> tactic i*)
val vernac_interp_atomic : identifier -> tactic_arg list -> tactic

val is_just_undef_macro  : Coqast.t -> string option

val bad_tactic_args : string -> 'a
