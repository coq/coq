
(* $Id$ *)

(*i*)
open Dyn
open Pp
open Names
open Proof_type
open Tacmach
open Tactic_debug
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
  enamed_declarations * Environ.env * (string * value) list * 
    (int * constr) list * goal sigma option * debug_info

(* To provide the tactic expressions *)
val loc : Coqast.loc
val tacticIn : (unit -> Coqast.t) -> Coqast.t

(* References for dynamic interpretation of user tactics. They are all
   initialized with dummy values *)
val r_evc     : enamed_declarations ref
val r_env     : Environ.env ref
val r_lfun    : (string * value) list ref
val r_lmatch  : (int * constr) list ref
val r_goalopt : goal sigma option ref
val r_debug   : debug_info ref

(* Sets the debugger mode *)
val set_debug : debug_info -> unit

(* Gives the state of debug *)
val get_debug : unit -> debug_info

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
