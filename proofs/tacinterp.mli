(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

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
  | VContext of (interp_sign -> goal sigma -> value)
  | VArg of tactic_arg
  | VFun of (string * value) list * string option list * Coqast.t
  | VVoid
  | VRec of value ref

(* Signature for interpretation: val\_interp and interpretation functions *)
and interp_sign =
  enamed_declarations * Environ.env * (string * value) list *
    (int * constr) list * goal sigma option * debug_info

(* Gives the constr corresponding to a CONSTR [tactic_arg] *)
val constr_of_Constr : tactic_arg -> constr

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

(* Adds a definition for tactics in the table *)
val add_tacdef : string -> Coqast.t -> unit

(* Interprets any expression *)
val val_interp : interp_sign -> Coqast.t -> value

(* Interprets tactic arguments *)
val interp_tacarg : interp_sign -> Coqast.t -> tactic_arg

(* Initial call for interpretation *)
val interp : Coqast.t -> tactic

(* Hides interpretation for pretty-print *)
val hide_interp : Coqast.t -> tactic

(* For bad tactic calls *)
val bad_tactic_args : string -> 'a
