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
  | VTacticClos of interp_sign * Coqast.t
  | VFTactic of tactic_arg list * string
  | VRTactic of (goal list sigma * validation)
  | VTactic of tactic
  | VContext of interp_sign * Coqast.t * Coqast.t list
  | VArg of tactic_arg
  | VFun of (identifier * value) list * identifier option list * Coqast.t
  | VVoid
  | VRec of value ref

(* Signature for interpretation: val\_interp and interpretation functions *)
and interp_sign =
  { evc : Evd.evar_map;
    env : Environ.env;
    lfun : (identifier * value) list;
    lmatch : (int * constr) list;
    goalopt : goal sigma option;
    debug : debug_info }

(* Gives the identifier corresponding to an Identifier [tactic_arg] *)
val id_of_Identifier : tactic_arg -> identifier

(* Gives the constr corresponding to a Constr [tactic_arg] *)
val constr_of_Constr : tactic_arg -> constr

(* Transforms an id into a constr if possible *)
val constr_of_id : interp_sign -> identifier -> constr

(* To embed several objects in Coqast.t *)
val tacticIn : (interp_sign -> Coqast.t) -> Coqast.t
val tacticOut : Coqast.t -> (interp_sign -> Coqast.t)
val valueIn : value -> Coqast.t
val valueOut: Coqast.t -> value
val constrIn : constr -> Coqast.t
val constrOut : Coqast.t -> constr
val loc : Coqast.loc

(* Sets the debugger mode *)
val set_debug : debug_info -> unit

(* Gives the state of debug *)
val get_debug : unit -> debug_info

(* Adds a definition for tactics in the table *)
val add_tacdef : identifier -> Coqast.t -> unit

(* Interprets any expression *)
val val_interp : interp_sign -> Coqast.t -> value

(* Interprets tactic arguments *)
val interp_tacarg : interp_sign -> Coqast.t -> tactic_arg

(* Interprets tactic expressions *)
val tac_interp : (identifier * value) list -> (int * constr) list ->
                 debug_info -> Coqast.t -> tactic

(* Initial call for interpretation *)
val interp : Coqast.t -> tactic

(* Hides interpretation for pretty-print *)
val hide_interp : Coqast.t -> tactic

(* Adds an interpretation function *)
val interp_add : string * (interp_sign -> Coqast.t -> value) -> unit

(* Adds a possible existing interpretation function *)
val overwriting_interp_add : string * (interp_sign -> Coqast.t -> value) ->
                             unit

(* For bad tactic calls *)
val bad_tactic_args : string -> 'a
