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
open Tacexpr
open Genarg
open Topconstr
(*i*)

(* Values for interpretation *)
type value =
  | VClosure of interp_sign * raw_tactic_expr
  | VTactic of tactic  (* For mixed ML/Ltac tactics (e.g. Tauto) *)
  | VFTactic of value list * (value list->tactic)
  | VRTactic of (goal list sigma * validation)
  | VContext of interp_sign * direction_flag
      * (pattern_expr,raw_tactic_expr) match_rule list
  | VFun of (identifier * value) list * identifier option list *raw_tactic_expr
  | VVoid
  | VInteger of int
  | VIdentifier of identifier
  | VConstr of constr
  | VConstr_context of constr
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
val id_of_Identifier : value -> identifier

(* Gives the constr corresponding to a Constr [value] *)
val constr_of_VConstr : value -> constr

(* Transforms an id into a constr if possible *)
val constr_of_id : interp_sign -> identifier -> constr

(* To embed several objects in Coqast.t *)
val tacticIn : (interp_sign -> raw_tactic_expr) -> raw_tactic_expr
val tacticOut : raw_tactic_expr -> (interp_sign -> raw_tactic_expr)
val valueIn : value -> raw_tactic_arg
val valueOut: raw_tactic_arg -> value
val constrIn : constr -> constr_expr
val constrOut : constr_expr -> constr

(* Sets the debugger mode *)
val set_debug : debug_info -> unit

(* Gives the state of debug *)
val get_debug : unit -> debug_info

(* Adds a definition for tactics in the table *)
val add_tacdef : (identifier Util.located * raw_tactic_expr) list -> unit

(* Adds an interpretation function for extra generic arguments *)
val add_genarg_interp :
  string ->
    (interp_sign -> raw_generic_argument -> closed_generic_argument) -> unit

val genarg_interp :
  interp_sign -> raw_generic_argument -> closed_generic_argument

(* Interprets any expression *)
val val_interp : interp_sign -> raw_tactic_expr -> value

(*
(* Interprets tactic arguments *)
val interp_tacarg : interp_sign -> raw_tactic_expr -> value
*)

(* Interprets redexp arguments *)
val interp_redexp : Environ.env -> Evd.evar_map -> raw_red_expr
  -> Tacred.red_expr

(* Interprets tactic expressions *)
val tac_interp : (identifier * value) list -> (int * constr) list ->
                 debug_info -> raw_tactic_expr -> tactic

(* Interprets constr expressions *)
val constr_interp : interp_sign -> constr_expr -> constr

(* Initial call for interpretation *)
val interp : raw_tactic_expr -> tactic

(* Hides interpretation for pretty-print *)
val hide_interp : raw_tactic_expr -> tactic

(* Adds an interpretation function *)
val interp_add : string * (interp_sign -> Coqast.t -> value) -> unit

(* Adds a possible existing interpretation function *)
val overwriting_interp_add : string * (interp_sign -> Coqast.t -> value) ->
                             unit


