(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

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
  | VTactic of Util.loc * tactic  (* For mixed ML/Ltac tactics (e.g. Tauto) *)
  | VRTactic of (goal list sigma * validation)
  | VFun of (identifier * value) list * identifier option list * glob_tactic_expr
  | VVoid
  | VInteger of int
  | VIntroPattern of intro_pattern_expr
  | VConstr of constr
  | VConstr_context of constr
  | VRec of value ref

(* Signature for interpretation: val\_interp and interpretation functions *)
and interp_sign =
  { lfun : (identifier * value) list;
    debug : debug_info }

(* Gives the identifier corresponding to an Identifier [tactic_arg] *)
val id_of_Identifier : Environ.env -> value -> identifier

(* Gives the constr corresponding to a Constr [value] *)
val constr_of_VConstr : Environ.env -> value -> constr

(* Transforms an id into a constr if possible *)
val constr_of_id : Environ.env -> identifier -> constr

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
val add_tacdef :
  bool -> (identifier Util.located * raw_tactic_expr) list -> unit
val add_primitive_tactic : string -> glob_tactic_expr -> unit

(* Adds an interpretation function for extra generic arguments *)
type glob_sign = {
  ltacvars : identifier list * identifier list;
  ltacrecvars : (identifier * Nametab.ltac_constant) list;
  gsigma : Evd.evar_map;
  genv : Environ.env }

val add_interp_genarg :
  string ->
    (glob_sign -> raw_generic_argument -> glob_generic_argument) *
    (interp_sign -> goal sigma -> glob_generic_argument -> 
      closed_generic_argument) *
    (Names.substitution -> glob_generic_argument -> glob_generic_argument)
    -> unit

val interp_genarg :
  interp_sign -> goal sigma -> glob_generic_argument -> closed_generic_argument

val intern_genarg :
  glob_sign -> raw_generic_argument -> glob_generic_argument

val subst_genarg :
  Names.substitution -> glob_generic_argument -> glob_generic_argument

(* Interprets any expression *)
val val_interp : interp_sign -> goal sigma -> glob_tactic_expr -> value

(* Interprets redexp arguments *)
val interp_redexp : Environ.env -> Evd.evar_map -> raw_red_expr
  -> Tacred.red_expr

(* Interprets tactic expressions *)
val interp_tac_gen : (identifier * value) list -> 
                 debug_info -> raw_tactic_expr -> tactic

(* Initial call for interpretation *)
val glob_tactic : raw_tactic_expr -> glob_tactic_expr

val glob_tactic_env : identifier list -> Environ.env -> raw_tactic_expr -> glob_tactic_expr

val eval_tactic : glob_tactic_expr -> tactic

val interp : raw_tactic_expr -> tactic

val subst_tactic : substitution -> glob_tactic_expr -> glob_tactic_expr

(* Hides interpretation for pretty-print *)

val hide_interp : raw_tactic_expr -> tactic option -> tactic

(* Adds an interpretation function *)
val interp_add : string * (interp_sign -> Coqast.t -> value) -> unit

(* Adds a possible existing interpretation function *)
val overwriting_interp_add : string * (interp_sign -> Coqast.t -> value) ->
                             unit


