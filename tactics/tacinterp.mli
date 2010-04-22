(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(*i*)
open Pp
open Util
open Names
open Proof_type
open Tacmach
open Tactic_debug
open Term
open Tacexpr
open Genarg
open Topconstr
open Mod_subst
open Redexpr
(*i*)

(* Values for interpretation *)
type value =
  | VRTactic of (goal list sigma)
  | VFun of ltac_trace * (identifier*value) list *
      identifier option list * glob_tactic_expr
  | VVoid
  | VInteger of int
  | VIntroPattern of intro_pattern_expr
  | VConstr of constr
  | VConstr_context of constr
  | VList of value list
  | VRec of (identifier*value) list ref * glob_tactic_expr

(* Signature for interpretation: val\_interp and interpretation functions *)
and interp_sign =
  { lfun : (identifier * value) list;
    avoid_ids : identifier list;
    debug : debug_info;
    trace : ltac_trace }

val extract_ltac_vars : interp_sign -> Evd.evar_map -> Environ.env ->
  Pretyping.var_map * Pretyping.unbound_ltac_var_map

(* Transforms an id into a constr if possible *)
val constr_of_id : Environ.env -> identifier -> constr

(* To embed several objects in Coqast.t *)
val tactic_in : (interp_sign -> glob_tactic_expr) -> Dyn.t
val tactic_out : Dyn.t -> (interp_sign -> glob_tactic_expr)

val tacticIn : (interp_sign -> raw_tactic_expr) -> raw_tactic_expr
val globTacticIn : (interp_sign -> glob_tactic_expr) -> raw_tactic_expr
val valueIn : value -> raw_tactic_arg
val constrIn : constr -> constr_expr

(* Sets the debugger mode *)
val set_debug : debug_info -> unit

(* Gives the state of debug *)
val get_debug : unit -> debug_info

(* Adds a definition for tactics in the table *)
val add_tacdef :
  Vernacexpr.locality_flag -> bool ->
  (Libnames.reference * bool * raw_tactic_expr) list -> unit
val add_primitive_tactic : string -> glob_tactic_expr -> unit

(* Tactic extensions *)
val add_tactic :
  string -> (typed_generic_argument list -> tactic) -> unit
val overwriting_add_tactic :
  string -> (typed_generic_argument list -> tactic) -> unit
val lookup_tactic :
  string -> (typed_generic_argument list) -> tactic

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
      typed_generic_argument) *
    (substitution -> glob_generic_argument -> glob_generic_argument)
    -> unit

val interp_genarg :
  interp_sign -> goal sigma -> glob_generic_argument -> typed_generic_argument

val intern_genarg :
  glob_sign -> raw_generic_argument -> glob_generic_argument

val intern_tactic :
  glob_sign -> raw_tactic_expr -> glob_tactic_expr

val intern_constr :
  glob_sign -> constr_expr -> rawconstr_and_expr

val intern_constr_with_bindings :
  glob_sign -> constr_expr * constr_expr Rawterm.bindings ->
  rawconstr_and_expr * rawconstr_and_expr Rawterm.bindings

val intern_hyp :
  glob_sign -> identifier Util.located -> identifier Util.located

val subst_genarg :
  substitution -> glob_generic_argument -> glob_generic_argument

val subst_rawconstr_and_expr :
  substitution -> rawconstr_and_expr -> rawconstr_and_expr

(* Interprets any expression *)
val val_interp : interp_sign -> goal sigma -> glob_tactic_expr -> value

(* Interprets an expression that evaluates to a constr *)
val interp_ltac_constr : interp_sign -> goal sigma -> glob_tactic_expr ->
  constr

(* Interprets redexp arguments *)
val interp_redexp : Environ.env -> Evd.evar_map -> raw_red_expr -> red_expr

(* Interprets tactic expressions *)
val interp_tac_gen : (identifier * value) list -> identifier list ->
                 debug_info -> raw_tactic_expr -> tactic

val interp_hyp :  interp_sign -> goal sigma -> identifier located -> identifier

val interp_bindings : interp_sign -> Environ.env -> Evd.evar_map -> rawconstr_and_expr Rawterm.bindings -> Evd.evar_map * constr Rawterm.bindings

(* Initial call for interpretation *)
val glob_tactic : raw_tactic_expr -> glob_tactic_expr

val glob_tactic_env : identifier list -> Environ.env -> raw_tactic_expr -> glob_tactic_expr

val eval_tactic : glob_tactic_expr -> tactic

val interp : raw_tactic_expr -> tactic

val eval_ltac_constr : goal sigma -> raw_tactic_expr -> constr

val subst_tactic : substitution -> glob_tactic_expr -> glob_tactic_expr

(* Hides interpretation for pretty-print *)

val hide_interp : raw_tactic_expr -> tactic option -> tactic

(* Declare the default tactic to fill implicit arguments *)
val declare_implicit_tactic : tactic -> unit

(* Declare the xml printer *)
val declare_xml_printer :
  (out_channel -> Environ.env -> Evd.evar_map -> constr -> unit) -> unit

(* printing *)
val print_ltac : Libnames.qualid -> std_ppcmds

(* Internals that can be useful for syntax extensions. *)

exception CannotCoerceTo of string

val interp_ltac_var : (value -> 'a) -> interp_sign -> Environ.env option -> identifier located -> 'a

val interp_int : interp_sign -> identifier located -> int

val error_ltac_variable : loc -> identifier -> Environ.env option -> value -> string -> 'a

