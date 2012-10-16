(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Names
open Proof_type
open Tacmach
open Tactic_debug
open Term
open Tacexpr
open Genarg
open Constrexpr
open Mod_subst
open Redexpr
open Misctypes

(** Values for interpretation *)
type value =
  | VRTactic of (goal list sigma)
  | VFun of ltac_trace * (identifier*value) list *
      identifier option list * glob_tactic_expr
  | VVoid
  | VInteger of int
  | VIntroPattern of intro_pattern_expr
  | VConstr of Pattern.constr_under_binders
  | VConstr_context of constr
  | VList of value list
  | VRec of (identifier*value) list ref * glob_tactic_expr

(** Signature for interpretation: val\_interp and interpretation functions *)
and interp_sign =
  { lfun : (identifier * value) list;
    avoid_ids : identifier list;
    debug : debug_info;
    trace : ltac_trace }

val extract_ltac_constr_values : interp_sign -> Environ.env ->
  Pretyping.ltac_var_map

(** To embed several objects in Coqast.t *)
val tactic_in : (interp_sign -> glob_tactic_expr) -> Dyn.t
val tactic_out : Dyn.t -> (interp_sign -> glob_tactic_expr)

val tacticIn : (interp_sign -> raw_tactic_expr) -> raw_tactic_expr
val globTacticIn : (interp_sign -> glob_tactic_expr) -> raw_tactic_expr
val valueIn : value -> raw_tactic_arg

(** Sets the debugger mode *)
val set_debug : debug_info -> unit

(** Gives the state of debug *)
val get_debug : unit -> debug_info


(** Adds an interpretation function for extra generic arguments *)

type interp_genarg_type =
    interp_sign -> goal sigma -> glob_generic_argument ->
      Evd.evar_map * typed_generic_argument

val add_interp_genarg : string -> interp_genarg_type -> unit

val interp_genarg : interp_genarg_type

(** Interprets any expression *)
val val_interp : interp_sign -> goal sigma -> glob_tactic_expr -> Evd.evar_map * value

(** Interprets an expression that evaluates to a constr *)
val interp_ltac_constr : interp_sign -> goal sigma -> glob_tactic_expr ->
  Evd.evar_map * constr

(** Interprets redexp arguments *)
val interp_redexp : Environ.env -> Evd.evar_map -> raw_red_expr -> Evd.evar_map * red_expr

(** Interprets tactic expressions *)

val interp_hyp :  interp_sign -> goal sigma -> identifier Loc.located -> identifier

val interp_bindings : interp_sign -> Environ.env -> Evd.evar_map ->
 glob_constr_and_expr bindings -> Evd.evar_map * constr bindings

val interp_open_constr_with_bindings : interp_sign -> Environ.env -> Evd.evar_map ->
  glob_constr_and_expr with_bindings -> Evd.evar_map * constr with_bindings

(** Initial call for interpretation *)

val eval_tactic : glob_tactic_expr -> tactic

(** Globalization + interpretation *)

val interp_tac_gen : (identifier * value) list -> identifier list ->
                 debug_info -> raw_tactic_expr -> tactic

val interp : raw_tactic_expr -> tactic

val eval_ltac_constr : goal sigma -> raw_tactic_expr -> Evd.evar_map * constr

(** Hides interpretation for pretty-print *)

val hide_interp : raw_tactic_expr -> tactic option -> tactic

(** Declare the xml printer *)
val declare_xml_printer :
  (out_channel -> Environ.env -> Evd.evar_map -> constr -> unit) -> unit

(** Internals that can be useful for syntax extensions. *)

exception CannotCoerceTo of string

val interp_ltac_var : (value -> 'a) -> interp_sign -> Environ.env option -> identifier Loc.located -> 'a

val interp_int : interp_sign -> identifier Loc.located -> int

val error_ltac_variable : Loc.t -> identifier -> Environ.env option -> value -> string -> 'a
