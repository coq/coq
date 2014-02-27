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

module Value :
sig
  type t = tlevel generic_argument
  val of_constr : constr -> t
  val to_constr : t -> constr option
  val of_int : int -> t
  val to_int : t -> int option
  val to_list : t -> t list option
end

(** Values for interpretation *)
type value = Value.t

module TacStore : Store.S with
  type t = Geninterp.TacStore.t
  and type 'a field = 'a Geninterp.TacStore.field

(** Signature for interpretation: val\_interp and interpretation functions *)
type interp_sign = Geninterp.interp_sign = {
  lfun : value Id.Map.t;
  extra : TacStore.t }

val f_avoid_ids : Id.t list TacStore.field
val f_debug : debug_info TacStore.field

val extract_ltac_constr_values : interp_sign -> Environ.env ->
  Pattern.constr_under_binders Id.Map.t
(** Given an interpretation signature, extract all values which are coercible to
    a [constr]. *)

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

(* spiwack: the [Term.constr] argument is the conclusion of the goal,
   for "casted open constr" *)
val interp_genarg : interp_sign -> Environ.env -> Evd.evar_map -> Term.constr -> Goal.goal ->
  glob_generic_argument -> Evd.evar_map * typed_generic_argument

(** Interprets any expression *)
val val_interp : interp_sign -> glob_tactic_expr -> value Proofview.glist Proofview.tactic

(** Interprets an expression that evaluates to a constr *)
val interp_ltac_constr : interp_sign -> glob_tactic_expr -> constr Proofview.glist Proofview.tactic

(** Interprets redexp arguments *)
val interp_redexp : Environ.env -> Evd.evar_map -> raw_red_expr -> Evd.evar_map * red_expr

(** Interprets tactic expressions *)

val interp_hyp :  interp_sign -> Environ.env -> Id.t Loc.located -> Id.t

val interp_bindings : interp_sign -> Environ.env -> Evd.evar_map ->
 glob_constr_and_expr bindings -> Evd.evar_map * constr bindings

val interp_open_constr_with_bindings : interp_sign -> Environ.env -> Evd.evar_map ->
  glob_constr_and_expr with_bindings -> Evd.evar_map * constr with_bindings

(** Initial call for interpretation *)

val eval_tactic : glob_tactic_expr -> unit Proofview.tactic

val eval_tactic_ist : interp_sign -> glob_tactic_expr -> unit Proofview.tactic
(** Same as [eval_tactic], but with the provided [interp_sign]. *)

(** Globalization + interpretation *)

val interp_tac_gen : value Id.Map.t -> Id.t list ->
                 debug_info -> raw_tactic_expr -> unit Proofview.tactic

val interp : raw_tactic_expr -> unit Proofview.tactic

(** Hides interpretation for pretty-print *)

val hide_interp : bool -> raw_tactic_expr -> unit Proofview.tactic option -> unit Proofview.tactic

(** Declare the xml printer *)
val declare_xml_printer :
  (out_channel -> Environ.env -> Evd.evar_map -> constr -> unit) -> unit

(** Internals that can be useful for syntax extensions. *)

val interp_ltac_var : (value -> 'a) -> interp_sign -> Environ.env option -> Id.t Loc.located -> 'a

val interp_int : interp_sign -> Id.t Loc.located -> int

val error_ltac_variable : Loc.t -> Id.t -> Environ.env option -> value -> string -> 'a
