(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Tactic_debug
open EConstr
open Tacexpr
open Genarg
open Redexpr
open Tactypes

val ltac_trace_info : ltac_trace Exninfo.t

module Value :
sig
  type t = Geninterp.Val.t
  val of_constr : constr -> t
  val to_constr : t -> constr option
  val of_int : int -> t
  val to_int : t -> int option
  val to_list : t -> t list option
  val of_closure : Geninterp.interp_sign -> glob_tactic_expr -> t
  val cast : 'a typed_abstract_argument_type -> Geninterp.Val.t -> 'a
  val apply : t -> t list -> unit Proofview.tactic
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

val f_avoid_ids : Id.Set.t TacStore.field
val f_debug : debug_info TacStore.field

val extract_ltac_constr_values : interp_sign -> Environ.env ->
  Ltac_pretype.constr_under_binders Id.Map.t
(** Given an interpretation signature, extract all values which are coercible to
    a [constr]. *)

(** Sets the debugger mode *)
val set_debug : debug_info -> unit

(** Gives the state of debug *)
val get_debug : unit -> debug_info

val type_uconstr :
  ?flags:Pretyping.inference_flags ->
  ?expected_type:Pretyping.typing_constraint ->
  Geninterp.interp_sign -> Ltac_pretype.closed_glob_constr -> constr Tactypes.delayed_open

(** Adds an interpretation function for extra generic arguments *)

val interp_genarg : interp_sign -> glob_generic_argument -> Value.t Ftactic.t

(** Interprets any expression *)
val val_interp : interp_sign -> glob_tactic_expr -> (value -> unit Proofview.tactic) -> unit Proofview.tactic

(** Interprets an expression that evaluates to a constr *)
val interp_ltac_constr : interp_sign -> glob_tactic_expr -> (constr -> unit Proofview.tactic) -> unit Proofview.tactic

(** Interprets redexp arguments *)
val interp_redexp : Environ.env -> Evd.evar_map -> raw_red_expr -> Evd.evar_map * red_expr

(** Interprets tactic expressions *)

val interp_hyp : interp_sign -> Environ.env -> Evd.evar_map ->
  lident -> Id.t

val interp_glob_closure : interp_sign -> Environ.env -> Evd.evar_map ->
  ?kind:Pretyping.typing_constraint -> ?pattern_mode:bool -> glob_constr_and_expr ->
  Ltac_pretype.closed_glob_constr

val interp_uconstr : interp_sign -> Environ.env -> Evd.evar_map ->
  glob_constr_and_expr -> Ltac_pretype.closed_glob_constr

val interp_constr_gen : Pretyping.typing_constraint -> interp_sign ->
  Environ.env -> Evd.evar_map -> glob_constr_and_expr -> Evd.evar_map * constr

val interp_bindings : interp_sign -> Environ.env -> Evd.evar_map ->
  glob_constr_and_expr bindings -> Evd.evar_map * constr bindings

val interp_open_constr : ?expected_type:Pretyping.typing_constraint ->
  ?flags:Pretyping.inference_flags ->
  interp_sign -> Environ.env -> Evd.evar_map ->
  glob_constr_and_expr -> Evd.evar_map * EConstr.constr

val interp_open_constr_with_classes : ?expected_type:Pretyping.typing_constraint ->
  interp_sign -> Environ.env -> Evd.evar_map ->
  glob_constr_and_expr -> Evd.evar_map * EConstr.constr

val interp_open_constr_with_bindings : interp_sign -> Environ.env -> Evd.evar_map ->
  glob_constr_and_expr with_bindings -> Evd.evar_map * EConstr.constr with_bindings

(** Initial call for interpretation *)

val eval_tactic : glob_tactic_expr -> unit Proofview.tactic

val eval_tactic_ist : interp_sign -> glob_tactic_expr -> unit Proofview.tactic
(** Same as [eval_tactic], but with the provided [interp_sign]. *)

val tactic_of_value : interp_sign -> Value.t -> unit Proofview.tactic

(** Globalization + interpretation *)

val interp_tac_gen : value Id.Map.t -> Id.Set.t ->
                 debug_info -> raw_tactic_expr -> unit Proofview.tactic

val interp : raw_tactic_expr -> unit Proofview.tactic

(** Hides interpretation for pretty-print *)

val hide_interp : bool -> raw_tactic_expr -> unit Proofview.tactic option -> unit Proofview.tactic

(** Internals that can be useful for syntax extensions. *)

val interp_ltac_var : (value -> 'a) -> interp_sign ->
  (Environ.env * Evd.evar_map) option -> lident -> 'a

val interp_int : interp_sign -> lident -> int

val interp_int_or_var : interp_sign -> int Locus.or_var -> int

val default_ist : unit -> Geninterp.interp_sign
(** Empty ist with debug set on the current value. *)
