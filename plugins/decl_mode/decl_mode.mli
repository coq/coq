(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Term
open Evd

val set_daimon_flag : unit -> unit
val clear_daimon_flag : unit -> unit
val get_daimon_flag : unit -> bool

type command_mode =
    Mode_tactic
  | Mode_proof
  | Mode_none

val mode_of_pftreestate : Proof.proof -> command_mode

val get_current_mode : unit -> command_mode

val check_not_proof_mode : string -> unit

type split_tree=
    Skip_patt of Id.Set.t * split_tree
  | Split_patt of Id.Set.t * inductive *
		(bool array * (Id.Set.t * split_tree) option) array
  | Close_patt of split_tree
  | End_patt of (Id.t * (int * int))

type elim_kind =
    EK_dep of split_tree
  | EK_nodep
  | EK_unknown

type recpath = int option*Declarations.wf_paths

type per_info =
    {per_casee:constr;
     per_ctype:types;
     per_ind:inductive;
     per_pred:constr;
     per_args:constr list;
     per_params:constr list;
     per_nparams:int;
     per_wf:recpath}

type stack_info =
    Per of Decl_expr.elim_type * per_info * elim_kind * Names.Id.t list
  | Suppose_case
  | Claim
  | Focus_claim

type pm_info =
    {pm_stack : stack_info list }

val info : pm_info Store.field

val get_info : Evd.evar_map -> Proof_type.goal -> pm_info

val try_get_info : Evd.evar_map -> Proof_type.goal -> pm_info option

val get_stack : Proof.proof -> stack_info list

val get_top_stack : Proof.proof -> stack_info list

val get_last:  Environ.env -> Id.t
(** [get_last] raises a [UserError] when it cannot find a previous
    statement in the environment. *)

val focus : Proof.proof -> unit

val unfocus : unit -> unit

val maximal_unfocus : unit -> unit
