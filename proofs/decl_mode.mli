(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id:$ *)

open Names
open Term
open Evd

(*arnaud: types factices *)
type pftreestate
module Proof_type :
sig
  type goal
end

(*arnaud: /types factices *)

val set_daimon_flag : unit -> unit
val clear_daimon_flag : unit -> unit
val get_daimon_flag : unit -> bool

type command_mode =
    Mode_tactic
  | Mode_proof
  | Mode_none

val mode_of_pftreestate : pftreestate -> command_mode
    
val get_current_mode : unit -> command_mode

val check_not_proof_mode : string -> unit

type split_tree=
    Skip_patt of Idset.t * split_tree
  | Split_patt of Idset.t * inductive *
		(bool array * (Idset.t * split_tree) option) array
  | Close_patt of split_tree
  | End_patt of (identifier * int)

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
    Per of Decl_expr.elim_type * per_info * elim_kind * Names.identifier list
  | Suppose_case
  | Claim
  | Focus_claim

type pm_info =
    {pm_stack : stack_info list }

val pm_in : pm_info -> Dyn.t

val get_info : Proof_type.goal -> pm_info

val get_end_command : pftreestate -> string option

val get_stack : pftreestate -> stack_info list

val get_top_stack : pftreestate -> stack_info list

val get_last:  Environ.env -> identifier
