(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Term
open Evd
open Errors
open Util


let daimon_flag = ref false

let set_daimon_flag () = daimon_flag:=true
let clear_daimon_flag () = daimon_flag:=false
let get_daimon_flag () = !daimon_flag



(* Information associated to goals. *)
open Store.Field

type split_tree=
    Skip_patt of Idset.t * split_tree
  | Split_patt of Idset.t * inductive *
		(bool array * (Idset.t * split_tree) option) array
  | Close_patt of split_tree
  | End_patt of (identifier * (int * int))

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
    Per of Decl_expr.elim_type * per_info * elim_kind * identifier list
  | Suppose_case
  | Claim
  | Focus_claim

type pm_info =
    { pm_stack : stack_info list}
let info = Store.field ()


(* Current proof mode *)

type command_mode =
    Mode_tactic
  | Mode_proof
  | Mode_none

let mode_of_pftreestate pts =
  (* spiwack: it used to be "top_goal_..." but this should be fine *)
  let { it = goals ; sigma = sigma } = Proof.V82.subgoals pts in
  let goal = List.hd goals in
    if info.get (Goal.V82.extra sigma goal) = None then
      Mode_tactic 
    else
      Mode_proof
	  
let get_current_mode () =
  try 
    mode_of_pftreestate (Pfedit.get_pftreestate ())
  with _ -> Mode_none

let check_not_proof_mode str =
 if get_current_mode () = Mode_proof then
   error str

let get_info sigma gl=
  match info.get (Goal.V82.extra sigma gl) with
  | None ->  invalid_arg "get_info"
  | Some pm -> pm

let try_get_info sigma gl =
  info.get (Goal.V82.extra sigma gl)

let get_stack pts =
  let { it = goals ; sigma = sigma } = Proof.V82.subgoals pts in
  let info = get_info sigma (List.hd goals) in
  info.pm_stack


let proof_focus = Proof.new_focus_kind ()
let proof_cond = Proof.no_cond proof_focus

let focus p =
  let inf = get_stack p in
  Proof.focus proof_cond inf 1 p

let unfocus = Proof.unfocus proof_focus

let maximal_unfocus = Proof_global.maximal_unfocus proof_focus

let get_top_stack pts =
  try
    Proof.get_at_focus proof_focus pts
  with Proof.NoSuchFocus ->
    let { it = gl ; sigma = sigma } = Proof.V82.top_goal pts in
    let info = get_info sigma gl in
    info.pm_stack

let get_last env =
  try
    let (id,_,_) =  List.hd (Environ.named_context env) in id
  with Invalid_argument _ -> error "no previous statement to use"

