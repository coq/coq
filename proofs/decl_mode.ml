(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id:$ i*)

open Names
open Term
open Evd
open Util

let daimon_flag = ref false

let set_daimon_flag () = daimon_flag:=true
let clear_daimon_flag () = daimon_flag:=false
let get_daimon_flag () = !daimon_flag

type command_mode =
    Mode_tactic
  | Mode_proof
  | Mode_none

let mode_of_pftreestate pts =
  let goal = sig_it (Refiner.top_goal_of_pftreestate pts) in
    if goal.evar_extra = None then
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
    Per of Decl_expr.elim_type * per_info * elim_kind * identifier list
  | Suppose_case
  | Claim
  | Focus_claim

type pm_info =
    { pm_stack : stack_info list}

let pm_in,pm_out = Dyn.create "pm_info"

let get_info gl=
  match gl.evar_extra with
      None ->  invalid_arg "get_info"
    | Some extra ->
	try pm_out extra with _ -> invalid_arg "get_info"

let get_stack pts =
  let info = get_info (sig_it (Refiner.nth_goal_of_pftreestate 1 pts)) in
    info.pm_stack

let get_top_stack pts =
  let info = get_info (sig_it (Refiner.top_goal_of_pftreestate pts)) in
    info.pm_stack

let get_end_command pts =
  match mode_of_pftreestate pts with
      Mode_proof ->
	Some
	  begin
	    match get_top_stack pts with
		[] -> "\"end proof\""
	      | Claim::_ -> "\"end claim\""
	      | Focus_claim::_-> "\"end focus\""
	      | (Suppose_case :: Per (et,_,_,_) :: _
		| Per (et,_,_,_) :: _ ) ->
		  begin
		    match et with
			Decl_expr.ET_Case_analysis ->
			  "\"end cases\" or start a new case"
		      | Decl_expr.ET_Induction ->
			  "\"end induction\" or start a new case"
		  end
	      | _ -> anomaly "lonely suppose"
	  end
    | Mode_tactic ->
	begin
	  try
	    ignore
	      (Refiner.up_until_matching_rule Proof_trees.is_proof_instr pts);
	    Some "\"return\""
	  with Not_found -> None
	end
    | Mode_none ->
        error "no proof in progress"

let get_last env =
  try
    let (id,_,_) =  List.hd (Environ.named_context env) in id
  with Invalid_argument _ -> error "no previous statement to use"
