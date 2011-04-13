(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Util
open Names
open Nameops
open Sign
open Term
open Declarations
open Entries
open Environ
open Evd
open Typing
open Refiner
open Tacexpr
open Proof_type
open Lib
open Safe_typing

let refining = Proof_global.there_are_pending_proofs
let check_no_pending_proofs = Proof_global.check_no_pending_proof

let get_current_proof_name = Proof_global.get_current_proof_name
let get_all_proof_names = Proof_global.get_all_proof_names

type lemma_possible_guards = Proof_global.lemma_possible_guards

let delete_proof = Proof_global.discard
let delete_current_proof = Proof_global.discard_current
let delete_all_proofs = Proof_global.discard_all

let undo n = 
  let p = Proof_global.give_me_the_proof () in
  for i = 1 to n do
    Proof.undo p
  done

let current_proof_depth () =
  try
    let p = Proof_global.give_me_the_proof () in
    Proof.V82.depth p
  with Proof_global.NoCurrentProof -> -1

(* [undo_todepth n] resets the proof to its nth step (does [undo (d-n)] where d
   is the depth of the focus stack). *)
let undo_todepth n =
  try
    undo ((current_proof_depth ()) - n )
  with Proof_global.NoCurrentProof  when n=0 -> ()

let set_undo _ = ()
let get_undo _ = None


let start_proof id str hyps c ?init_tac ?compute_guard hook = 
  let goals = [ (Global.env_of_context hyps , c) ] in
  let init_tac = Option.map Proofview.V82.tactic init_tac in
  Proof_global.start_proof id str goals ?compute_guard hook;
  Option.iter Proof_global.run_tactic init_tac

let restart_proof () =
  let p = Proof_global.give_me_the_proof () in
  try while true do
    Proof.undo p
  done with Proof.EmptyUndoStack -> ()

let resume_last_proof () = Proof_global.resume_last ()
let resume_proof (_,id) = Proof_global.resume id
let suspend_proof ()  =  Proof_global.suspend ()

let cook_proof hook =
  let prf = Proof_global.give_me_the_proof () in
  hook prf;
  match Proof_global.close_proof () with
  | (i,([e],cg,str,h)) -> (i,(e,cg,str,h))
  | _ -> Util.anomaly "Pfedit.cook_proof: more than one proof term."

let xml_cook_proof = ref (fun _ -> ())
let set_xml_cook_proof f = xml_cook_proof := f

let get_pftreestate () =
  Proof_global.give_me_the_proof ()

let set_end_tac tac =
  let tac = Proofview.V82.tactic tac in
  Proof_global.set_endline_tactic tac

exception NoSuchGoal
let get_nth_V82_goal i =
  let p = Proof_global.give_me_the_proof () in
  let { it=goals ; sigma = sigma } = Proof.V82.subgoals p in
  try
    { it=(List.nth goals (i-1)) ; sigma=sigma }
  with Failure _ -> raise NoSuchGoal
    
let get_goal_context_gen i =
  try
    let { it=goal ; sigma=sigma } =  get_nth_V82_goal i in
    (sigma, Refiner.pf_env { it=goal ; sigma=sigma })
  with Proof_global.NoCurrentProof -> Util.error "No focused proof."

let get_goal_context i =
  try get_goal_context_gen i
  with NoSuchGoal -> Util.error "No such goal."

let get_current_goal_context () =
  try get_goal_context_gen 1
  with NoSuchGoal ->
    (* spiwack: returning empty evar_map, since if there is no goal, under focus,
        there is no accessible evar either *)
    (Evd.empty, Global.env ())

let current_proof_statement () =
  match Proof_global.V82.get_current_initial_conclusions () with
    | (id,([concl],strength,hook)) -> id,strength,concl,hook
    | _ -> Util.anomaly "Pfedit.current_proof_statement: more than one statement"

let solve_nth ?(with_end_tac=false) gi tac = 
  try 
    let tac = Proofview.V82.tactic tac in
    let tac = if with_end_tac then 
                Proof_global.with_end_tac tac
              else
		tac
    in
    Proof_global.run_tactic (Proofview.tclFOCUS gi gi tac) 
  with 
    | Proof_global.NoCurrentProof  -> Util.error "No focused proof"
    | Proofview.IndexOutOfRange | Failure "list_chop" -> 
	let msg = str "No such goal: " ++ int gi ++ str "." in
	Util.errorlabstrm "" msg

let by = solve_nth 1

let instantiate_nth_evar_com n com = 
  let pf = Proof_global.give_me_the_proof () in
  Proof.V82.instantiate_evar n com pf


(**********************************************************************)
(* Shortcut to build a term using tactics *)

open Decl_kinds

let next = let n = ref 0 in fun () -> incr n; !n

let build_constant_by_tactic id sign typ tac =
  start_proof id (Global,false,Proof Theorem) sign typ (fun _ _ -> ());
  try
    by tac;
    let _,(const,_,_,_) = cook_proof (fun _ -> ()) in
    delete_current_proof ();
    const
  with e ->
    delete_current_proof ();
    raise e

let build_by_tactic typ tac =
  let id = id_of_string ("temporary_proof"^string_of_int (next())) in
  let sign = Decls.clear_proofs (Global.named_context ()) in
  (build_constant_by_tactic id sign typ tac).const_entry_body
