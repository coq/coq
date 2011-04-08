(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

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
open Proof_trees
open Tacexpr
open Proof_type
open Lib
open Safe_typing

(*********************************************************************)
(* Managing the proofs state                                         *)
(* Mainly contributed by C. Murthy                                   *)
(*********************************************************************)

type lemma_possible_guards = int list list

type proof_topstate = {
  mutable top_end_tac : tactic option;
  top_init_tac : tactic option;
  top_compute_guard : lemma_possible_guards;
  top_goal : goal;
  top_strength : Decl_kinds.goal_kind;
  top_hook : declaration_hook }

let proof_edits =
  (Edit.empty() : (identifier,pftreestate,proof_topstate) Edit.t)

let get_all_proof_names () = Edit.dom proof_edits

let msg_proofs use_resume =
  match Edit.dom proof_edits with
    | [] -> (spc () ++ str"(No proof-editing in progress).")
    | l ->  (str"." ++ fnl () ++ str"Proofs currently edited:" ++ spc () ++
               (prlist_with_sep pr_spc pr_id (get_all_proof_names ())) ++
	       str"." ++
               (if use_resume then (fnl () ++ str"Use \"Resume\" first.")
              	else (mt ()))
)

let undo_default = 50
let undo_limit = ref undo_default

(*********************************************************************)
(*    Functions for decomposing and modifying the proof state        *)
(*********************************************************************)

let get_state () =
  match Edit.read proof_edits with
    | None -> errorlabstrm "Pfedit.get_state"
          (str"No focused proof" ++ msg_proofs true)
    | Some(_,pfs,ts) -> (pfs,ts)

let get_topstate ()    = snd(get_state())
let get_pftreestate () = fst(get_state())

let get_end_tac () = let ts = get_topstate () in ts.top_end_tac

let get_goal_context n =
  let pftree = get_pftreestate () in
  let goal = nth_goal_of_pftreestate n pftree in
  (project goal, pf_env goal)

let get_current_goal_context () = get_goal_context 1

let set_current_proof = Edit.focus proof_edits

let resume_proof (loc,id) =
  try
    Edit.focus proof_edits id
  with Invalid_argument "Edit.focus" ->
    user_err_loc(loc,"Pfedit.set_proof",str"No such proof" ++ msg_proofs false)

let suspend_proof () =
  try
    Edit.unfocus proof_edits
  with Invalid_argument "Edit.unfocus" ->
    errorlabstrm "Pfedit.suspend_current_proof"
      (str"No active proof" ++ (msg_proofs true))

let resume_last_proof () =
  match (Edit.last_focused proof_edits) with
    | None ->
        errorlabstrm "resume_last" (str"No proof-editing in progress.")
    | Some p ->
	Edit.focus proof_edits p

let get_current_proof_name () =
  match Edit.read proof_edits with
    | None ->
        errorlabstrm "Pfedit.get_proof"
          (str"No focused proof" ++ msg_proofs true)
    | Some(na,_,_) -> na

let add_proof (na,pfs,ts) =
  Edit.create proof_edits (na,pfs,ts,!undo_limit+1)

let delete_proof_gen = Edit.delete proof_edits

let delete_proof (loc,id) =
  try
    delete_proof_gen id
  with (UserError ("Edit.delete",_)) ->
    user_err_loc
      (loc,"Pfedit.delete_proof",str"No such proof" ++ msg_proofs false)

let mutate f =
  try
    Edit.mutate proof_edits (fun _ pfs -> f pfs)
  with Invalid_argument "Edit.mutate" ->
    errorlabstrm "Pfedit.mutate"
      (str"No focused proof" ++ msg_proofs true)

let start (na,ts) =
  let pfs = mk_pftreestate ts.top_goal in
  let pfs = Option.fold_right solve_pftreestate ts.top_init_tac pfs in
  add_proof(na,pfs,ts)

let restart_proof () =
  match Edit.read proof_edits with
    | None ->
	errorlabstrm "Pfedit.restart"
          (str"No focused proof to restart" ++ msg_proofs true)
    | Some(na,_,ts) ->
	delete_proof_gen na;
        start (na,ts);
        set_current_proof na

let proof_term () =
  extract_pftreestate (get_pftreestate())

(* Detect is one has completed a subtree of the initial goal *)
let subtree_solved () =
  let pts = get_pftreestate () in
  is_complete_proof (proof_of_pftreestate pts) &
  not (is_top_pftreestate pts)

let tree_solved () =
  let pts = get_pftreestate () in
  is_complete_proof (proof_of_pftreestate pts)

let top_tree_solved () =
  let pts = get_pftreestate () in
  is_complete_proof (proof_of_pftreestate (top_of_tree pts))

(*********************************************************************)
(*                 Undo functions                                    *)
(*********************************************************************)

let set_undo = function
  | None -> undo_limit := undo_default
  | Some n ->
      if n>=0 then
	undo_limit := n
      else
	error "Cannot set a negative undo limit"

let get_undo () = Some !undo_limit

let undo n =
  try
    Edit.undo proof_edits n;
       (* needed because the resolution of a subtree is done in 2 steps
       then a sequence of undo can lead to a focus on a completely solved
       subtree - this solution only works properly if undoing one step *)
    if subtree_solved() then  Edit.undo proof_edits 1
  with (Invalid_argument "Edit.undo") ->
    errorlabstrm "Pfedit.undo" (str"No focused proof" ++ msg_proofs true)

(* Undo current focused proof to reach depth [n]. This is used in
   [vernac_backtrack]. *)
let undo_todepth n =
  try
    Edit.undo_todepth proof_edits n
  with (Invalid_argument "Edit.undo") ->
    errorlabstrm "Pfedit.undo" (str"No focused proof" ++ msg_proofs true)

(* Return the depth of the current focused proof stack, this is used
   to put informations in coq prompt (in emacs mode). *)
let current_proof_depth() =
  try
    Edit.depth proof_edits
  with (Invalid_argument "Edit.depth") -> -1

(*********************************************************************)
(*                  Proof cooking                                    *)
(*********************************************************************)

let xml_cook_proof = ref (fun _ -> ())
let set_xml_cook_proof f = xml_cook_proof := f

let cook_proof k =
  let (pfs,ts) = get_state()
  and ident = get_current_proof_name () in
  let {evar_concl=concl} = ts.top_goal
  and strength = ts.top_strength in
  let pfterm = extract_pftreestate pfs in
  !xml_cook_proof (strength,pfs);
  k pfs;
  (ident,
   ({ const_entry_body = pfterm;
      const_entry_type = Some concl;
      const_entry_opaque = true;
      const_entry_boxed = false},
    ts.top_compute_guard, strength, ts.top_hook))

let current_proof_statement () =
  let ts = get_topstate() in
  (get_current_proof_name (), ts.top_strength,
   ts.top_goal.evar_concl, ts.top_hook)

(*********************************************************************)
(*              Abort   functions                                    *)
(*********************************************************************)

let refining () = [] <> (Edit.dom proof_edits)

let check_no_pending_proofs () =
  if refining () then
    errorlabstrm "check_no_pending_proofs"
      (str"Proof editing in progress" ++ (msg_proofs false) ++ fnl() ++
         str"Use \"Abort All\" first or complete proof(s).")

let delete_current_proof () = delete_proof_gen (get_current_proof_name ())

let delete_all_proofs () = Edit.clear proof_edits

(*********************************************************************)
(*   Modifying the end tactic of the current profftree               *)
(*********************************************************************)
let set_end_tac tac =
  let top = get_topstate () in
  top.top_end_tac <- Some tac

(*********************************************************************)
(*              Modifying the current prooftree                      *)
(*********************************************************************)

let start_proof na str sign concl ?init_tac ?(compute_guard=[]) hook =
  let top_goal = mk_goal sign concl None in
  let ts = {
    top_end_tac = None;
    top_init_tac = init_tac;
    top_compute_guard = compute_guard;
    top_goal = top_goal;
    top_strength = str;
    top_hook = hook}
  in
  start(na,ts);
  set_current_proof na

let solve_nth k tac =
  let pft = get_pftreestate () in
  if not (List.mem (-1) (cursor_of_pftreestate pft)) then
    mutate (solve_nth_pftreestate k tac)
  else
    error "cannot apply a tactic when we are descended behind a tactic-node"

let by tac = mutate (solve_pftreestate tac)

let instantiate_nth_evar_com n c =
  mutate (Evar_refiner.instantiate_pf_com n c)

let traverse n = mutate (traverse n)

(* [traverse_to path]

   Traverses the current proof to get to the location specified by
   [path].

   ALGORITHM: The algorithm works on reversed paths. One just has to remove
   the common part on the reversed paths.

*)

let common_ancestor l1 l2 =
  let rec common_aux l1 l2 =
    match l1, l2 with
      | a1::l1', a2::l2' when a1 = a2 -> common_aux l1' l2'
      | _, _ -> List.rev l1, List.length l2
  in
  common_aux (List.rev l1) (List.rev l2)

let rec traverse_up = function
  | 0 -> (function pf -> pf)
  | n -> (function pf -> Refiner.traverse 0 (traverse_up (n - 1) pf))

let rec traverse_down = function
  | [] -> (function pf -> pf)
  | n::l -> (function pf -> Refiner.traverse n (traverse_down l pf))

let traverse_to path =
  let up_and_down path pfs =
    let cursor = cursor_of_pftreestate pfs in
    let down_list, up_count = common_ancestor path cursor in
    traverse_down down_list (traverse_up up_count pfs)
  in
  mutate (up_and_down path)

(* traverse the proof tree until it reach the nth subgoal *)
let traverse_nth_goal n = mutate (nth_unproven n)

let traverse_prev_unproven () = mutate prev_unproven

let traverse_next_unproven () = mutate next_unproven

(* The goal focused on *)
let focus_n = ref 0
let make_focus n = focus_n := n
let focus () = !focus_n
let focused_goal () = let n = !focus_n in if n=0 then 1 else n

let reset_top_of_tree () =
  mutate top_of_tree

let reset_top_of_script () =
  mutate (fun pts ->
	try
	 up_until_matching_rule is_proof_instr pts
	with Not_found -> top_of_tree pts)

(**********************************************************************)
(* Shortcut to build a term using tactics *)

open Decl_kinds

let next = let n = ref 0 in fun () -> incr n; !n

let build_constant_by_tactic id sign typ tac =
  start_proof id (Global,Proof Theorem) sign typ (fun _ _ -> ());
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
