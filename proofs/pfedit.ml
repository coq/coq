
(* $Id$ *)

open Pp
open Util
open Names
open Sign
open Term
open Declarations
open Environ
open Evd
open Declare
open Typing
open Tacmach
open Proof_trees
open Proof_type
open Lib
open Astterm

(*********************************************************************)
(* Managing the proofs state                                         *)
(* Mainly contributed by C. Murthy                                   *)
(*********************************************************************)

type proof_topstate = {
  top_hyps : named_context * named_context;
  top_goal : goal;
  top_strength : strength }

let proof_edits =
  (Edit.empty() : (identifier,pftreestate,proof_topstate) Edit.t)

let get_all_proof_names () = Edit.dom proof_edits

let msg_proofs use_resume =
  match Edit.dom proof_edits with
    | [] -> [< 'sPC ; 'sTR"(No proof-editing in progress)." >]
    | l ->  [< 'sTR"." ; 'fNL ; 'sTR"Proofs currently edited:" ; 'sPC ;
               (prlist_with_sep pr_spc pr_id (get_all_proof_names ())) ;
	       'sTR"." ;
               (if use_resume then [< 'fNL ; 'sTR"Use \"Resume\" first." >]
              	else [< >])
            >]

let undo_default = 12
let undo_limit = ref undo_default

(*********************************************************************)
(*    Functions for decomposing and modifying the proof state        *)
(*********************************************************************)

let get_state () =
  match Edit.read proof_edits with
    | None -> errorlabstrm "Pfedit.get_state"
          [< 'sTR"No focused proof"; msg_proofs true >]
    | Some(_,pfs,ts) -> (pfs,ts)

let get_topstate ()    = snd(get_state())
let get_pftreestate () = fst(get_state())

(*i
let get_evmap_sign og =
  let og = match og with
    | Some n ->
        let pftree = get_pftreestate () in
        Some (nth_goal_of_pftreestate n pftree)
    | None ->
        try
          let pftree = get_pftreestate () in
          Some (nth_goal_of_pftreestate 1 pftree)
        with e when Logic.catchable_exception e -> 
	  None 
  in
  match og with
    | Some goal -> (project goal, pf_env goal)
    | _ -> (Evd.empty, Global.env())
i*)

let get_goal_context n =
  let pftree = get_pftreestate () in
  let goal = nth_goal_of_pftreestate n pftree in
  (project goal, pf_env goal)

let get_current_goal_context () = get_goal_context 1

let set_current_proof s = 
  try 
    Edit.focus proof_edits s
  with Invalid_argument "Edit.focus" ->
    errorlabstrm "Pfedit.set_proof"
      [< 'sTR"No such proof" ; (msg_proofs false) >]

let resume_proof = set_current_proof

let suspend_proof () =
  try 
    Edit.unfocus proof_edits
  with Invalid_argument "Edit.unfocus" ->
    errorlabstrm "Pfedit.suspend_current_proof"
      [< 'sTR"No active proof" ; (msg_proofs true) >]
      
let resume_last_proof () =
  match (Edit.last_focused proof_edits) with
    | None ->
        errorlabstrm "resume_last" [< 'sTR"No proof-editing in progress." >]
    | Some p -> 
	Edit.focus proof_edits p
	  
let get_current_proof_name () =
  match Edit.read proof_edits with
    | None ->
        errorlabstrm "Pfedit.get_proof"
          [< 'sTR"No focused proof" ; msg_proofs true >]
    | Some(na,_,_) -> na

let add_proof (na,pfs,ts) =
  Edit.create proof_edits (na,pfs,ts,Some !undo_limit)
    
let delete_proof na =
  try 
    Edit.delete proof_edits na
  with (UserError ("Edit.delete",_)) ->
    errorlabstrm "Pfedit.delete_proof"
      [< 'sTR"No such proof" ; msg_proofs false >]
      
let init_proofs () = Edit.clear proof_edits
		       
let mutate f =
  try 
    Edit.mutate proof_edits (fun _ pfs -> f pfs)
  with Invalid_argument "Edit.mutate" ->
    errorlabstrm "Pfedit.mutate"
      [< 'sTR"No focused proof" ; msg_proofs true >]

let start (na,ts) =
  let pfs = mk_pftreestate ts.top_goal in 
  add_proof(na,pfs,ts)
    
let restart_proof () =
  match Edit.read proof_edits with
    | None -> 
	errorlabstrm "Pfedit.restart"
          [< 'sTR"No focused proof to restart" ; msg_proofs true >]
    | Some(na,_,ts) -> 
	delete_proof na;
        start (na,ts);
        set_current_proof na

let proof_term () =
  extract_pftreestate (get_pftreestate())
    
(* Detect is one has completed a subtree of the initial goal *)
let subtree_solved () = 
  let pts = get_pftreestate () in
  is_complete_proof (proof_of_pftreestate pts) & 
  not (is_top_pftreestate pts)

(*********************************************************************)
(*                 Undo functions                                    *)
(*********************************************************************)
    
let set_undo n = 
  if n>=0 then 
    undo_limit := n+1
  else 
    error "Cannot set a negative undo limit"
      
let reset_undo  () = set_undo undo_default

let undo n =
  try 
    Edit.undo proof_edits n; 
       (* needed because the resolution of a subtree is done in 2 steps 
       then a sequence of undo can lead to a focus on a completely solved 
       subtree - this solution only works properly if undoing one step *)
    if subtree_solved() then  Edit.undo proof_edits 1
  with (Invalid_argument "Edit.undo") ->
    errorlabstrm "Pfedit.undo" [< 'sTR"No focused proof"; msg_proofs true >]

(*********************************************************************)
(*                  Proof cooking                                    *)
(*********************************************************************)

let cook_proof () =
  let (pfs,ts) = get_state() 
  and ident = get_current_proof_name () in
  let {evar_concl=concl} = ts.top_goal 
  and strength = ts.top_strength in
  let pfterm = extract_pftreestate pfs in
  (ident,
   ({ const_entry_body = pfterm; const_entry_type = Some concl },
    strength))

(*********************************************************************)
(*              Abort   functions                                    *)
(*********************************************************************)
 
let refining () = [] <> (Edit.dom proof_edits)

let check_no_pending_proofs () =
  if refining () then 
    errorlabstrm "check_no_pending_proofs"
      [< 'sTR"Proof editing in progress" ; (msg_proofs false) ;
         'sTR"Use \"Abort All\" first or complete proof(s)." >]

let delete_current_proof () = delete_proof (get_current_proof_name ())

let delete_all_proofs = init_proofs
   
(*********************************************************************)
(*              Modifying the current prooftree                      *)
(*********************************************************************)

let start_proof na str sign concl =
  let top_goal = mk_goal (mt_ctxt Intset.empty) sign concl in
  let ts = { 
    top_hyps = (sign,empty_named_context);
    top_goal = top_goal;
    top_strength = str }
  in
  start(na,ts);
  set_current_proof na

(*
let start_proof_constr na str concl =
  let sigma = Evd.empty in
  let env = Global.env() in
(* Si c'est un constr, il est supposé typable dans le contexte courant
  let _ = execute_type env sigma concl in
*)
  start_proof_with_type na str env concl
*)

let solve_nth k tac =
  let pft = get_pftreestate() in
  if not (List.mem (-1) (cursor_of_pftreestate pft)) then 
    mutate (solve_nth_pftreestate k tac)
  else 
    error "cannot apply a tactic when we are descended behind a tactic-node"

let by tac = mutate (solve_pftreestate tac)

let instantiate_nth_evar_com n c = mutate (instantiate_pf_com n c)

let traverse n = mutate (traverse n)
 
(* [traverse_to path]

   Traverses the current proof to get to the location specified by
   [path].

   ALGORITHM:

   If the cursor is equal to the path, we are done.

   If the cursor is longer than the path, then traverse to the parent

   If the cursor is equal to the tail of the path, then traverse to
   the head of the path, and we are done.

   Otherwise, traverse to the parent, traverse to the tail of the
   path, then traverse to the path.

*)

let rec nth_cdr = function
  | 0 -> (function l -> l)
  | n -> (compose List.tl (nth_cdr (n - 1)))
	
let rec common_ancestor_equal_length = function
  | ((a::l1), (b::l2)) ->
      let (prefx,n) as result = (common_ancestor_equal_length (l1,l2)) in
      if result = ([],0) then    
        if a = b then 
	  result
        else 
	  (a::prefx),(n + 1)
      else 
	(a::prefx),(n + 1)
  | ([], []) -> [],0
  | (_, _) -> anomaly "common_ancestor_equal_length"
	
let common_ancestor l1 l2 =
  let diff_lengths = (List.length l1) - (List.length l2) in
  if diff_lengths > 0 then
    let head,tail = list_chop diff_lengths l1 in
    let (prefx,n) = common_ancestor_equal_length (tail,l2) in 
    (head@prefx),n
  else if diff_lengths < 0 then
    let (prefx,n) = common_ancestor_equal_length
		      (l1, (nth_cdr (- diff_lengths) l2)) in
    prefx,(n - diff_lengths)
  else 
    common_ancestor_equal_length (l1,l2)
      
let rec traverse_up = function
  | 0 -> (function pf -> pf)
  | n -> (function pf -> Tacmach.traverse 0 (traverse_up (n - 1) pf))

let rec traverse_down = function
  | [] -> (function pf -> pf)
  | n::l -> (function pf -> Tacmach.traverse n (traverse_down l pf))

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
  let pts = get_pftreestate () in 
  if not (is_top_pftreestate pts) then mutate top_of_tree



