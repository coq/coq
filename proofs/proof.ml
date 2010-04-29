(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Module defining the last essential tiles of interactive proofs.
   The features of the Proof module are undoing and focusing.
   A proof is a mutable object, it contains a proofview, and some information
   to be able to undo actions, and to unfocus the current view. All three
   of these being meant to evolve.
   - Proofview: a proof is primarily the data of the current view.
     That which is shown to the user (as a remainder, a proofview
     is mainly the logical state of the proof, together with the
     currently focused goals).
   - Focus: a proof has a focus stack: the top of the stack contains
     the context in which to unfocus the current view to a view focused
     with the rest of the stack.
     In addition, this contains, for each of the focus context,  a 
     "focus kind" and a "focus condition" (in practice, and for modularity,
     the focus kind is actually stored inside the condition). To unfocus, one
     needs to know the focus kind, and the condition (for instance "no condition" or
     the proof under focused must be complete) must be met.
   - Undo: since proofviews and focus stacks are immutable objects, 
     it could suffice to hold the previous states, to allow to return to the past.
     However, we also allow other modules to do actions that can be undone.
     Therefore the undo stack stores action to be ran to undo.
*)

open Term

type focus_kind = int
type focus_condition = focus_kind -> Proofview.proofview -> bool

let next_kind = ref 0
let new_focus_kind () =
  let r = !next_kind in
  incr next_kind;
  r

(* To be authorized to unfocus one must meet the condition prescribed by
    the action which focused.*)
(* spiwack: we could consider having a list of authorized focus_kind instead
    of just one, if anyone needs it *)
(* [no_cond] only checks that the unfocusing command uses the right
    [focus_kind]. *)
let no_cond k0 k _ = k0 = k
(* [done_cond] checks that the unfocusing command uses the right [focus_kind]
    and that the focused proofview is complete. *)
let done_cond k0 k p = k0 = k && Proofview.finished p


(* Subpart of the type of proofs. It contains the parts of the proof which
   are under control of the undo mechanism *)
type proof_state = {
  (* Current focused proofview *)
  proofview: Proofview.proofview;
  (* History of the focusings, provides information on how
     to unfocus the proof.
     The list is empty when the proof is fully unfocused. *)
  focus_stack: (focus_condition*Proofview.focus_context) list;
  (* Extra information which can be freely used to create new behaviours. *)
  intel: Store.t
}

type proof_info = {
  mutable endline_tactic : unit Proofview.tactic ;
  initial_conclusions : Term.types list
}

type undo_action = 
  | State of proof_state
  | Effect of (unit -> unit)

type proof = { (* current proof_state *)
               mutable state : proof_state;
               (* The undo stack *)
               mutable undo_stack : undo_action list;
	       info : proof_info
             }


(*** General proof functions ***)

let start goals =
  { state = { proofview = Proofview.init goals ;
	             focus_stack = [] ;
	             intel = Store.empty} ;
      undo_stack = [] ;
      info = { endline_tactic = Proofview.tclUNIT ();
	            initial_conclusions = List.map snd goals }
  }

let rec unroll_focus pv = function
  | (_,ctx)::stk -> unroll_focus (Proofview.unfocus ctx pv) stk
  | [] -> pv

(* spiwack: a proof is considered completed even if its still focused, if the focus
                   doesn't hide any goal. *)
let is_done p =
  Proofview.finished p.state.proofview && 
  Proofview.finished (unroll_focus p.state.proofview p.state.focus_stack)

(* spiwack: for compatibility with <= 8.2 proof engine *)
let has_unresolved_evar p =
  Proofview.V82.has_unresolved_evar p.state.proofview

(* Returns the list of partial proofs to initial goals *)
let partial_proof p =
  List.map fst (Proofview.return p.state.proofview)

exception UnfinishedProof
exception HasUnresolvedEvar
let return p =
  if not (is_done p) then
    raise UnfinishedProof
  else if has_unresolved_evar p then 
    (* spiwack: for compatibility with <= 8.2 proof engine *)
    raise HasUnresolvedEvar
  else
    Proofview.return p.state.proofview

(*** The following functions implement the basic internal mechanisms
     of proofs, they are not meant to be exported in the .mli ***)

(* An auxiliary function to push a {!focus_context} on the focus stack. *)
let push_focus kind context pr =
  pr.state <- { pr.state with focus_stack = (kind,context)::pr.state.focus_stack }

exception FullyUnfocused

(* An auxiliary function to read the kind of the next focusing step *)
let cond_of_focus pr =
  match pr.state.focus_stack with
  | (cond,_)::_ -> cond
  | _ -> raise FullyUnfocused

(* An auxiliary function to pop and read the last {!Proofview.focus_context} 
   on the focus stack. *)
let pop_focus pr =
  match pr.state.focus_stack with
  | focus::other_focuses -> 
      pr.state <- { pr.state with focus_stack = other_focuses }; focus
  | _ -> 
      raise FullyUnfocused

(* Auxiliary function to push a [proof_state] onto the undo stack. *)
let push_undo save ({ undo_stack = stack } as pr) =
  pr.undo_stack <- save::stack

(* Auxiliary function to pop and read a [save_state] from the undo stack. *)
exception EmptyUndoStack
let pop_undo pr = 
  match pr.undo_stack with
  | state::stack -> pr.undo_stack <- stack; state
  | _ -> raise EmptyUndoStack


(* This function focuses the proof [pr] between indices [i] and [j] *)
let _focus cond i j pr =
  let (focused,context) = Proofview.focus i j pr.state.proofview in
  push_focus cond context pr;
  pr.state <- { pr.state with proofview = focused }

(* This function unfocuses the proof [pr], it raises [CannotUnfocus],
   if the proof is already fully unfocused.
   This function does not care about the condition of the current focus. *)
let _unfocus pr =
  let (_,fc) = pop_focus pr in
  pr.state <- { pr.state with proofview = Proofview.unfocus fc pr.state.proofview }


(*** Endline tactic ***)

(* spiwack this is an information about the UI, it might be a good idea to move
   it to the Proof_global module *)

(* Sets the tactic to be used when a tactic line is closed with [...] *)
let set_endline_tactic tac p =
 p.info.endline_tactic <- tac

let with_end_tac pr tac =
  Proofview.tclTHEN tac pr.info.endline_tactic

(*** The following functions define the safety mechanism of the
     proof system, they may be unsafe if not used carefully. There is
     currently no reason to export them in the .mli ***)

(* This functions saves the current state into a [proof_state]. *)
let save_state { state = ps } = State ps

(* This function stores the current proof state in the undo stack. *)
let save pr =
  push_undo (save_state pr) pr

(* This function restores a state, presumably from the top of the undo stack. *)
let restore_state save pr = 
  match save with
  | State save -> pr.state <- save
  | Effect undo -> undo ()

(* Interpretes the Undo command. *)
let undo pr = 
  (* On a single line, since the effects commute *)
  restore_state (pop_undo pr) pr

(* Adds an undo effect to the undo stack. Use it with care, errors here might result
    in inconsistent states. *)
let add_undo effect pr =
  push_undo (Effect effect) pr

(* Focus command (focuses on the [i]th subgoal) *)
(* spiwack: there could also, easily be a focus-on-a-range tactic, is there 
   a need for it? *)
let focus cond i pr =
  save pr;
  _focus cond i i pr

(* Unfocus command.
   Fails if the proof is not focused. *)
let unfocus kind pr =
  let starting_point = save_state pr in
  try
    let cond = cond_of_focus pr in
    if cond kind pr.state.proofview then
      (_unfocus pr;
       push_undo starting_point pr)
    else
      Util.error "This proof is focused, but cannot be unfocused this way"
  with FullyUnfocused -> 
    Util.error "This proof is not focused"

let no_focused_goal p =
  Proofview.finished p.state.proofview

(*** Function manipulation proof extra informations ***)

let get_proof_info pr =
  pr.state.intel

let set_proof_info info pr =
  save pr;
  pr.state <- { pr.state with intel=info }


(*** Tactics ***)

let run_tactic env tac pr =
  let starting_point = save_state pr in
  let sp = pr.state.proofview in
  try
    let tacticced_proofview = Proofview.apply env tac sp in
    pr.state <- { pr.state with proofview = tacticced_proofview };
    push_undo starting_point pr
  with e -> 
    restore_state starting_point pr;
    raise e
  


(*** Compatibility layer with <=v8.2 ***)
module V82 = struct
  let subgoals p =
    Proofview.V82.goals p.state.proofview

  let background_subgoals p =
    Proofview.V82.goals (unroll_focus p.state.proofview p.state.focus_stack)

  let get_initial_conclusions p = 
    p.info.initial_conclusions

  let depth p = List.length p.undo_stack

  let top_goal p = 
    let { Evd.it=gls ; sigma=sigma } = 
	Proofview.V82.top_goals p.state.proofview
    in
    { Evd.it=List.hd gls ; sigma=sigma }

  let instantiate_evar n com pr =
    let starting_point = save_state pr in
    let sp = pr.state.proofview in
    try
      let new_proofview = Proofview.V82.instantiate_evar n com sp in
      pr.state <- { pr.state with proofview = new_proofview };
      push_undo starting_point pr
    with e -> 
      restore_state starting_point pr;
      raise e
end
