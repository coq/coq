(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

(* arnaud: rajouter le blabla sur la  théorie du module ici. Le undo ! Le undo ! Note importante : une preuve est un record mutable de truc immutables !*)

open Term
type subproof = Subproof.subproof (* rather than opening Subproof *)

(* arnaud: transactional_stack retiré le 19 decembre 2007, il est trouvable
   dans la révision 10394 *)
(* arnaud: sequence retiré le 20 décembre 2007, il est aussi trouvable dans
   la révision 10394 (ainsi que quelques suivantes). *)

type focus_kind = 
  | FocusCommand
  | InternalFocus

(* Subpart of the type of proofs. It contains the parts of the proof which
   are controled by the undo mechanism *)
type proof_state = {
  (* Current focused subproof *)
  subproof: subproof;
  (* History of the focusings, provides information on how
     to unfocus the proof.
     The list is empty when the proof is fully unfocused. *)
  focus_stack: (focus_kind*Subproof.focus_context) list
}

type 'a proof = { (* current proof_state *)
                  mutable state : proof_state;
		  (* The undo stack *)
		  mutable undo_stack : proof_state list;
                  (* function executed at QED. *)
		  return: constr list -> 'a
		}



(*** The following functions implement the basic internal mechanisms
     of proofs, they are not meant to be exported in the .mli ***)

(* An auxiliary function to push a {!focus_context} on the focus stack. *)
let push_focus kind context pr =
  pr.state <- { pr.state with focus_stack = (kind,context)::pr.state.focus_stack }

exception FullyUnfocused

(* An auxiliary function to read the kind of the next focusing step *)
let kind_of_focus pr =
  match pr.state.focus_stack with
  | (kind,_)::_ -> kind
  | _ -> raise FullyUnfocused

(* An auxiliary function to pop and read the last {!Subproof.focus_context} 
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
let _focus ?(kind=InternalFocus) i j pr =
  let (focused,context) = Subproof.focus i j pr.state.subproof in
  push_focus kind context pr;
  pr.state <- { pr.state with subproof = focused }

(* This function unfocuses the proof [pr], it raises [CannotUnfocus],
   if the proof is already fully unfocused.
   This function does not care which is the kind of the current focus. *)
let _unfocus pr =
  let (_,fc) = pop_focus pr in
  pr.state <- { pr.state with subproof = Subproof.unfocus fc pr.state.subproof }





(*** The following functions define the safety mechanism of the
     proof system, they may be unsafe if not used carefully. There is
     currently no reason to export them in the .mli ***)

(* This functions saves the current state into a [proof_state]. *)
let save_state { state = ps } = ps

(* This function stores the current proof state in the undo stack. *)
let save pr =
  push_undo (save_state pr) pr

(* This function interpetes (and execute) a single [undo_action] *)
let restore_state save pr = pr.state <- save

(* Interpretes the Undo command. *)
let undo pr = 
  (* on a single line since the effects commute *)
  restore_state (pop_undo pr) pr

(* This function unfocuses a proof until it is fully unfocused
   or there is at least one focused subgoal. *)
let rec unfocus_until_sound pr =
  if Subproof.finished pr.state.subproof then
    try 
      _unfocus pr; unfocus_until_sound pr
    with
      | FullyUnfocused -> ()
  else
    ()

(* Generic function which allows to generate any sort of
   focusing command.
   Note that focus kinds being often meaningful, 
   there is no [unfocus_gen]. *)
let focus_gen kind i j pr =
  save pr;
  _focus ~kind:kind i j pr

(* Focus command (focuses on the [i]th subgoal) *)
(* there could also, easily be a focus-on-a-range tactic, is there 
   a need for it? *)
let focus i pr = 
  focus_gen FocusCommand i i pr

(* Unfocus command.
   Fails if the proof is not focused. *)
(* arnaud: à expliquer proprement que ça ne défocus que des focus
   de type FocusCommand. *)
let unfocus pr =
  let starting_point = save_state pr in
  try
    if kind_of_focus pr = FocusCommand then
      (_unfocus pr;
       push_undo starting_point pr)
    else
      Util.error "This proof is focused, but cannot be unfocused this way"
  with FullyUnfocused -> 
    Util.error "This proof is not focused"



(*** ***)
(* arnaud: cette section, si courte qu'elle est, mérite probablement un titre *)

let run_tactic env tac pr =
  let starting_point = save_state pr in
  let sp = pr.state.subproof in
  try
    let tacticced_subproof = Subproof.apply env tac sp in
    pr.state <- { pr.state with subproof = tacticced_subproof };
    unfocus_until_sound pr;
    push_undo starting_point pr
  with e -> (* arnaud: traitement particulier de TacticFailure ? *)
    restore_state starting_point pr;
    raise e

(*** **)
(* arnaud: hack pour debugging *)
let current_proof = ref None

let start_proof _i gk _ c _decl = 
  let new_subproof = Subproof.start (Global.env ()) [c] in
  let new_proof = 
    { state = {subproof = new_subproof; focus_stack = []}; undo_stack = []; return = fun _ -> () } 
  in
  current_proof := Some new_proof

let pr_subgoals pr_fun =
  match !current_proof with
  | None -> Pp.str ""
  | Some { state = { subproof = sp } } -> Subproof.pr_subgoals sp pr_fun


let db_run_tactic_on env n tac =
  match ! current_proof with
  | None -> ()
  | Some cur -> run_tactic env (Subproof.choose_one n tac) cur

let hide_interp f t ot =
  match !current_proof with
    | None -> Util.anomaly "Proof.hide_interp: seulement quand on prouve quelque chose"
    | Some cur -> f cur t ot

let subproof_of { state = { subproof = sp } } = sp
