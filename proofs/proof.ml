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

(* Basically a subtype of proof: it is used to store a state of a proof
   at a given stage, to be able to perform undo.
   The invariant is that it does not contain the undo stack. *)
type save_state = 
    { restore_subproof: subproof;
      restore_focus_stack: Subproof.focus_context list
    }

type 'a proof = { (* Current focused subproof *)
		  mutable subproof : subproof;
		  (* History of the focusings, provides information
		     on how to unfocus the proof.
		     The list is empty when the proof is fully
		     unfocused. *)
                  (* arnaud: à enrichir pour begin subproof/end subproof *)
                  mutable focus_stack : Subproof.focus_context list;
		  (* The undo stack *)
		  mutable undo_stack : save_state list;
                  (* function executed at QED. *)
		  return: constr list -> 'a
		}



(*** The following functions implement the basic internal mechanisms
     of proofs, they are not meant to be exported in the .mli ***)

(* An auxiliary function to push a {!focus_context} on the focus stack. *)
let push_focus context pr =
  pr.focus_stack <- context::pr.focus_stack

(* An auxiliary function to pop and read the last {!Subproof.focus_context} 
   on the focus stack. *)
exception CannotUnfocus
let pop_focus pr =
  match pr.focus_stack with
  | context::other_focus -> pr.focus_stack <- other_focus; context
  | _ -> raise CannotUnfocus

(* Auxiliary function to push a [save_state] unto the undo stack. *)
let push_undo save ({ undo_stack = stack } as pr) =
  pr.undo_stack <- save::stack

(* Auxiliary function to pop and read a [save_state] from the undo stack. *)
let pop_undo pr = 
  match pr.undo_stack with
  | state::stack -> pr.undo_stack <- stack; state
  | _ -> Util.anomaly "Proof.undo_pop: malformed call."


(* This function focuses the proof [pr] between indices [i] and [j] *)
let _focus i j pr =
  let (focused,context) = Subproof.focus i j pr.subproof in
  push_focus context pr;
  pr.subproof <- focused

(* This function unfocuses the proof [pr], it raises [CannotUnfocus],
   if the proof is already fully unfocused. *)
let _unfocus pr =
  (* In a single line, since the effects commute. *)
  pr.subproof <- Subproof.unfocus (pop_focus pr) pr.subproof





(*** The following functions define the safety mechanism of the
     proof system, they may be unsafe if not used carefully. There is
     currently no reason to export them in the .mli ***)

(* This functions saves the current state into a [save_state]. *)
let save_state { subproof = sp ; focus_stack = focus_stack } =
  { restore_subproof = sp;
    restore_focus_stack = focus_stack 
  }

(* This function interpetes (and execute) a single [undo_action] *)
let restore_state save pr =
  pr.subproof <- save.restore_subproof;
  pr.focus_stack <- save.restore_focus_stack



(* This function unfocuses a proof until it is fully unfocused
   or there is at least one focused subgoal. *)
let rec unfocus_until_sound ({subproof = sp} as pr) =
  if Subproof.finished sp then
    try 
      _unfocus pr
    with
      | CannotUnfocus -> ()
  else
    ()


(* Interpretes the Undo command. *)
let undo pr = 
  (* on a single line since the effects commute *)
  restore_state (pop_undo pr) pr(* focus tactic (focuses on the [i]th subgoal) *)
(* there could also, easily be a focus-on-a-range tactic, is there 
   a need for it? *)
(* arnaud: il faut mettre des undo information ! *)
let focus i pr = _focus i i pr

(* unfocus command.
   Fails if the proof is not focused. *)
(* arnaud: il faut mettre des undo information ! *)
let unfocus  =
  fun pr ->
    try
      _unfocus pr
    with
      | CannotUnfocus -> Util.error "This proof is not focused"



(*** ***)
(* arnaud: cette section, si courte qu'elle est, mérite probablement un titre *)

let run_tactic tac env ( { subproof = sp } as pr ) =
  let starting_point = save_state pr in
  try
    let tacticced_subproof = Subproof.apply env tac sp in
    pr.subproof <- tacticced_subproof;
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
  let new_proof = { subproof = new_subproof; undo_stack = []; focus_stack = []; return = fun _ -> () } in
  current_proof := Some new_proof

let pr_subgoals pr_fun =
  match !current_proof with
  | None -> Pp.str ""
  | Some {subproof = sp} -> Subproof.pr_subgoals sp pr_fun


let db_run_tactic_on env n tac =
  match ! current_proof with
  | None -> ()
  | Some cur ->(focus n cur;
               run_tactic env tac cur;
	       unfocus cur)

let hide_interp f t ot =
  match !current_proof with
    | None -> Util.anomaly "Proof.hide_interp: seulement quand on prouve quelque chose"
    | Some cur -> f cur t ot

let subproof_of { subproof = sp } = sp
