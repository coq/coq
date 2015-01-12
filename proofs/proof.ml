(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Module defining the last essential tiles of interactive proofs.
   A proof deals with the focusing commands (including the braces and bullets),
   the shelf (see the [shelve] tactic) and given up goal (see the [give_up]
   tactic). A proof is made of the following:
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
   - Shelf: A list of goals which have been put aside during the proof. They can be
     retrieved with the [Unshelve] command, or solved by side effects
   - Given up goals: as long as there is a given up goal, the proof is not completed.
     Given up goals cannot be retrieved, the user must go back where the tactic
     [give_up] was run and solve the goal there.
*)

open Util

type _focus_kind = int
type 'a focus_kind = _focus_kind
type focus_info = Obj.t
type reason = NotThisWay | AlreadyNoFocus
type unfocusable =
  | Cannot of reason
  | Loose
  | Strict
type _focus_condition =
  | CondNo       of bool * _focus_kind
  | CondDone     of bool * _focus_kind
  | CondEndStack of        _focus_kind (* loose_end is false here *)
type 'a focus_condition = _focus_condition

let next_kind = ref 0
let new_focus_kind () =
  let r = !next_kind in
  incr next_kind;
  r

(* To be authorized to unfocus one must meet the condition prescribed by
    the action which focused.*)
(* spiwack: we could consider having a list of authorized focus_kind instead
    of just one, if anyone needs it *)

exception CannotUnfocusThisWay

(* Cannot focus on non-existing subgoals *)
exception NoSuchGoals of int * int


exception FullyUnfocused

let _ = Errors.register_handler begin function
  | CannotUnfocusThisWay ->
    Errors.error "This proof is focused, but cannot be unfocused this way"
  | NoSuchGoals (i,j) when Int.equal i j ->
      Errors.errorlabstrm "Focus" Pp.(str"No such goal (" ++ int i ++ str").")
  | NoSuchGoals (i,j) ->
      Errors.errorlabstrm "Focus" Pp.(
        str"Not every goal in range ["++ int i ++ str","++int j++str"] exist."
      )
  | FullyUnfocused -> Errors.error "The proof is not focused"
  | _ -> raise Errors.Unhandled
end

let check_cond_kind c k =
  let kind_of_cond = function
    | CondNo (_,k) | CondDone(_,k) | CondEndStack k -> k in
  Int.equal (kind_of_cond c) k

let test_cond c k1 pw =
  match c with
  | CondNo(_,     k) when Int.equal k k1 -> Strict
  | CondNo(true,  _)             -> Loose
  | CondNo(false, _)             -> Cannot NotThisWay
  | CondDone(_,     k) when Int.equal k k1 && Proofview.finished pw -> Strict
  | CondDone(true,  _)                                      -> Loose
  | CondDone(false, _)                                      -> Cannot NotThisWay
  | CondEndStack k when Int.equal k k1 -> Strict
  | CondEndStack _             -> Cannot AlreadyNoFocus

let no_cond ?(loose_end=false) k = CondNo (loose_end, k)
let done_cond ?(loose_end=false) k = CondDone (loose_end,k)

(* Subpart of the type of proofs. It contains the parts of the proof which
   are under control of the undo mechanism *)
type proof = {
  (* Current focused proofview *)
  proofview: Proofview.proofview;
  (* Entry for the proofview *)
  entry : Proofview.entry;
  (* History of the focusings, provides information on how
     to unfocus the proof and the extra information stored while focusing.
     The list is empty when the proof is fully unfocused. *)
  focus_stack: (_focus_condition*focus_info*Proofview.focus_context) list;
  (* List of goals that have been shelved. *)
  shelf : Goal.goal list;
  (* List of goals that have been given up *)
  given_up : Goal.goal list;
}

(*** General proof functions ***)

let proof p =
  let (goals,sigma) = Proofview.proofview p.proofview in
  (* spiwack: beware, the bottom of the stack is used by [Proof]
     internally, and should not be exposed. *)
  let rec map_minus_one f = function
    | [] -> assert false
    | [_] -> []
    | a::l -> f a :: (map_minus_one f l)
  in
  let stack =
    map_minus_one (fun (_,_,c) -> Proofview.focus_context c) p.focus_stack
  in
  let shelf = p.shelf in
  let given_up = p.given_up in
  (goals,stack,shelf,given_up,sigma)

type 'a pre_goals = {
    fg_goals : 'a list;
  (** List of the focussed goals *)
  bg_goals : ('a list * 'a list) list;
  (** Zipper representing the unfocussed background goals *)
  shelved_goals : 'a list;
  (** List of the goals on the shelf. *)
  given_up_goals : 'a list;
  (** List of the goals that have been given up *)
}

let map_structured_proof pfts process_goal: 'a pre_goals =
  let (goals, zipper, shelf, given_up, sigma) = proof pfts in
  let fg = List.map (process_goal sigma) goals in
  let map_zip (lg, rg) =
    let lg = List.map (process_goal sigma) lg in
    let rg = List.map (process_goal sigma) rg in
    (lg, rg)
  in
  let bg = List.map map_zip zipper in
  let shelf = List.map (process_goal sigma) shelf in
  let given_up = List.map (process_goal sigma) given_up in
    { fg_goals = fg;
      bg_goals = bg;
      shelved_goals = shelf;
      given_up_goals = given_up; }

let rec unroll_focus pv = function
  | (_,_,ctx)::stk -> unroll_focus (Proofview.unfocus ctx pv) stk
  | [] -> pv
(* spiwack: a proof is considered completed even if its still focused, if the focus
   doesn't hide any goal.
   Unfocusing is handled in {!return}. *)
let is_done p =
  Proofview.finished p.proofview &&
  Proofview.finished (unroll_focus p.proofview p.focus_stack)

(* spiwack: for compatibility with <= 8.2 proof engine *)
let has_unresolved_evar p =
  Proofview.V82.has_unresolved_evar p.proofview

(* Returns the list of partial proofs to initial goals *)
let partial_proof p = Proofview.partial_proof p.entry p.proofview

(*** The following functions implement the basic internal mechanisms
     of proofs, they are not meant to be exported in the .mli ***)

(* An auxiliary function to push a {!focus_context} on the focus stack. *)
let push_focus cond inf context pr =
  { pr with focus_stack = (cond,inf,context)::pr.focus_stack }

(* An auxiliary function to read the kind of the next focusing step *)
let cond_of_focus pr =
  match pr.focus_stack with
  | (cond,_,_)::_ -> cond
  | _ -> raise FullyUnfocused

(* An auxiliary function to pop and read the last {!Proofview.focus_context} 
   on the focus stack. *)
let pop_focus pr =
  match pr.focus_stack with
  | focus::other_focuses ->
      { pr with focus_stack = other_focuses }, focus
  | _ ->
      raise FullyUnfocused

(* This function focuses the proof [pr] between indices [i] and [j] *)
let _focus cond inf i j pr =
  let focused, context = Proofview.focus i j pr.proofview in
  let pr = push_focus cond inf context pr in
  { pr with proofview = focused }

(* This function unfocuses the proof [pr], it raises [FullyUnfocused],
   if the proof is already fully unfocused.
   This function does not care about the condition of the current focus. *)
let _unfocus pr =
  let pr, (_,_,fc) = pop_focus pr in
   { pr with proofview = Proofview.unfocus fc pr.proofview }

(* Focus command (focuses on the [i]th subgoal) *)
(* spiwack: there could also, easily be a focus-on-a-range tactic, is there 
   a need for it? *)
let focus cond inf i pr =
  try _focus cond (Obj.repr inf) i i pr
  with CList.IndexOutOfRange -> raise (NoSuchGoals (i,i))

let rec unfocus kind pr () =
  let cond = cond_of_focus pr in
  match test_cond cond kind pr.proofview with
  | Cannot NotThisWay -> raise CannotUnfocusThisWay
  | Cannot AlreadyNoFocus -> raise FullyUnfocused
  | Strict ->
     let pr = _unfocus pr in
     pr
  | Loose ->
    begin try
            let pr = _unfocus pr in
	    unfocus kind pr ()
      with FullyUnfocused -> raise CannotUnfocusThisWay
    end

exception NoSuchFocus
(* no handler: should not be allowed to reach toplevel. *)
let rec get_in_focus_stack kind stack =
  match stack with
  | (cond,inf,_)::stack ->
      if check_cond_kind cond kind then inf
      else get_in_focus_stack kind stack
  | [] -> raise NoSuchFocus
let get_at_focus kind pr =
  Obj.magic (get_in_focus_stack kind pr.focus_stack)

let is_last_focus kind pr =
  let (cond,_,_) = List.hd pr.focus_stack in
  check_cond_kind cond kind

let no_focused_goal p =
  Proofview.finished p.proofview

let rec maximal_unfocus k p =
  if no_focused_goal p then
    try maximal_unfocus k (unfocus k p ())
    with FullyUnfocused | CannotUnfocusThisWay -> p
  else p

(*** Proof Creation/Termination ***)

(* [end_of_stack] is unfocused by return to close every loose focus. *)
let end_of_stack_kind = new_focus_kind ()
let end_of_stack = CondEndStack end_of_stack_kind

let unfocused = is_last_focus end_of_stack_kind

let start sigma goals =
  let entry, proofview = Proofview.init sigma goals in
  let pr = {
    proofview;
    entry;
    focus_stack = [] ;
    shelf = [] ;
    given_up = [] } in
  _focus end_of_stack (Obj.repr ()) 1 (List.length goals) pr
let dependent_start goals =
  let entry, proofview = Proofview.dependent_init goals in
  let pr = {
    proofview;
    entry;
    focus_stack = [] ;
    shelf = [] ;
    given_up = [] } in
  let number_of_goals = List.length (Proofview.initial_goals pr.entry) in
  _focus end_of_stack (Obj.repr ()) 1 number_of_goals pr

exception UnfinishedProof
exception HasShelvedGoals
exception HasGivenUpGoals
exception HasUnresolvedEvar
let _ = Errors.register_handler begin function
  | UnfinishedProof -> Errors.error "Some goals have not been solved."
  | HasShelvedGoals -> Errors.error "Some goals have been left on the shelf."
  | HasGivenUpGoals -> Errors.error "Some goals have been given up."
  | HasUnresolvedEvar -> Errors.error "Some existential variables are uninstantiated."
  | _ -> raise Errors.Unhandled
end

let return p =
  if not (is_done p) then
    raise UnfinishedProof
  else if not (CList.is_empty (p.shelf)) then
    raise HasShelvedGoals
  else if not (CList.is_empty (p.given_up)) then
    raise HasGivenUpGoals
  else if has_unresolved_evar p then
    (* spiwack: for compatibility with <= 8.3 proof engine *)
    raise HasUnresolvedEvar
  else
    let p = unfocus end_of_stack_kind p () in
    Proofview.return p.proofview

let initial_goals p = Proofview.initial_goals p.entry

let compact p =
  let entry, proofview = Proofview.compact p.entry p.proofview in
  { p with proofview; entry }

(*** Function manipulation proof extra informations ***)

(*** Tactics ***)

let run_tactic env tac pr =
  let sp = pr.proofview in
  let (_,tacticced_proofview,(status,to_shelve,give_up),info_trace) =
    Proofview.apply env tac sp
  in
  let sigma = Proofview.return tacticced_proofview in
  (* Already solved goals are not to be counted as shelved. Nor are
     they to be marked as unresolvable. *)
  let undef l = List.filter (fun g -> Evd.is_undefined sigma g) l in
  let retrieved = undef (List.rev (Evd.future_goals sigma)) in
  let shelf = (undef pr.shelf)@retrieved@(undef to_shelve) in
  let proofview =
    List.fold_left
      Proofview.Unsafe.mark_as_goal
      tacticced_proofview
      retrieved
  in
  let given_up = pr.given_up@give_up in
  let proofview = Proofview.Unsafe.reset_future_goals proofview in
  { pr with proofview ; shelf ; given_up },(status,info_trace)

(*** Commands ***)

let in_proof p k = k (Proofview.return p.proofview)

(* Remove all the goals from the shelf and adds them at the end of the
   focused goals. *)
let unshelve p =
  { p with proofview = Proofview.unshelve (p.shelf) (p.proofview) ; shelf = [] }

(*** Compatibility layer with <=v8.2 ***)
module V82 = struct
  let subgoals p =
    Proofview.V82.goals p.proofview

  let background_subgoals p =
    Proofview.V82.goals (unroll_focus p.proofview p.focus_stack)

  let top_goal p =
    let { Evd.it=gls ; sigma=sigma; } =
	Proofview.V82.top_goals p.entry p.proofview
    in
    { Evd.it=List.hd gls ; sigma=sigma; }

  let top_evars p =
    Proofview.V82.top_evars p.entry

  let grab_evars p =
    if not (is_done p) then
      raise UnfinishedProof
    else
      { p with proofview = Proofview.V82.grab p.proofview }


  let instantiate_evar n com pr =
    let sp = pr.proofview in
    let proofview = Proofview.V82.instantiate_evar n com sp in
    let shelf =
      List.filter begin fun g ->
        Evd.is_undefined (Proofview.return proofview) g
      end pr.shelf
    in
    { pr with proofview ; shelf }

end
