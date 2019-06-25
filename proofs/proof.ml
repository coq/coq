(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
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

exception NoSuchGoal of Names.Id.t

exception FullyUnfocused

let _ = CErrors.register_handler begin function
  | CannotUnfocusThisWay ->
    CErrors.user_err Pp.(str "This proof is focused, but cannot be unfocused this way")
  | NoSuchGoals (i,j) when Int.equal i j ->
      CErrors.user_err ~hdr:"Focus" Pp.(str"No such goal (" ++ int i ++ str").")
  | NoSuchGoals (i,j) ->
      CErrors.user_err ~hdr:"Focus" Pp.(
        str"Not every goal in range ["++ int i ++ str","++int j++str"] exist."
      )
  | NoSuchGoal id ->
      CErrors.user_err
        ~hdr:"Focus"
        Pp.(str "No such goal: " ++ str (Names.Id.to_string id) ++ str ".")
  | FullyUnfocused -> CErrors.user_err Pp.(str "The proof is not focused")
  | _ -> raise CErrors.Unhandled
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
type t =
  { proofview: Proofview.proofview
  (** Current focused proofview *)
  ; entry : Proofview.entry
  (** Entry for the proofview *)
  ; focus_stack: (_focus_condition*focus_info*Proofview.focus_context) list
  (** History of the focusings, provides information on how to unfocus
     the proof and the extra information stored while focusing.  The
     list is empty when the proof is fully unfocused. *)
  ; shelf : Goal.goal list
  (** List of goals that have been shelved. *)
  ; given_up : Goal.goal list
  (** List of goals that have been given up *)
  ; name : Names.Id.t
  (** the name of the theorem whose proof is being constructed *)
  ; poly : bool
  (** Locality, polymorphism, and "kind" [Coercion, Definition, etc...] *)
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
let has_shelved_goals p = not (CList.is_empty (p.shelf))
let has_given_up_goals p = not (CList.is_empty (p.given_up))

let is_complete p =
  is_done p && not (has_unresolved_evar p) &&
  not (has_shelved_goals p) && not (has_given_up_goals p)

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

(* Focus on the goal named id *)
let focus_id cond inf id pr =
  let (focused_goals, evar_map) = Proofview.proofview pr.proofview in
  begin match try Some (Evd.evar_key id evar_map) with Not_found -> None with
  | Some ev ->
     begin match CList.safe_index Evar.equal ev focused_goals with
     | Some i ->
        (* goal is already under focus *)
        _focus cond (Obj.repr inf) i i pr
     | None ->
        if CList.mem_f Evar.equal ev pr.shelf then
          (* goal is on the shelf, put it in focus *)
          let proofview = Proofview.unshelve [ev] pr.proofview in
          let shelf =
            CList.filter (fun ev' -> Evar.equal ev ev' |> not) pr.shelf
          in
          let pr = { pr with proofview; shelf } in
          let (focused_goals, _) = Proofview.proofview pr.proofview in
          let i =
            (* Now we know that this will succeed *)
            try CList.index Evar.equal ev focused_goals
            with Not_found -> assert false
          in
          _focus cond (Obj.repr inf) i i pr
        else
          raise CannotUnfocusThisWay
     end
  | None ->
     raise (NoSuchGoal id)
  end

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

let start ~name ~poly sigma goals =
  let entry, proofview = Proofview.init sigma goals in
  let pr =
    { proofview
    ; entry
    ; focus_stack = []
    ; shelf = []
    ; given_up = []
    ; name
    ; poly
  } in
  _focus end_of_stack (Obj.repr ()) 1 (List.length goals) pr

let dependent_start ~name ~poly goals =
  let entry, proofview = Proofview.dependent_init goals in
  let pr =
    { proofview
    ; entry
    ; focus_stack = []
    ; shelf = []
    ; given_up = []
    ; name
    ; poly
  } in
  let number_of_goals = List.length (Proofview.initial_goals pr.entry) in
  _focus end_of_stack (Obj.repr ()) 1 number_of_goals pr

type open_error_reason =
  | UnfinishedProof
  | HasGivenUpGoals

let print_open_error_reason er = let open Pp in match er with
  | UnfinishedProof ->
    str "Attempt to save an incomplete proof"
  | HasGivenUpGoals ->
    strbrk "Attempt to save a proof with given up goals. If this is really what you want to do, use Admitted in place of Qed."

exception OpenProof of Names.Id.t option * open_error_reason

let _ = CErrors.register_handler begin function
    | OpenProof (pid, reason) ->
      let open Pp in
      Option.cata (fun pid ->
          str " (in proof " ++ Names.Id.print pid ++ str "): ") (mt()) pid ++ print_open_error_reason reason
    | _ -> raise CErrors.Unhandled
  end

let warn_remaining_shelved_goals =
  CWarnings.create ~name:"remaining-shelved-goals" ~category:"tactics"
    (fun () -> Pp.str"The proof has remaining shelved goals")

let warn_remaining_unresolved_evars =
  CWarnings.create ~name:"remaining-unresolved-evars" ~category:"tactics"
    (fun () -> Pp.str"The proof has unresolved variables")

let return ?pid (p : t) =
  if not (is_done p) then
    raise (OpenProof(pid, UnfinishedProof))
  else if has_given_up_goals p then
    raise (OpenProof(pid, HasGivenUpGoals))
  else begin
    if has_shelved_goals p then warn_remaining_shelved_goals ()
    else if has_unresolved_evar p then warn_remaining_unresolved_evars ();
    let p = unfocus end_of_stack_kind p () in
    Proofview.return p.proofview
  end

let compact p =
  let entry, proofview = Proofview.compact p.entry p.proofview in
  { p with proofview; entry }

(*** Function manipulation proof extra informations ***)

(*** Tactics ***)

let run_tactic env tac pr =
  let open Proofview.Notations in
  let sp = pr.proofview in
  let undef sigma l = List.filter (fun g -> Evd.is_undefined sigma g) l in
  let tac =
    tac >>= fun result ->
    Proofview.tclEVARMAP >>= fun sigma ->
    (* Already solved goals are not to be counted as shelved. Nor are
      they to be marked as unresolvable. *)
    let retrieved = Evd.filter_future_goals (Evd.is_undefined sigma) (Evd.save_future_goals sigma) in
    let retrieved,retrieved_given_up = Evd.extract_given_up_future_goals retrieved in
    (* Check that retrieved given up is empty *)
    if not (List.is_empty retrieved_given_up) then
      CErrors.anomaly Pp.(str "Evars generated outside of proof engine (e.g. V82, clear, ...) are not supposed to be explicitly given up.");
    let sigma = Proofview.Unsafe.mark_as_goals sigma retrieved in
    Proofview.Unsafe.tclEVARS sigma >>= fun () ->
    Proofview.tclUNIT (result,retrieved)
  in
  let { name; poly } = pr in
  let ((result,retrieved),proofview,(status,to_shelve,give_up),info_trace) =
    Proofview.apply ~name ~poly env tac sp
  in
  let sigma = Proofview.return proofview in
  let to_shelve = undef sigma to_shelve in
  let shelf = (undef sigma pr.shelf)@retrieved@to_shelve in
  let proofview =
    List.fold_left
      Proofview.Unsafe.mark_as_unresolvable
      proofview
      to_shelve
  in
  let given_up = pr.given_up@give_up in
  let proofview = Proofview.Unsafe.reset_future_goals proofview in
  { pr with proofview ; shelf ; given_up },(status,info_trace),result

(*** Commands ***)

let in_proof p k = k (Proofview.return p.proofview)

(* Remove all the goals from the shelf and adds them at the end of the
   focused goals. *)
let unshelve p =
  { p with proofview = Proofview.unshelve (p.shelf) (p.proofview) ; shelf = [] }

(*** Compatibility layer with <=v8.2 ***)
module V82 = struct

  let background_subgoals p =
    let it, sigma = Proofview.proofview (unroll_focus p.proofview p.focus_stack) in
    Evd.{ it; sigma }

  let top_goal p =
    let { Evd.it=gls ; sigma=sigma; } =
	Proofview.V82.top_goals p.entry p.proofview
    in
    { Evd.it=List.hd gls ; sigma=sigma; }

  let top_evars p =
    Proofview.V82.top_evars p.entry p.proofview

  let grab_evars p =
    if not (is_done p) then
      raise (OpenProof(None, UnfinishedProof))
    else
      { p with proofview = Proofview.V82.grab p.proofview }

  (* Main component of vernac command Existential *)
  let instantiate_evar env n intern pr =
    let tac =
      Proofview.tclBIND Proofview.tclEVARMAP begin fun sigma ->
      let (evk, evi) =
        let evl = Evarutil.non_instantiated sigma in
        let evl = Evar.Map.bindings evl in
        if (n <= 0) then
          CErrors.user_err Pp.(str "incorrect existential variable index")
        else if CList.length evl < n then
          CErrors.user_err Pp.(str "not so many uninstantiated existential variables")
        else
          CList.nth evl (n-1)
      in
      let env = Evd.evar_filtered_env evi in
      let rawc = intern env sigma in
      let ltac_vars = Glob_ops.empty_lvar in
      let sigma = Evar_refiner.w_refine (evk, evi) (ltac_vars, rawc) sigma in
      Proofview.Unsafe.tclEVARS sigma
    end in
    let { name; poly } = pr in
    let ((), proofview, _, _) = Proofview.apply ~name ~poly env tac pr.proofview in
    let shelf =
      List.filter begin fun g ->
        Evd.is_undefined (Proofview.return proofview) g
      end pr.shelf
    in
    { pr with proofview ; shelf }

end

let all_goals p =
  let add gs set =
    List.fold_left (fun s g -> Goal.Set.add g s) set gs in
  let (goals,stack,shelf,given_up,_) = proof p in
    let set = add goals Goal.Set.empty in
    let set = List.fold_left (fun s gs -> let (g1, g2) = gs in add g1 (add g2 set)) set stack in
    let set = add shelf set in
    let set = add given_up set in
    let { Evd.it = bgoals ; sigma = bsigma } = V82.background_subgoals p in
    add bgoals set

type data =
  { sigma : Evd.evar_map
  (** A representation of the evar_map [EJGA wouldn't it better to just return the proofview?] *)
  ; goals : Evar.t list
  (** Focused goals *)
  ; entry : Proofview.entry
  (** Entry for the proofview *)
  ; stack : (Evar.t list * Evar.t list) list
  (** A representation of the focus stack *)
  ; shelf : Evar.t list
  (** A representation of the shelf  *)
  ; given_up : Evar.t list
  (** A representation of the given up goals  *)
  ; name : Names.Id.t
  (** The name of the theorem whose proof is being constructed *)
  ; poly : bool
  (** Locality, polymorphism, and "kind" [Coercion, Definition, etc...] *)
  }

let data { proofview; focus_stack; entry; shelf; given_up; name; poly } =
  let goals, sigma = Proofview.proofview proofview in
  (* spiwack: beware, the bottom of the stack is used by [Proof]
     internally, and should not be exposed. *)
  let rec map_minus_one f = function
    | [] -> assert false
    | [_] -> []
    | a::l -> f a :: (map_minus_one f l)
  in
  let stack =
    map_minus_one (fun (_,_,c) -> Proofview.focus_context c) focus_stack in
  { sigma; goals; entry; stack; shelf; given_up; name; poly }

let pr_proof p =
  let { goals=fg_goals; stack=bg_goals; shelf; given_up; _ } = data p in
  Pp.(
    let pr_goal_list = prlist_with_sep spc Goal.pr_goal in
    let rec aux acc = function
      | [] -> acc
      | (before,after)::stack ->
         aux (pr_goal_list before ++ spc () ++ str "{" ++ acc ++ str "}" ++ spc () ++
              pr_goal_list after) stack in
    str "[" ++ str "focus structure: " ++
               aux (pr_goal_list fg_goals) bg_goals ++ str ";" ++ spc () ++
    str "shelved: " ++ pr_goal_list shelf ++ str ";" ++ spc () ++
    str "given up: " ++ pr_goal_list given_up ++
    str "]"
  )
