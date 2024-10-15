(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
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
   - Given up goals: as long as there is a given up goal, the proof is not completed.
     Given up goals cannot be retrieved, the user must go back where the tactic
     [give_up] was run and solve the goal there.
*)

open Util

module FocusKind = Dyn.Make()

type 'a focus_kind = 'a FocusKind.tag
type reason = NotThisWay | AlreadyNoFocus
type unfocusable =
  | Cannot of reason
  | Loose
  | Strict
type 'a focus_condition =
  | CondNo       of bool * 'a focus_kind
  | CondDone     of bool * 'a focus_kind
  | CondEndStack of        'a focus_kind (* loose_end is false here *)

let new_focus_kind = FocusKind.create

(* To be authorized to unfocus one must meet the condition prescribed by
    the action which focused.*)
(* spiwack: we could consider having a list of authorized focus_kind instead
    of just one, if anyone needs it *)

exception CannotUnfocusThisWay

(* Cannot focus on non-existing subgoals *)
exception NoSuchGoals of int * int

exception NoSuchGoal of Names.Id.t option

exception FullyUnfocused

let _ = CErrors.register_handler begin function
  | CannotUnfocusThisWay ->
    Some (Pp.str "This proof is focused, but cannot be unfocused this way")
  | NoSuchGoals (i,j) when Int.equal i j ->
    Some Pp.(str "[Focus] No such goal (" ++ int i ++ str").")
  | NoSuchGoals (i,j) ->
    Some Pp.(str "[Focus] Not every goal in range ["++ int i ++ str","++int j++str"] exist.")
  | NoSuchGoal (Some id) ->
    Some Pp.(str "[Focus] No such goal: " ++ str (Names.Id.to_string id) ++ str ".")
  | NoSuchGoal None ->
    Some Pp.(str "[Focus] No such goal.")
  | FullyUnfocused ->
    Some (Pp.str "The proof is not focused")
  | _ -> None
end

let check_cond_kind c k =
  let kind_of_cond = function
    | CondNo (_,k) | CondDone(_,k) | CondEndStack k -> k in
  FocusKind.eq (kind_of_cond c) k

let equal_kind c k = match FocusKind.eq c k with
| None -> false
| Some _ -> true

let test_cond c k1 pw =
  match c with
  | CondNo(_,     k) when equal_kind k k1 -> Strict
  | CondNo(true,  _)             -> Loose
  | CondNo(false, _)             -> Cannot NotThisWay
  | CondDone(_,     k) when equal_kind k k1 && Proofview.finished pw -> Strict
  | CondDone(true,  _)                                      -> Loose
  | CondDone(false, _)                                      -> Cannot NotThisWay
  | CondEndStack k when equal_kind k k1 -> Strict
  | CondEndStack _             -> Cannot AlreadyNoFocus

let no_cond ?(loose_end=false) k = CondNo (loose_end, k)
let done_cond ?(loose_end=false) k = CondDone (loose_end,k)

type focus_element = FocusElt : 'a focus_condition * 'a * Proofview.focus_context -> focus_element

(* Subpart of the type of proofs. It contains the parts of the proof which
   are under control of the undo mechanism *)
type t =
  { proofview: Proofview.proofview
  (** Current focused proofview *)
  ; entry : Proofview.entry
  (** Entry for the proofview *)
  ; focus_stack: focus_element list
  (** History of the focusings, provides information on how to unfocus
     the proof and the extra information stored while focusing.  The
     list is empty when the proof is fully unfocused. *)
  ; name : Names.Id.t
  (** the name of the theorem whose proof is being constructed *)
  ; poly : bool
  (** polymorphism *)
  ; typing_flags : Declarations.typing_flags option
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
  let map (FocusElt (_, _, c)) = Proofview.focus_context c in
  let stack = map_minus_one map p.focus_stack in
  (goals,stack,sigma)

let rec unroll_focus pv = function
  | FocusElt (_,_,ctx)::stk -> unroll_focus (Proofview.unfocus ctx pv) stk
  | [] -> pv

(* spiwack: a proof is considered completed even if its still focused, if the focus
   doesn't hide any goal.
   Unfocusing is handled in {!return}. *)
let is_done p =
  Proofview.finished p.proofview &&
  Proofview.finished (unroll_focus p.proofview p.focus_stack)

(* Returns the list of partial proofs to initial goals *)
let partial_proof p = Proofview.partial_proof p.entry p.proofview

(*** The following functions implement the basic internal mechanisms
     of proofs, they are not meant to be exported in the .mli ***)

(* An auxiliary function to push a {!focus_context} on the focus stack. *)
let push_focus cond inf context pr =
  { pr with focus_stack = FocusElt(cond,inf,context)::pr.focus_stack }

type any_focus_condition = AnyFocusCond : 'a focus_condition -> any_focus_condition

(* An auxiliary function to read the kind of the next focusing step *)
let cond_of_focus pr =
  match pr.focus_stack with
  | FocusElt (cond,_,_)::_ -> AnyFocusCond cond
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
  let pr, FocusElt (_,_,fc) = pop_focus pr in
   { pr with proofview = Proofview.unfocus fc pr.proofview }

(* Focus command (focuses on the [i]th subgoal) *)
(* spiwack: there could also, easily be a focus-on-a-range tactic, is there
   a need for it? *)
let focus cond inf i pr =
  try _focus cond inf i i pr
  with CList.IndexOutOfRange -> raise (NoSuchGoals (i,i))

(* Focus on the goal named id *)
let focus_id cond inf id pr =
  let (focused_goals, evar_map) = Proofview.proofview pr.proofview in
  begin match try Some (Evd.evar_key id evar_map) with Not_found -> None with
  | Some ev ->
     begin match CList.index_opt Evar.equal ev focused_goals with
     | Some i ->
        (* goal is already under focus *)
        _focus cond inf i i pr
     | None ->
        if CList.mem_f Evar.equal ev (Evd.shelf evar_map) then
          (* goal is on the shelf, put it in focus *)
          let proofview = Proofview.unshelve [ev] pr.proofview in
          let pr = { pr with proofview } in
          let (focused_goals, _) = Proofview.proofview pr.proofview in
          let i =
            (* Now we know that this will succeed *)
            try CList.index Evar.equal ev focused_goals
            with Not_found -> assert false
          in
          _focus cond inf i i pr
        else
          raise CannotUnfocusThisWay
     end
  | None ->
     raise (NoSuchGoal (Some id))
  end

let rec unfocus kind pr () =
  let AnyFocusCond cond = cond_of_focus pr in
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
let rec get_in_focus_stack : type a. a focus_kind -> _ -> a = fun kind stack ->
  match stack with
  | FocusElt (cond,inf,_)::stack ->
    begin match check_cond_kind cond kind with
    | Some Refl -> inf
    | None -> get_in_focus_stack kind stack
    end
  | [] -> raise NoSuchFocus
let get_at_focus kind pr =
  get_in_focus_stack kind pr.focus_stack

let is_last_focus kind pr =
  let FocusElt (cond,_,_) = List.hd pr.focus_stack in
  Option.has_some (check_cond_kind cond kind)

let no_focused_goal p =
  Proofview.finished p.proofview

let rec maximal_unfocus k p =
  if no_focused_goal p then
    try maximal_unfocus k (unfocus k p ())
    with FullyUnfocused | CannotUnfocusThisWay -> p
  else p

(*** Proof Creation/Termination ***)

(* [end_of_stack] is unfocused by return to close every loose focus. *)
let end_of_stack_kind = new_focus_kind "end_of_stack"
let end_of_stack = CondEndStack end_of_stack_kind

let unfocused = is_last_focus end_of_stack_kind

let unfocus_all p = unfocus end_of_stack_kind p ()

let start ~name ~poly ?typing_flags sigma goals =
  let entry, proofview = Proofview.init sigma goals in
  let pr =
    { proofview
    ; entry
    ; focus_stack = []
    ; name
    ; poly
    ; typing_flags
  } in
  _focus end_of_stack () 1 (List.length goals) pr

let dependent_start ~name ~poly ?typing_flags goals =
  let entry, proofview = Proofview.dependent_init goals in
  let pr =
    { proofview
    ; entry
    ; focus_stack = []
    ; name
    ; poly
    ; typing_flags
  } in
  let number_of_goals = List.length (Proofview.initial_goals pr.entry) in
  _focus end_of_stack () 1 number_of_goals pr

let compact p =
  let entry, proofview = Proofview.compact p.entry p.proofview in
  { p with proofview; entry }

let update_sigma_univs ugraph p =
  let proofview = Proofview.Unsafe.update_sigma_univs ugraph p.proofview in
  { p with proofview }

(*** Function manipulation proof extra informations ***)

(*** Tactics ***)

let run_tactic env tac pr =
  let open Proofview.Notations in
  let tac =
    (* include the future goals in the shelf *)
    Proofview.with_shelf tac >>= fun (shelf, v) ->
    Proofview.Unsafe.tclNEWSHELVED shelf <*>
    Proofview.tclUNIT v
  in
  let { name; poly; proofview } = pr in
  let (result,proofview,status,info_trace) =
    Proofview.apply ~name ~poly env tac proofview
  in
  let sigma = Proofview.return proofview in
  (* cleanup any shelved goals that got defined
     (this is only useful for goals that were already in the shelf,
     tclNEWSHELVED filters out defined goals instead of adding them)
     XXX should we be doing something advance-aware like tclNEWSHELVED? *)
  let proofview = Proofview.filter_shelf (Evd.is_undefined sigma) proofview in
  { pr with proofview },(status,info_trace),result

(*** Commands ***)

(* Remove all the goals from the shelf and adds them at the end of the
   focused goals. *)
let unshelve p =
  let sigma = Proofview.return p.proofview in
  let shelf = Evd.shelf sigma in
  let proofview = Proofview.unshelve shelf p.proofview in
  { p with proofview }

let background_subgoals p =
  let it, _ = Proofview.proofview (unroll_focus p.proofview p.focus_stack) in
  it

let all_goals p =
  let add gs set =
    List.fold_left (fun s g -> Evar.Set.add g s) set gs in
  let (goals,stack,sigma) = proof p in
    let set = add goals Evar.Set.empty in
    let set = List.fold_left (fun s gs -> let (g1, g2) = gs in add g1 (add g2 set)) set stack in
    let set = add (Evd.shelf sigma) set in
    let set = Evar.Set.union (Evd.given_up sigma) set in
    let bgoals = background_subgoals p in
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
  ; name : Names.Id.t
  (** The name of the theorem whose proof is being constructed *)
  ; poly : bool
  (** Locality, polymorphism, and "kind" [Coercion, Definition, etc...] *)
  }

let data { proofview; focus_stack; entry; name; poly } =
  let goals, sigma = Proofview.proofview proofview in
  (* spiwack: beware, the bottom of the stack is used by [Proof]
     internally, and should not be exposed. *)
  let rec map_minus_one f = function
    | [] -> assert false
    | [_] -> []
    | a::l -> f a :: (map_minus_one f l)
  in
  let map (FocusElt (_, _, c)) = Proofview.focus_context c in
  let stack = map_minus_one map focus_stack in
  { sigma; goals; entry; stack; name; poly }

let pr_goal e = Pp.(str "GOAL:" ++ int (Evar.repr e))

let goal_uid e = string_of_int (Evar.repr e)

let pr_proof p =
  let { goals=fg_goals; stack=bg_goals; sigma } = data p in
  Pp.(
    let pr_goal_list = prlist_with_sep spc pr_goal in
    let rec aux acc = function
      | [] -> acc
      | (before,after)::stack ->
         aux (pr_goal_list before ++ spc () ++ str "{" ++ acc ++ str "}" ++ spc () ++
              pr_goal_list after) stack in
    str "[" ++ str "focus structure: " ++
               aux (pr_goal_list fg_goals) bg_goals ++ str ";" ++ spc () ++
    str "shelved: " ++ pr_goal_list (Evd.shelf sigma) ++ str ";" ++ spc () ++
    str "given up: " ++ pr_goal_list (Evar.Set.elements @@ Evd.given_up sigma) ++
    str "]"
  )

let { Goptions.get = use_unification_heuristics } =
  Goptions.declare_bool_option_and_ref
    ~key:["Solve";"Unification";"Constraints"]
    ~value:true
    ()

exception SuggestNoSuchGoals of int * t

exception FailedConstraints of exn

let () = CErrors.register_handler (function
    | FailedConstraints e ->
      Some Pp.(CErrors.print e ++ spc() ++
               hov 1
                 (str "(while solving unification constraints," ++ spc() ++
                  str "see flag \"Solve Unification Constraints\")"))
    | _ -> None)

let solve_constraints =
  Proofview.tclOR Refine.solve_constraints
    (fun (e,info) -> Proofview.tclZERO ~info (FailedConstraints e))

let solve ?with_end_tac gi info_lvl tac pr =
    let tac = match with_end_tac with
      | None -> tac
      | Some etac -> Proofview.tclTHEN tac etac in
    let tac = match info_lvl with
      | None -> tac
      | Some _ -> Proofview.Trace.record_info_trace tac
    in
    let nosuchgoal =
      let info = Exninfo.reify () in
      Proofview.tclZERO ~info (SuggestNoSuchGoals (1,pr))
    in
    let tac = Goal_select.tclSELECT ~nosuchgoal gi tac in
    let tac =
      if use_unification_heuristics () then
        Proofview.tclTHEN tac solve_constraints
      else tac
    in
    let env = Global.env () in
    let env = Environ.update_typing_flags ?typing_flags:pr.typing_flags env in
    let (p,(status,info),()) = run_tactic env tac pr in
    let env = Global.env () in
    let sigma = Evd.from_env env in
    let () =
      match info_lvl with
      | None -> ()
      | Some i -> Feedback.msg_info (Pp.hov 0 (Proofview.Trace.pr_info env sigma ~lvl:i info))
    in
    (p,status)

(**********************************************************************)
(* Shortcut to build a term using tactics *)

let refine_by_tactic ~name ~poly env sigma ty tac =
  (* Save the initial side-effects to restore them afterwards. We set the
     current set of side-effects to be empty so that we can retrieve the
     ones created during the tactic invocation easily. *)
  let eff = Evd.eval_side_effects sigma in
  let sigma = Evd.drop_side_effects sigma in
  (* Save the existing goals *)
  let sigma = Evd.push_future_goals sigma in
  (* Start a proof *)
  let prf = start ~name ~poly sigma [env, ty] in
  let (prf, _, ()) =
    try run_tactic env tac prf
    with Logic_monad.TacticFailure e as src ->
      (* Catch the inner error of the monad tactic *)
      let (_, info) = Exninfo.capture src in
      Exninfo.iraise (e, info)
  in
  (* Plug back the retrieved sigma *)
  let { goals; stack; sigma; entry } = data prf in
  assert (stack = []);
  let ans = match Proofview.initial_goals entry with
  | [_, c, _] -> c
  | _ -> assert false
  in
  let ans = EConstr.to_constr ~abort_on_undefined_evars:false sigma ans in
  (* [neff] contains the freshly generated side-effects *)
  let neff = Evd.eval_side_effects sigma in
  (* Reset the old side-effects *)
  let sigma = Evd.drop_side_effects sigma in
  let sigma = Evd.emit_side_effects eff sigma in
  (* Restore former goals *)
  let _goals, sigma = Evd.pop_future_goals sigma in
  (* Push remaining goals as future_goals which is the only way we
     have to inform the caller that there are goals to collect while
     not being encapsulated in the monad *)
  let sigma = List.fold_right Evd.declare_future_goal goals sigma in
  (* Get rid of the fresh side-effects by internalizing them in the term
     itself. Note that this is unsound, because the tactic may have solved
     other goals that were already present during its invocation, so that
     those goals rely on effects that are not present anymore. Hopefully,
     this hack will work in most cases. *)
  let neff = neff.Evd.seff_private in
  let (ans, _) = Safe_typing.inline_private_constants env ((ans, Univ.ContextSet.empty), neff) in
  EConstr.of_constr ans, sigma

let get_goal_context_gen pf i =
  let { sigma; goals } = data pf in
  let goal = try List.nth goals (i-1) with Failure _ -> raise (NoSuchGoal None) in
  let env = Evd.evar_filtered_env (Global.env ()) (Evd.find_undefined sigma goal) in
  (sigma, env)

let get_proof_context p =
  try get_goal_context_gen p 1
  with
  | NoSuchGoal _ ->
    (* No more focused goals *)
    let { sigma } = data p in
    sigma, Global.env ()
