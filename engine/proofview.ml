(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)


(** This files defines the basic mechanism of proofs: the [proofview]
    type is the state which tactics manipulate (a global state for
    existential variables, together with the list of goals), and the type
    ['a tactic] is the (abstract) type of tactics modifying the proof
    state and returning a value of type ['a]. *)

open Pp
open Util
open Proofview_monad
open Context.Named.Declaration

(** Main state of tactics *)
type proofview = Proofview_monad.proofview

(* The first items in pairs below are proofs (under construction).
   The second items in the pairs below are statements that are being proved. *)
type entry = (EConstr.constr * EConstr.types) list

(** Returns a stylised view of a proofview for use by, for instance,
    ide-s. *)
(* spiwack: the type of [proofview] will change as we push more
   refined functions to ide-s. This would be better than spawning a
   new nearly identical function every time. Hence the generic name. *)
(* In this version: returns the list of focused goals together with
   the [evar_map] context. *)
let proofview p =
  List.map drop_state p.comb , p.solution

let compact el ({ solution } as pv) =
  let nf c = Evarutil.nf_evar solution c in
  let nf0 c = EConstr.(to_constr ~abort_on_undefined_evars:false solution (of_constr c)) in
  let size = Evd.fold (fun _ _ i -> i+1) solution 0 in
  let new_el = List.map (fun (t,ty) -> nf t, nf ty) el in
  let pruned_solution = Evd.drop_all_defined solution in
  let apply_subst_einfo _ ei =
    Evd.({ ei with
       evar_concl =  nf ei.evar_concl;
       evar_hyps = Environ.map_named_val (fun d -> map_constr nf0 d) ei.evar_hyps;
       evar_candidates = Option.map (List.map nf) ei.evar_candidates }) in
  let new_solution = Evd.raw_map_undefined apply_subst_einfo pruned_solution in
  let new_size = Evd.fold (fun _ _ i -> i+1) new_solution 0 in
  Feedback.msg_info (Pp.str (Printf.sprintf "Evars: %d -> %d\n" size new_size));
  new_el, { pv with solution = new_solution; }


(** {6 Starting and querying a proof view} *)

type telescope =
  | TNil of Evd.evar_map
  | TCons of Environ.env * Evd.evar_map * EConstr.types * (Evd.evar_map -> EConstr.constr -> telescope)

let map_telescope_evd f = function
  | TNil sigma -> TNil (f sigma)
  | TCons (env,sigma,ty,g) -> TCons(env,(f sigma),ty,g)

let dependent_init =
  (* Goals don't have a source location. *)
  let src = Loc.tag @@ Evar_kinds.GoalEvar in
  (* Main routine *)
  let rec aux = function
  | TNil sigma -> [], { solution = sigma; comb = [] }
  | TCons (env, sigma, typ, t) ->
    let (sigma, econstr) = Evarutil.new_evar env sigma ~src ~typeclass_candidate:false typ in
    let (gl, _) = EConstr.destEvar sigma econstr in
    let ret, { solution = sol; comb = comb } = aux (t sigma econstr) in
    let entry = (econstr, typ) :: ret in
    entry, { solution = sol; comb = with_empty_state gl :: comb }
  in
  fun t ->
    let t = map_telescope_evd Evd.push_future_goals t in
    let entry, v = aux t in
    (* The created goal are not to be shelved. *)
    let _goals, solution = Evd.pop_future_goals v.solution in
    entry, { v with solution }

let init =
  let rec aux sigma = function
    | [] -> TNil sigma
    | (env,g)::l -> TCons (env,sigma,g,(fun sigma _ -> aux sigma l))
  in
  fun sigma l -> dependent_init (aux sigma l)

let initial_goals initial = initial

let finished = function
  | {comb = []} -> true
  | _  -> false

let return { solution=defs } = defs

let return_constr { solution = defs } c = Evarutil.nf_evar defs c

let partial_proof entry pv = CList.map (return_constr pv) (CList.map fst entry)


(** {6 Focusing commands} *)

(** A [focus_context] represents the part of the proof view which has
    been removed by a focusing action, it can be used to unfocus later
    on. *)
(* First component is a reverse list of the goals which come before
   and second component is the list of the goals which go after (in
   the expected order). *)
type focus_context = goal_with_state list * goal_with_state list


(** Returns a stylised view of a focus_context for use by, for
    instance, ide-s. *)
(* spiwack: the type of [focus_context] will change as we push more
   refined functions to ide-s. This would be better than spawning a
   new nearly identical function every time. Hence the generic name. *)
(* In this version: the goals in the context, as a "zipper" (the first
   list is in reversed order). *)
let focus_context (left,right) =
  (List.map drop_state left, List.map drop_state right)

(** This (internal) function extracts a sublist between two indices,
    and returns this sublist together with its context: if it returns
    [(a,(b,c))] then [a] is the sublist and [(rev b) @ a @ c] is the
    original list.  The focused list has length [j-i-1] and contains
    the goals from number [i] to number [j] (both included) the first
    goal of the list being numbered [1].  [focus_sublist i j l] raises
    [IndexOutOfRange] if [i > length l], or [j > length l] or [j <
    i]. *)
let focus_sublist i j l =
  let (left,sub_right) = CList.goto (i-1) l in
  let (sub, right) =
    try CList.chop (j-i+1) sub_right
    with Failure _ -> raise CList.IndexOutOfRange
  in
  (sub, (left,right))

(** Inverse operation to the previous one. *)
let unfocus_sublist (left,right) s =
  CList.rev_append left (s@right)


(** [focus i j] focuses a proofview on the goals from index [i] to
    index [j] (inclusive, goals are indexed from [1]). I.e. goals
    number [i] to [j] become the only focused goals of the returned
    proofview.  It returns the focused proofview, and a context for
    the focus stack. *)
let focus i j sp =
  let (new_comb, (left, right)) = focus_sublist i j sp.comb in
  ( { sp with comb = new_comb } , (left, right) )

let cleared_alias evd g =
  let evk = drop_state g in
  let state = get_state g in
  Option.map (fun g -> goal_with_state g state) (Evarutil.advance evd evk)

(** [undefined defs l] is the list of goals in [l] which are still
    unsolved (after advancing cleared goals). Note that order matters. *)
let undefined_evars defs l =
  List.fold_right (fun evk l ->
      match Evarutil.advance defs evk with
      | Some evk -> List.add_set Evar.equal evk l
      | None -> l) l []
let goal_with_state_equal x y = Evar.equal (drop_state x) (drop_state y)
let undefined defs l =
  List.fold_right (fun evk l ->
      match cleared_alias defs evk with
      | Some evk -> List.add_set goal_with_state_equal evk l
      | None -> l) l []

(** Unfocuses a proofview with respect to a context. *)
let unfocus (left, right) sp =
  { sp with comb = undefined sp.solution (unfocus_sublist (left, right) sp.comb) }

let with_empty_state = Proofview_monad.with_empty_state
let drop_state = Proofview_monad.drop_state
let goal_with_state = Proofview_monad.goal_with_state

(** {6 The tactic monad} *)

(** - Tactics are objects which apply a transformation to all the
    subgoals of the current view at the same time. By opposition to
    the old vision of applying it to a single goal. It allows tactics
    such as [shelve_unifiable], tactics to reorder the focused goals,
    or global automation tactic for dependent subgoals (instantiating
    an evar has influences on the other goals of the proof in
    progress, not being able to take that into account causes the
    current eauto tactic to fail on some instances where it could
    succeed).  Another benefit is that it is possible to write tactics
    that can be executed even if there are no focused goals.
    - Tactics form a monad ['a tactic], in a sense a tactic can be
    seen as a function (without argument) which returns a value of
    type 'a and modifies the environment (in our case: the view).
    Tactics of course have arguments, but these are given at the
    meta-level as OCaml functions.  Most tactics in the sense we are
    used to return [()], that is no really interesting values. But
    some might pass information around.  The tactics seen in Coq's
    Ltac are (for now at least) only [unit tactic], the return values
    are kept for the OCaml toolkit.  The operation or the monad are
    [Proofview.tclUNIT] (which is the "return" of the tactic monad)
    [Proofview.tclBIND] (which is the "bind") and [Proofview.tclTHEN]
    (which is a specialized bind on unit-returning tactics).
    - Tactics have support for full-backtracking. Tactics can be seen
    having multiple success: if after returning the first success a
    failure is encountered, the tactic can backtrack and use a second
    success if available. The state is backtracked to its previous
    value, except the non-logical state defined in the {!NonLogical}
    module below.
*)
(* spiwack: as far as I'm aware this doesn't really relate to
   F. Kirchner and C. Muñoz. *)

module Proof = Logical

(** type of tactics:

   tactics can
   - access the environment,
   - report unsafe status, shelved goals and given up goals
   - access and change the current [proofview]
   - backtrack on previous changes of the proofview *)
type +'a tactic = 'a Proof.t

(** Applies a tactic to the current proofview. *)
let apply ~name ~poly env t sp =
  let open Logic_monad in
  let ans = Proof.repr (Proof.run t P.{trace=false; name; poly} (sp,env)) in
  let ans = Logic_monad.NonLogical.run ans in
  match ans with
  | Nil (e, info) -> Exninfo.iraise (TacticFailure e, info)
  | Cons ((r, (state, _), status, info), _) ->
    r, state, status, Trace.to_tree info



(** {7 Monadic primitives} *)

(** Unit of the tactic monad. *)
let tclUNIT = Proof.return

(** Bind operation of the tactic monad. *)
let tclBIND = Proof.(>>=)

(** Interprets the ";" (semicolon) of Ltac. As a monadic operation,
    it's a specialized "bind". *)
let tclTHEN = Proof.(>>)

(** [tclIGNORE t] has the same operational content as [t], but drops
    the returned value. *)
let tclIGNORE = Proof.ignore

module Monad = Proof



(** {7 Failure and backtracking} *)


(** [tclZERO e] fails with exception [e]. It has no success. *)
let tclZERO ?(info=Exninfo.null) e =
  if not (CErrors.noncritical e) then
    CErrors.anomaly (Pp.str "tclZERO receiving critical error: " ++ CErrors.print e);
  Proof.zero (e, info)

(** [tclOR t1 t2] behaves like [t1] as long as [t1] succeeds. Whenever
    the successes of [t1] have been depleted and it failed with [e],
    then it behaves as [t2 e]. In other words, [tclOR] inserts a
    backtracking point. *)
let tclOR = Proof.plus

(** [tclORELSE t1 t2] is equal to [t1] if [t1] has at least one
    success or [t2 e] if [t1] fails with [e]. It is analogous to
    [try/with] handler of exception in that it is not a backtracking
    point. *)
let tclORELSE t1 t2 =
  let open Logic_monad in
  let open Proof in
  split t1 >>= function
    | Nil e -> t2 e
    | Cons (a,t1') -> plus (return a) t1'

(** [tclIFCATCH a s f] is a generalisation of {!tclORELSE}: if [a]
    succeeds at least once then it behaves as [tclBIND a s] otherwise,
    if [a] fails with [e], then it behaves as [f e]. *)
let tclIFCATCH a s f =
  let open Logic_monad in
  let open Proof in
  split a >>= function
    | Nil e -> f e
    | Cons (x,a') -> plus (s x) (fun e -> (a' e) >>= fun x' -> (s x'))

(** [tclONCE t] behave like [t] except it has at most one success:
    [tclONCE t] stops after the first success of [t]. If [t] fails
    with [e], [tclONCE t] also fails with [e]. *)
let tclONCE = Proof.once

exception MoreThanOneSuccess
let _ = CErrors.register_handler begin function
  | MoreThanOneSuccess ->
    Some (Pp.str "This tactic has more than one success.")
  | _ -> None
end

(** [tclEXACTLY_ONCE e t] succeeds as [t] if [t] has exactly one
    success. Otherwise it fails. The tactic [t] is run until its first
    success, then a failure with exception [e] is simulated. It [t]
    yields another success, then [tclEXACTLY_ONCE e t] fails with
    [MoreThanOneSuccess] (it is a user error). Otherwise,
    [tclEXACTLY_ONCE e t] succeeds with the first success of
    [t]. Notice that the choice of [e] is relevant, as the presence of
    further successes may depend on [e] (see {!tclOR}). *)
let tclEXACTLY_ONCE e t =
  let open Logic_monad in
  let open Proof in
  split t >>= function
    | Nil (e, info) -> tclZERO ~info e
    | Cons (x,k) ->
      let info = Exninfo.null in
      Proof.split (k (e, Exninfo.null)) >>= function
      | Nil _ -> tclUNIT x
      | _ -> tclZERO ~info MoreThanOneSuccess


(** [tclCASE t] wraps the {!Proofview_monad.Logical.split} primitive. *)
type 'a case =
| Fail of Exninfo.iexn
| Next of 'a * (Exninfo.iexn -> 'a tactic)
let tclCASE t =
  let open Logic_monad in
  let map = function
  | Nil e -> Fail e
  | Cons (x, t) -> Next (x, t)
  in
  Proof.map map (Proof.split t)

let tclBREAK = Proof.break



(** {7 Focusing tactics} *)

exception NoSuchGoals of int

let _ = CErrors.register_handler begin function
  | NoSuchGoals n ->
    Some (str "No such " ++ str (String.plural n "goal") ++ str ".")
  | _ -> None
end

(** [tclFOCUS ?nosuchgoal i j t] applies [t] in a context where
    only the goals numbered [i] to [j] are focused (the rest of the goals
    is restored at the end of the tactic). If the range [i]-[j] is not
    valid, then it [tclFOCUS_gen nosuchgoal i j t] is [nosuchgoal]. *)
let tclFOCUS ?nosuchgoal i j t =
  let nosuchgoal ~info = Option.default (tclZERO ~info (NoSuchGoals (j+1-i))) nosuchgoal in
  let open Proof in
  Pv.get >>= fun initial ->
  try
    let (focused,context) = focus i j initial in
    Pv.set focused >>
    t >>= fun result ->
    Pv.modify (fun next -> unfocus context next) >>
    return result
  with CList.IndexOutOfRange as exn ->
    let _, info = Exninfo.capture exn in
    nosuchgoal ~info

let tclTRYFOCUS i j t = tclFOCUS ~nosuchgoal:(tclUNIT ()) i j t

let tclFOCUSLIST ?(nosuchgoal=tclZERO (NoSuchGoals 0)) l t =
  let open Proof in
  Comb.get >>= fun comb ->
  let n = CList.length comb in
  let ok (i, j) = 1 <= i && i <= j && j <= n in
  if not (CList.for_all ok l) then nosuchgoal
  else
    match l with
    | [] -> nosuchgoal
    | (mi, _) :: _ ->
      (* Get the left-most goal to focus. This goal won't move, and we
         will then place all the other goals to focus to the right. *)
      let mi = CList.fold_left (fun m (i, _) -> min m i) mi l in
      (* [CList.goto] returns a zipper, so that
         [(rev left) @ sub_right = comb]. *)
      let left, sub_right = CList.goto (mi-1) comb in
      let p x _ = CList.exists (fun (i, j) -> i <= x + mi && x + mi <= j) l in
      let sub, right = CList.partitioni p sub_right in
      let mj = mi - 1 + CList.length sub in
      Comb.set (CList.rev_append left (sub @ right)) >>
      tclFOCUS mi mj t

(** Like {!tclFOCUS} but selects a single goal by name. *)
let tclFOCUSID ?(nosuchgoal=tclZERO (NoSuchGoals 1)) id t =
  let open Proof in
  Pv.get >>= fun initial ->
  try
    let ev = Evd.evar_key id initial.solution in
    try
      let comb = CList.map drop_state initial.comb in
      let n = CList.index Evar.equal ev comb in
      (* goal is already under focus *)
      let (focused,context) = focus n n initial in
      Pv.set focused >>
        t >>= fun result ->
      Pv.modify (fun next -> unfocus context next) >>
        return result
    with Not_found ->
      (* otherwise, save current focus and work purely on the shelve *)
      Comb.set [with_empty_state ev] >>
        t >>= fun result ->
      Comb.set initial.comb  >>
        return result
  with Not_found -> nosuchgoal

(** {7 Dispatching on goals} *)

exception SizeMismatch of int*int
let _ = CErrors.register_handler begin function
  | SizeMismatch (i,j) ->
    let open Pp in
    Some (
      str"Incorrect number of goals" ++ spc() ++
      str"(expected "++int i++str(String.plural i " tactic") ++ str", was given "++ int j++str").")
  | _ -> None
end

(** A variant of [Monad.List.iter] where we iter over the focused list
    of goals. The argument tactic is executed in a focus comprising
    only of the current goal, a goal which has been solved by side
    effect is skipped. The generated subgoals are concatenated in
    order.  *)
let iter_goal i =
  let open Proof in
  Comb.get >>= fun initial ->
  Proof.List.fold_left begin fun (subgoals as cur) goal ->
    Solution.get >>= fun step ->
    match cleared_alias step goal with
    | None -> return cur
    | Some goal ->
        Comb.set [goal] >>
        i goal >>
        Proof.map (fun comb -> comb :: subgoals) Comb.get
  end [] initial >>= fun subgoals ->
  Solution.get >>= fun evd ->
  Comb.set CList.(undefined evd (flatten (rev subgoals)))

(** List iter but allocates a list of results *)
let map_goal i =
  let rev = List.rev in (* hem... Proof masks List... *)
  let open Proof in
  Comb.get >>= fun initial ->
  Proof.List.fold_left begin fun (acc, subgoals as cur) goal ->
    Solution.get >>= fun step ->
    match cleared_alias step goal with
    | None -> return cur
    | Some goal ->
        Comb.set [goal] >>
        i goal >>= fun res ->
        Proof.map (fun comb -> comb :: subgoals) Comb.get >>= fun x ->
        return (res :: acc, x)
  end ([],[]) initial >>= fun (results_rev, subgoals) ->
  Solution.get >>= fun evd ->
  Comb.set CList.(undefined evd (flatten (rev subgoals))) >>
  return (rev results_rev)

(** A variant of [Monad.List.fold_left2] where the first list is the
    list of focused goals. The argument tactic is executed in a focus
    comprising only of the current goal, a goal which has been solved
    by side effect is skipped. The generated subgoals are concatenated
    in order. *)
let fold_left2_goal i s l =
  let open Proof in
  Pv.get >>= fun initial ->
  let err =
    return () >>= fun () -> (* Delay the computation of list lengths. *)
    tclZERO (SizeMismatch (CList.length initial.comb,CList.length l))
  in
  Proof.List.fold_left2 err begin fun ((r,subgoals) as cur) goal a ->
    Solution.get >>= fun step ->
    match cleared_alias step goal with
    | None -> return cur
    | Some goal ->
        Comb.set [goal] >>
        i goal a r >>= fun r ->
        Proof.map (fun comb -> (r, comb :: subgoals)) Comb.get
  end (s,[]) initial.comb l >>= fun (r,subgoals) ->
  Solution.get >>= fun evd ->
  Comb.set CList.(undefined evd (flatten (rev subgoals))) >>
  return r

(** Dispatch tacticals are used to apply a different tactic to each
    goal under focus. They come in two flavours: [tclDISPATCH] takes a
    list of [unit tactic]-s and build a [unit tactic]. [tclDISPATCHL]
    takes a list of ['a tactic] and returns an ['a list tactic].

    They both work by applying each of the tactic in a focus
    restricted to the corresponding goal (starting with the first
    goal). In the case of [tclDISPATCHL], the tactic returns a list of
    the same size as the argument list (of tactics), each element
    being the result of the tactic executed in the corresponding goal.

    When the length of the tactic list is not the number of goal,
    raises [SizeMismatch (g,t)] where [g] is the number of available
    goals, and [t] the number of tactics passed.

    [tclDISPATCHGEN join tacs] generalises both functions as the
    successive results of [tacs] are stored in reverse order in a
    list, and [join] is used to convert the result into the expected
    form. *)
let tclDISPATCHGEN0 join tacs =
  match tacs with
  | [] ->
      begin
        let open Proof in
        Comb.get >>= function
        | [] -> tclUNIT (join [])
        | comb -> tclZERO (SizeMismatch (CList.length comb,0))
      end
  | [tac] ->
      begin
        let open Proof in
        Pv.get >>= function
        | { comb=[goal] ; solution } ->
            begin match cleared_alias solution goal with
            | None -> tclUNIT (join [])
            | Some _ -> Proof.map (fun res -> join [res]) tac
            end
        | {comb} -> tclZERO (SizeMismatch(CList.length comb,1))
      end
  | _ ->
      let iter _ t cur = Proof.map (fun y -> y :: cur) t in
      let ans = fold_left2_goal iter [] tacs in
      Proof.map join ans

let tclDISPATCHGEN join tacs =
  let branch t = InfoL.tag (Info.DBranch) t in
  let tacs = CList.map branch tacs in
  InfoL.tag (Info.Dispatch) (tclDISPATCHGEN0 join tacs)

let tclDISPATCH tacs = tclDISPATCHGEN ignore tacs

let tclDISPATCHL tacs = tclDISPATCHGEN CList.rev tacs


(** [extend_to_list startxs rx endxs l] builds a list
    [startxs @ [rx,...,rx] @ endxs] of the same length as [l]. Raises
    [SizeMismatch] if [startxs @ endxs] is already longer than [l]. *)
let extend_to_list startxs rx endxs l =
  (* spiwack: I use [l] essentially as a natural number *)
  let rec duplicate acc = function
    | [] -> acc
    | _::rest -> duplicate (rx::acc) rest
  in
  let rec tail to_match rest =
    match rest, to_match with
    | [] , _::_ -> raise (SizeMismatch(0,0)) (* placeholder *)
    | _::rest , _::to_match -> tail to_match rest
    | _ , [] -> duplicate endxs rest
  in
  let rec copy pref rest =
    match rest,pref with
    | [] , _::_ -> raise (SizeMismatch(0,0)) (* placeholder *)
    | _::rest, a::pref -> a::(copy pref rest)
    | _ , [] -> tail endxs rest
  in
  copy startxs l

(** [tclEXTEND b r e] is a variant of {!tclDISPATCH}, where the [r]
    tactic is "repeated" enough time such that every goal has a tactic
    assigned to it ([b] is the list of tactics applied to the first
    goals, [e] to the last goals, and [r] is applied to every goal in
    between). *)
let tclEXTEND tacs1 rtac tacs2 =
  let open Proof in
  Comb.get >>= fun comb ->
  try
    let tacs = extend_to_list tacs1 rtac tacs2 comb in
    tclDISPATCH tacs
  with SizeMismatch _ ->
    tclZERO (SizeMismatch(
      CList.length comb,
      (CList.length tacs1)+(CList.length tacs2)))
(* spiwack: failure occurs only when the number of goals is too
   small. Hence we can assume that [rtac] is replicated 0 times for
   any error message. *)

(** [tclEXTEND [] tac []]. *)
let tclINDEPENDENT tac =
  let open Proof in
  Pv.get >>= fun initial ->
  match initial.comb with
  | [] -> tclUNIT ()
  | [_] -> tac
  | _ ->
      let tac = InfoL.tag (Info.DBranch) tac in
      InfoL.tag (Info.Dispatch) (iter_goal (fun _ -> tac))

let tclINDEPENDENTL tac =
  let open Proof in
  Pv.get >>= fun initial ->
  match initial.comb with
  | [] -> tclUNIT []
  | [_] -> tac >>= fun x -> return [x]
  | _ ->
      let tac = InfoL.tag (Info.DBranch) tac in
      InfoL.tag (Info.Dispatch) (map_goal (fun _ -> tac))

(** {7 Goal manipulation} *)

(** Shelves all the goals under focus. *)
let shelve =
  let open Proof in
  Comb.get >>= fun initial ->
  Comb.set [] >>
  InfoL.leaf (Info.Tactic (fun _ _ -> Pp.str"shelve")) >>
  let initial = CList.map drop_state initial in
  Pv.modify (fun pv -> { pv with solution = Evd.shelve pv.solution initial })

let shelve_goals l =
  let open Proof in
  Comb.get >>= fun initial ->
  let comb = CList.filter (fun g -> not (CList.mem (drop_state g) l)) initial in
  Comb.set comb >>
  InfoL.leaf (Info.Tactic (fun _ _ -> Pp.str"shelve_goals")) >>
  Pv.modify (fun pv -> { pv with solution = Evd.shelve pv.solution l })

(** [depends_on sigma src tgt] checks whether the goal [src] appears
    as an existential variable in the definition of the goal [tgt] in
    [sigma]. *)
let depends_on sigma src tgt =
  let evi = Evd.find sigma tgt in
  Evar.Set.mem src (Evd.evars_of_filtered_evar_info sigma (Evarutil.nf_evar_info sigma evi))

let unifiable_delayed g l =
  CList.exists (fun (tgt, lazy evs) -> not (Evar.equal g tgt) && Evar.Set.mem g evs) l

let free_evars sigma l =
  let cache = Evarutil.create_undefined_evars_cache () in
  let map ev =
  (* Computes the set of evars appearing in the hypotheses, the conclusion or
     the body of the evar_info [evi]. Note: since we want to use it on goals,
     the body is actually supposed to be empty. *)
    let evi = Evd.find sigma ev in
    let fevs = lazy (Evarutil.filtered_undefined_evars_of_evar_info ~cache sigma evi) in
    (ev, fevs)
  in
  List.map map l

let free_evars_with_state sigma l =
  let cache = Evarutil.create_undefined_evars_cache () in
  let map ev =
  (* Computes the set of evars appearing in the hypotheses, the conclusion or
     the body of the evar_info [evi]. Note: since we want to use it on goals,
     the body is actually supposed to be empty. *)
    let ev = drop_state ev in
    let evi = Evd.find sigma ev in
    let fevs = lazy (Evarutil.filtered_undefined_evars_of_evar_info ~cache sigma evi) in
    (ev, fevs)
  in
  List.map map l


(** [unifiable sigma g l] checks whether [g] appears in another
    subgoal of [l]. The list [l] may contain [g], but it does not
    affect the result. *)
let unifiable_delayed_with_state sigma g l =
  let g = drop_state g in
  unifiable_delayed g l

let unifiable sigma g l =
  let l = free_evars sigma l in
  unifiable_delayed g l

(** [partition_unifiable sigma l] partitions [l] into a pair [(u,n)]
    where [u] is composed of the unifiable goals, i.e. the goals on
    whose definition other goals of [l] depend, and [n] are the
    non-unifiable goals. *)
let partition_unifiable sigma l =
  let fevs = free_evars_with_state sigma l in
  CList.partition (fun g -> unifiable_delayed_with_state sigma g fevs) l

(** Shelves the unifiable goals under focus, i.e. the goals which
    appear in other goals under focus (the unfocused goals are not
    considered). *)
let shelve_unifiable_informative =
  let open Proof in
  Pv.get >>= fun initial ->
  let (u,n) = partition_unifiable initial.solution initial.comb in
  Comb.set n >>
  InfoL.leaf (Info.Tactic (fun _ _ -> Pp.str"shelve_unifiable")) >>
  let u = CList.map drop_state u in
  Pv.modify (fun pv -> { pv with solution = Evd.shelve pv.solution u }) >>
  tclUNIT u

let shelve_unifiable =
  let open Proof in
  shelve_unifiable_informative >>= fun _ -> tclUNIT ()

(** [guard_no_unifiable] returns the list of unifiable goals if some
    goals are unifiable (see {!shelve_unifiable}) in the current focus. *)
let guard_no_unifiable =
  let open Proof in
  Pv.get >>= fun initial ->
  let (u,n) = partition_unifiable initial.solution initial.comb in
  match u with
  | [] -> tclUNIT None
  | gls ->
      let l = CList.map (fun g -> Evd.dependent_evar_ident (drop_state g) initial.solution) gls in
      let l = CList.map (fun id -> Names.Name id) l in
      tclUNIT (Some l)

(** [unshelve l p] moves all the goals in [l] from the shelf and put them at
    the end of the focused goals of p, if they are still undefined after [advance] *)
let unshelve l p =
  let solution = Evd.unshelve p.solution l in
  let l = List.map with_empty_state l in
  (* advance the goals in case of clear *)
  let l = undefined p.solution l in
  { comb = p.comb@l; solution }

let filter_shelf f pv =
  { pv with solution = Evd.filter_shelf f pv.solution }

let mark_in_evm ~goal evd evars =
  let evd =
    if goal then
      let mark evd content =
        let info = Evd.find evd content in
        let info =
          { info with Evd.evar_source = match info.Evd.evar_source with
                (* Two kinds for goal evars:
                   - GoalEvar (morally not dependent)
                   - VarInstance (morally dependent of some name).
                   This is a heuristic for naming these evars. *)
                | loc, (Evar_kinds.QuestionMark { Evar_kinds.qm_name=Names.Name id} |
                        Evar_kinds.ImplicitArg (_,(_,Some id),_)) -> loc, Evar_kinds.VarInstance id
                | _, (Evar_kinds.VarInstance _ | Evar_kinds.GoalEvar) as x -> x
                | loc,_ -> loc,Evar_kinds.GoalEvar }
        in Evd.add evd content info
      in CList.fold_left mark evd evars
    else evd
  in
  let tcs = Evd.get_typeclass_evars evd in
  let evset = Evar.Set.of_list evars in
  Evd.set_typeclass_evars evd (Evar.Set.diff tcs evset)

let with_shelf tac =
  let open Proof in
  Pv.get >>= fun pv ->
  let { solution } = pv in
  Pv.set { pv with solution = Evd.push_shelf @@ Evd.push_future_goals solution } >>
  tac >>= fun ans ->
  Pv.get >>= fun npv ->
  let { solution = sigma } = npv in
  let gls, sigma = Evd.pop_shelf sigma in
  (* The pending future goals are necessarily coming from V82.tactic *)
  (* and thus considered as to shelve, as in Proof.run_tactic *)
  let fgl, sigma = Evd.pop_future_goals sigma in
  (* Ensure we mark and return only unsolved goals *)
  let gls' = CList.rev_append fgl.Evd.FutureGoals.comb gls in
  let gls' = undefined_evars sigma gls' in
  let sigma = mark_in_evm ~goal:false sigma gls' in
  let npv = { npv with solution = sigma } in
  Pv.set npv >> tclUNIT (gls', ans)

(** [goodmod p m] computes the representative of [p] modulo [m] in the
    interval [[0,m-1]].*)
let goodmod p m =
  if m = 0 then 0 else
    let p' = p mod m in
    (* if [n] is negative [n mod l] is negative of absolute value less
      than [l], so [(n mod l)+l] is the representative of [n] in the
      interval [[0,l-1]].*)
    if p' < 0 then p'+m else p'

let cycle n =
  let open Proof in
  InfoL.leaf (Info.Tactic (fun _ _ -> Pp.(str"cycle "++int n))) >>
  Comb.modify begin fun initial ->
    let l = CList.length initial in
    let n' = goodmod n l in
    let (front,rear) = CList.chop n' initial in
    rear@front
  end

let swap i j =
  let open Proof in
  InfoL.leaf (Info.Tactic (fun _ _ -> Pp.(hov 2 (str"swap"++spc()++int i++spc()++int j)))) >>
  Comb.modify begin fun initial ->
    let l = CList.length initial in
    let i = if i>0 then i-1 else i and j = if j>0 then j-1 else j in
    let i = goodmod i l and j = goodmod j l in
    CList.map_i begin fun k x ->
      match k with
      | k when Int.equal k i -> CList.nth initial j
      | k when Int.equal k j -> CList.nth initial i
      | _ -> x
    end 0 initial
  end

let revgoals =
  let open Proof in
  InfoL.leaf (Info.Tactic (fun _ _ -> Pp.str"revgoals")) >>
  Comb.modify CList.rev

let numgoals =
  let open Proof in
  Comb.get >>= fun comb ->
  return (CList.length comb)



(** {7 Access primitives} *)

let tclEVARMAP = Solution.get

let tclENV = Env.get



(** {7 Put-like primitives} *)


let emit_side_effects eff x =
  { x with solution = Evd.emit_side_effects eff x.solution }

let tclEFFECTS eff =
  let open Proof in
  return () >>= fun () -> (* The Global.env should be taken at exec time *)
  Env.set (Global.env ()) >>
  Pv.modify (fun initial -> emit_side_effects eff initial)

let mark_as_unsafe = Status.put false

(** Gives up on the goal under focus. Reports an unsafe status. Proofs
    with given up goals cannot be closed. *)

let give_up evs pv =
  let solution = List.fold_left (fun sigma ev -> Evd.give_up (drop_state ev) sigma) pv.solution evs in
  { pv with solution }

let give_up =
  let open Proof in
  Comb.get >>= fun initial ->
  Comb.set [] >>
  mark_as_unsafe >>
  InfoL.leaf (Info.Tactic (fun _ _ -> Pp.str"give_up")) >>
  Pv.modify (give_up initial)


(** {7 Control primitives} *)


module Progress = struct

  let eq_constr evd extended_evd =
    Evarutil.eq_constr_univs_test ~evd ~extended_evd

  (** equality function on hypothesis contexts *)
  let eq_named_context_val sigma1 sigma2 ctx1 ctx2 =
    let c1 = EConstr.named_context_of_val ctx1 and c2 = EConstr.named_context_of_val ctx2 in
    let eq_named_declaration d1 d2 =
      match d1, d2 with
      | LocalAssum (i1,t1), LocalAssum (i2,t2) ->
         Context.eq_annot Names.Id.equal i1 i2 && eq_constr sigma1 sigma2 t1 t2
      | LocalDef (i1,c1,t1), LocalDef (i2,c2,t2) ->
         Context.eq_annot Names.Id.equal i1 i2 && eq_constr sigma1 sigma2 c1 c2
         && eq_constr sigma1 sigma2 t1 t2
      | _ ->
         false
    in List.equal eq_named_declaration c1 c2

  let eq_evar_body sigma1 sigma2 b1 b2 =
    let open Evd in
    match b1, b2 with
    | Evar_empty, Evar_empty -> true
    | Evar_defined t1, Evar_defined t2 -> eq_constr sigma1 sigma2 t1 t2
    | _ -> false

  let eq_evar_info sigma1 sigma2 ei1 ei2 =
    let open Evd in
    eq_constr sigma1 sigma2 ei1.evar_concl ei2.evar_concl &&
    eq_named_context_val sigma1 sigma2 (ei1.evar_hyps) (ei2.evar_hyps) &&
    eq_evar_body sigma1 sigma2 ei1.evar_body ei2.evar_body

  (** Equality function on goals *)
  let goal_equal ~evd ~extended_evd evar extended_evar =
    let evi = Evd.find evd evar in
    let extended_evi = Evd.find extended_evd extended_evar in
    eq_evar_info evd extended_evd evi extended_evi

end

let tclPROGRESS t =
  let open Proof in
  Pv.get >>= fun initial ->
  t >>= fun res ->
  Pv.get >>= fun final ->
  (* [*_test] test absence of progress. [quick_test] is approximate
     whereas [exhaustive_test] is complete. *)
  let quick_test =
    initial.solution == final.solution && initial.comb == final.comb
  in
  let test =
    quick_test ||
    Util.List.for_all2eq begin fun i f ->
      Progress.goal_equal ~evd:initial.solution
        ~extended_evd:final.solution (drop_state i) (drop_state f)
    end initial.comb final.comb
  in
  if not test then
    tclUNIT res
  else
    let info = Exninfo.reify () in
    tclZERO ~info (CErrors.UserError (Some "Proofview.tclPROGRESS", Pp.str "Failed to progress."))

let _ = CErrors.register_handler begin function
  | Logic_monad.Tac_Timeout ->
    Some (Pp.str "[Proofview.tclTIMEOUT] Tactic timeout!")
  | _ -> None
end

let tclTIMEOUT n t =
  let open Proof in
  (* spiwack: as one of the monad is a continuation passing monad, it
     doesn't force the computation to be threaded inside the underlying
     (IO) monad. Hence I force it myself by asking for the evaluation of
     a dummy value first, lest [timeout] be called when everything has
     already been computed. *)
  let t = Proof.lift (Logic_monad.NonLogical.return ()) >> t in
  Proof.get >>= fun initial ->
  Proof.current >>= fun envvar ->
  Proof.lift begin
    Logic_monad.NonLogical.catch
      begin
        let open Logic_monad.NonLogical in
        timeout n (Proof.repr (Proof.run t envvar initial)) >>= fun r ->
        match r with
        | Logic_monad.Nil e -> return (Util.Inr e)
        | Logic_monad.Cons (r, _) -> return (Util.Inl r)
      end
      begin let open Logic_monad.NonLogical in function (e, info) ->
        match e with
        | Logic_monad.Tac_Timeout ->
          return (Util.Inr (Logic_monad.Tac_Timeout, info))
        | Logic_monad.TacticFailure e ->
          return (Util.Inr (e, info))
        | e -> Logic_monad.NonLogical.raise (e, info)
      end
  end >>= function
    | Util.Inl (res,s,m,i) ->
        Proof.set s >>
        Proof.put m >>
        Proof.update (fun _ -> i) >>
        return res
    | Util.Inr (e, info) -> tclZERO ~info e

let tclTIME s t =
  let pr_time t1 t2 n msg =
    let msg =
      if n = 0 then
        str msg
      else
        str (msg ^ " after ") ++ int n ++ str (String.plural n " backtracking")
    in
    Feedback.msg_info(str "Tactic call" ++ pr_opt str s ++ str " ran for " ++
             System.fmt_time_difference t1 t2 ++ str " " ++ surround msg) in
  let rec aux n t =
    let open Proof in
    tclUNIT () >>= fun () ->
    let tstart = System.get_time() in
    Proof.split t >>= let open Logic_monad in function
    | Nil (e, info) ->
      begin
        let tend = System.get_time() in
        pr_time tstart tend n "failure";
        tclZERO ~info e
      end
    | Cons (x,k) ->
        let tend = System.get_time() in
        pr_time tstart tend n "success";
        tclOR (tclUNIT x) (fun e -> aux (n+1) (k e))
  in aux 0 t

let tclProofInfo =
  let open Proof in
  Logical.current >>= fun P.{name; poly} ->
  tclUNIT (name, poly)

(** {7 Unsafe primitives} *)

module Unsafe = struct

  let (>>=) = tclBIND

  let tclEVARS evd =
    Pv.modify (fun ps -> { ps with solution = Evd.clear_metas evd })

  let tclNEWGOALS gls =
    Pv.modify begin fun step ->
      let gls = undefined step.solution gls in
      { step with comb = step.comb @ gls }
    end

  let tclNEWSHELVED gls =
    Pv.modify begin fun step ->
      let gls = undefined_evars step.solution gls in
      { step with solution = Evd.shelve step.solution gls }
    end

  let tclGETSHELF = tclEVARMAP >>= fun sigma -> tclUNIT @@ Evd.shelf sigma

  let tclSETENV = Env.set

  let tclGETGOALS = Comb.get

  let tclSETGOALS = Comb.set

  let tclEVARSADVANCE evd =
    Pv.modify (fun ps -> { solution = evd; comb = undefined evd ps.comb })

  let tclEVARUNIVCONTEXT ctx =
    Pv.modify (fun ps -> { ps with solution = Evd.set_universe_context ps.solution ctx })

  let push_future_goals p =
    { p with solution = Evd.push_future_goals p.solution }

  let mark_as_goals evd content =
    mark_in_evm ~goal:true evd content

  let advance = Evarutil.advance

  let undefined = undefined

  let mark_unresolvables evm evs =
    mark_in_evm ~goal:false evm evs

  let mark_as_unresolvables p evs =
    { p with solution = mark_in_evm ~goal:false p.solution evs }

  let update_sigma_univs ugraph pv =
    { pv with solution = Evd.update_sigma_univs ugraph pv.solution }

end

module UnsafeRepr = Proof.Unsafe

let (>>=) = tclBIND

(** {6 Goal-dependent tactics} *)

let goal_env env evars gl =
  let evi = Evd.find evars gl in
  Evd.evar_filtered_env env evi

let goal_nf_evar sigma gl =
  let evi = Evd.find sigma gl in
  let evi = Evarutil.nf_evar_info sigma evi in
  let sigma = Evd.add sigma gl evi in
  (gl, sigma)


let catchable_exception = function
  | Logic_monad.Exception _ -> false
  | e -> CErrors.noncritical e


module Goal = struct

  type t = {
    env : Environ.env;
    sigma : Evd.evar_map;
    concl : EConstr.constr ;
    state : StateStore.t;
    self : Evar.t ; (* for compatibility with old-style definitions *)
  }

  let print { sigma; self } = { Evd.it = self; sigma }

  let state { state=state } = state

  let env {env} = env
  let sigma {sigma} = sigma
  let hyps {env} = EConstr.named_context env
  let concl {concl} = concl

  let gmake_with info env sigma goal state =
    { env = Environ.reset_with_named_context (Evd.evar_filtered_hyps info) env ;
      sigma = sigma ;
      concl = Evd.evar_concl info;
      state = state ;
      self = goal }

  let nf_gmake env sigma goal =
    let state = get_state goal in
    let goal = drop_state goal in
    let info = Evarutil.nf_evar_info sigma (Evd.find sigma goal) in
    let sigma = Evd.add sigma goal info in
    gmake_with info env sigma goal state , sigma

  let nf_enter f =
    InfoL.tag (Info.Dispatch) begin
    iter_goal begin fun goal ->
      tclENV >>= fun env ->
      tclEVARMAP >>= fun sigma ->
      try
        let (gl, sigma) = nf_gmake env sigma goal in
        tclTHEN (Unsafe.tclEVARS sigma) (InfoL.tag (Info.DBranch) (f gl))
      with e when catchable_exception e ->
        let (e, info) = Exninfo.capture e in
        tclZERO ~info e
    end
    end
  let gmake env sigma goal =
    let state = get_state goal in
    let goal = drop_state goal in
    let info = Evd.find sigma goal in
    gmake_with info env sigma goal state

  let enter f =
    let f gl = InfoL.tag (Info.DBranch) (f gl) in
    InfoL.tag (Info.Dispatch) begin
    iter_goal begin fun goal ->
      Env.get >>= fun env ->
      tclEVARMAP >>= fun sigma ->
      try f (gmake env sigma goal)
      with e when catchable_exception e ->
        let (e, info) = Exninfo.capture e in
        tclZERO ~info e
    end
    end

  let enter_one ?(__LOC__=__LOC__) f =
    let open Proof in
    Comb.get >>= function
    | [goal] -> begin
       Env.get >>= fun env ->
       tclEVARMAP >>= fun sigma ->
       try f (gmake env sigma goal)
       with e when catchable_exception e ->
         let (e, info) = Exninfo.capture e in
         tclZERO ~info e
      end
    | _ ->
       CErrors.anomaly Pp.(str __LOC__ ++ str " enter_one")

  let goals =
    Pv.get >>= fun step ->
    let sigma = step.solution in
    let map goal =
      match cleared_alias sigma goal with
      | None -> None (* ppedrot: Is this check really necessary? *)
      | Some goal ->
        let gl =
          Env.get >>= fun env ->
          tclEVARMAP >>= fun sigma ->
          tclUNIT (gmake env sigma goal)
        in
        Some gl
    in
    tclUNIT (CList.map_filter map step.comb)

  let unsolved { self=self } =
    tclEVARMAP >>= fun sigma ->
    tclUNIT (not (Option.is_empty (Evarutil.advance sigma self)))

  (* compatibility *)
  let goal { self=self } = self

end



(** {6 Trace} *)

module Trace = struct

  let record_info_trace = InfoL.record_trace

  let log m = InfoL.leaf (Info.Msg m)
  let name_tactic m t = InfoL.tag (Info.Tactic m) t

  let pr_info env sigma ?(lvl=0) info =
    assert (lvl >= 0);
    Info.(print env sigma (collapse lvl info))

end



(** {6 Non-logical state} *)

module NonLogical = Logic_monad.NonLogical

let tclLIFT = Proof.lift

let tclCHECKINTERRUPT =
   tclLIFT (NonLogical.make Control.check_for_interrupt)

(*** Compatibility layer with <= 8.2 tactics ***)
module V82 = struct
  type tac = Evar.t Evd.sigma -> Evar.t list Evd.sigma

  let tactic ?(nf_evars=true) tac =
    (* spiwack: we ignore the dependencies between goals here,
       expectingly preserving the semantics of <= 8.2 tactics *)
    (* spiwack: convenience notations, waiting for ocaml 3.12 *)
    let open Proof in
    Pv.get >>= fun ps ->
    try
      let tac g_w_s evd =
        let g, w = drop_state g_w_s, get_state g_w_s in
        let glsigma  =
          tac { Evd.it = g ; sigma = evd; }  in
        let sigma = glsigma.Evd.sigma in
        let g = CList.map (fun g -> goal_with_state g w) glsigma.Evd.it in
        ( g, sigma )
      in
        (* Old style tactics expect the goals normalized with respect to evars. *)
      let (initgoals_w_state, initevd) =
        Evd.Monad.List.map (fun g_w_s s ->
          let g, w = drop_state g_w_s, get_state g_w_s in
          let g, s = if nf_evars then goal_nf_evar s g else g, s in
          goal_with_state g w, s) ps.comb ps.solution
      in
      let (goalss,evd) = Evd.Monad.List.map tac initgoals_w_state initevd in
      let sgs = CList.flatten goalss in
      let sgs = undefined evd sgs in
      InfoL.leaf (Info.Tactic (fun _ _ -> Pp.str"<unknown>")) >>
      Pv.set { solution = evd; comb = sgs; }
    with e when catchable_exception e ->
      let (e, info) = Exninfo.capture e in
      tclZERO ~info e


  (* normalises the evars in the goals, and stores the result in
     solution. *)
  let nf_evar_goals =
    Pv.modify begin fun ps ->
    let map g s = goal_nf_evar s g in
    let comb = CList.map drop_state ps.comb in
    let (_goals,evd) = Evd.Monad.List.map map comb ps.solution in
    { ps with solution = evd; }
    end

  let has_unresolved_evar pv =
    Evd.has_undefined pv.solution

  (* Main function in the implementation of Grab Existential Variables.*)
  let grab pv =
    let undef = Evd.undefined_map pv.solution in
    let goals = CList.rev_map fst (Evar.Map.bindings undef) in
    { pv with comb = List.map with_empty_state goals }



  let top_goals initial { solution=solution; } =
    let goals = CList.map (fun (t,_) -> fst (Constr.destEvar (EConstr.Unsafe.to_constr t))) initial in
    { Evd.it = goals ; sigma=solution; }

  let top_evars initial { solution=sigma; } =
    let evars_of_initial (c,_) =
      Evar.Set.elements (Evd.evar_nodes_of_term c)
    in
    CList.flatten (CList.map evars_of_initial initial)

  let of_tactic t gls =
    try
      let env = Global.env () in
      let init = { solution = gls.Evd.sigma ; comb = [with_empty_state gls.Evd.it] } in
      let name, poly = Names.Id.of_string "legacy_pe", false in
      let (_,final,_,_) = apply ~name ~poly (goal_env env gls.Evd.sigma gls.Evd.it) t init in
      { Evd.sigma = final.solution ; it = CList.map drop_state final.comb }
    with Logic_monad.TacticFailure e as src ->
      let (_, info) = Exninfo.capture src in
      Exninfo.iraise (e, info)

  let put_status = Status.put

  let catchable_exception = catchable_exception

  let wrap_exceptions f =
    try f ()
    with e when catchable_exception e ->
      let (e, info) = Exninfo.capture e in tclZERO ~info e

end

(** {7 Notations} *)

module Notations = struct
  let (>>=) = tclBIND
  let (<*>) = tclTHEN
  let (<+>) t1 t2 = tclOR t1 (fun _ -> t2)
end
