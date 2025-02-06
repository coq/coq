(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pp
open Util
open Names
open Term
open Constr
open Termops
open EConstr
open Tactics
open Typeclasses
open Evd
open Locus
open Proofview.Notations
open Hints

module NamedDecl = Context.Named.Declaration

(** Hint database named "typeclass_instances", created in prelude *)
let typeclasses_db = "typeclass_instances"

(** Options handling *)

let typeclasses_depth_opt_name = ["Typeclasses";"Depth"]
let { Goptions.get = get_typeclasses_depth } =
  Goptions.declare_intopt_option_and_ref
    ~key:typeclasses_depth_opt_name
    ~value:None
    ()

let set_typeclasses_depth =
  Goptions.set_int_option_value typeclasses_depth_opt_name

(** When this flag is enabled, the resolution of type classes tries to avoid
    useless introductions. This is no longer useful since we have eta, but is
    here for compatibility purposes. Another compatibility issues is that the
    cost (in terms of search depth) can differ. *)
let { Goptions.get = get_typeclasses_limit_intros } =
  Goptions.declare_bool_option_and_ref
    ~key:["Typeclasses";"Limit";"Intros"]
    ~value:true
    ()

let { Goptions.get = get_typeclasses_dependency_order } =
  Goptions.declare_bool_option_and_ref
    ~key:["Typeclasses";"Dependency";"Order"]
    ~value:false
    ()

let iterative_deepening_opt_name = ["Typeclasses";"Iterative";"Deepening"]
let { Goptions.get = get_typeclasses_iterative_deepening } =
  Goptions.declare_bool_option_and_ref
    ~key:iterative_deepening_opt_name
    ~value:false
    ()

module Debug : sig
  val ppdebug : int -> (unit -> Pp.t) -> unit

  val get_debug : unit -> int

  val set_typeclasses_debug : bool -> unit
end = struct
  let typeclasses_debug = ref 0

  let set_typeclasses_debug d = (:=) typeclasses_debug (if d then 1 else 0)
  let get_typeclasses_debug () = if !typeclasses_debug > 0 then true else false

  let set_typeclasses_verbose = function
    | None -> typeclasses_debug := 0
    | Some n -> typeclasses_debug := n
  let get_typeclasses_verbose () =
    if !typeclasses_debug = 0 then None else Some !typeclasses_debug

  let () =
    let open Goptions in
    declare_bool_option
      { optstage = Summary.Stage.Interp;
        optdepr  = None;
        optkey   = ["Typeclasses";"Debug"];
        optread  = get_typeclasses_debug;
        optwrite = set_typeclasses_debug; }

  let () =
    let open Goptions in
    declare_int_option
      { optstage = Summary.Stage.Interp;
        optdepr  = None;
        optkey   = ["Typeclasses";"Debug";"Verbosity"];
        optread  = get_typeclasses_verbose;
        optwrite = set_typeclasses_verbose; }

  let ppdebug lvl pp =
    if !typeclasses_debug > lvl then Feedback.msg_debug (pp())

  let get_debug () = !typeclasses_debug
end
open Debug
let set_typeclasses_debug = set_typeclasses_debug

type search_strategy = Dfs | Bfs

let set_typeclasses_strategy = function
  | Dfs -> Goptions.set_bool_option_value iterative_deepening_opt_name false
  | Bfs -> Goptions.set_bool_option_value iterative_deepening_opt_name true

let pr_ev evs ev =
  let evi = Evd.find_undefined evs ev in
  let env = Evd.evar_filtered_env (Global.env ()) evi in
  Printer.pr_econstr_env env evs (Evd.evar_concl evi)

let pr_ev_with_id evs ev =
  Evar.print ev ++ str " : " ++ pr_ev evs ev

  (** Typeclasses instance search tactic / eauto *)

open Auto
open Unification

let auto_core_unif_flags st allowed_evars = {
  modulo_conv_on_closed_terms = Some st;
  use_metas_eagerly_in_conv_on_closed_terms = true;
  use_evars_eagerly_in_conv_on_closed_terms = false;
  modulo_delta = st;
  modulo_delta_types = st;
  check_applied_meta_types = false;
  use_pattern_unification = true;
  use_meta_bound_pattern_unification = true;
  allowed_evars;
  restrict_conv_on_strict_subterms = false; (* ? *)
  modulo_betaiota = true;
  modulo_eta = false;
}

let auto_unif_flags ?(allowed_evars = Evarsolve.AllowedEvars.all) st =
  let fl = auto_core_unif_flags st allowed_evars in
  { core_unify_flags = fl;
    merge_unify_flags = fl;
    subterm_unify_flags = fl;
    allow_K_in_toplevel_higher_order_unification = false;
    resolve_evars = false
}

let e_give_exact flags h =
  let open Tacmach in
  Proofview.Goal.enter begin fun gl ->
  let env = Proofview.Goal.env gl in
  let sigma = project gl in
  let sigma, c = Hints.fresh_hint env sigma h in
  let (sigma, t1) = Typing.type_of (pf_env gl) sigma c in
  Proofview.Unsafe.tclEVARS sigma <*>
  Clenv.unify ~flags ~cv_pb:CUMUL t1 <*> exact_no_check c
  end

let unify_resolve ~with_evars flags h diff = match diff with
| None ->
  Hints.hint_res_pf ~with_evars ~with_classes:false ~flags h
| Some (diff, ty) ->
  let () = assert (Option.is_empty (fst @@ hint_as_term @@ h)) in
  Proofview.Goal.enter begin fun gl ->
  let env = Proofview.Goal.env gl in
  let sigma = Tacmach.project gl in
  let sigma, c = Hints.fresh_hint env sigma h in
  let clenv = Clenv.mk_clenv_from_n env sigma diff (c, ty) in
  Clenv.res_pf ~with_evars ~with_classes:false ~flags clenv
  end

(** Dealing with goals of the form A -> B and hints of the form
  C -> A -> B.
*)
let with_prods nprods h f =
  if get_typeclasses_limit_intros () then
    Proofview.Goal.enter begin fun gl ->
      if Option.has_some (fst @@ hint_as_term h) || Int.equal nprods 0 then f None
      else
        let sigma = Tacmach.project gl in
        let ty = Retyping.get_type_of (Proofview.Goal.env gl) sigma (snd @@ hint_as_term h) in
        let diff = nb_prod sigma ty - nprods in
        if (>=) diff 0 then f (Some (diff, ty))
        else Tacticals.tclZEROMSG (str"Not enough premisses")
    end
  else Proofview.Goal.enter
         begin fun gl ->
         if Int.equal nprods 0 then f None
         else Tacticals.tclZEROMSG (str"Not enough premisses") end

(** Semantics of type class resolution lemma application:

  - Use unification to find a well-typed substitution. There might
    be evars in the goal and the lemma. Evars in the goal can get refined.
  - Independent evars are turned into goals, whatever their kind is.
  - Dependent evars of the lemma corresponding to arguments which appear
    in independent goals or the conclusion are turned into subgoals iff
    they are of typeclass kind.
  - The remaining dependent evars not of typeclass type are shelved,
    and resolution must fill them for it to succeed, otherwise we
    backtrack.
 *)

let pr_gls sigma gls =
  prlist_with_sep spc
   (fun ev -> int (Evar.repr ev) ++ spc () ++ pr_ev sigma ev) gls

(** Ensure the dependent subgoals are shelved after an apply/eapply. *)
let shelve_dependencies gls =
  let open Proofview in
  if CList.is_empty gls then tclUNIT ()
  else
    tclEVARMAP >>= fun sigma ->
    ppdebug 1 (fun () -> str" shelving dependent subgoals: " ++ pr_gls sigma gls);
    shelve_goals gls

let hintmap_of env sigma hdc secvars concl =
  match hdc with
  | None -> fun db -> ModeMatch (NoMode, Hint_db.map_none ~secvars db)
  | Some hdc ->
    fun db -> Hint_db.map_eauto env sigma ~secvars hdc concl db

(** Hack to properly solve dependent evars that are typeclasses *)
let rec e_trivial_fail_db db_list local_db secvars =
  let open Tacticals in
  let open Tacmach in
  let trivial_fail =
    Proofview.Goal.enter
    begin fun gl ->
    let env = Proofview.Goal.env gl in
    let sigma = Tacmach.project gl in
    let d = NamedDecl.get_id @@ pf_last_hyp gl in
    let hints = push_resolve_hyp env sigma d local_db in
      e_trivial_fail_db db_list hints secvars
      end
  in
  let trivial_resolve =
    Proofview.Goal.enter
    begin fun gl ->
    let tacs = e_trivial_resolve db_list local_db secvars
                                 (pf_env gl) (project gl) (pf_concl gl) in
      tclFIRST (List.map (fun (x,_,_,_,_) -> x) tacs)
    end
  in
  let tacl =
    Eauto.e_assumption ::
    (tclTHEN Tactics.intro trivial_fail :: [trivial_resolve])
  in
  tclSOLVE tacl

and e_my_find_search db_list local_db secvars hdc complete env sigma concl0 =
  let prods, concl = EConstr.decompose_prod_decls sigma concl0 in
  let nprods = List.length prods in
  let allowed_evars =
    let all = Evarsolve.AllowedEvars.all in
    match hdc with
    | Some (hd,_) ->
      begin match Typeclasses.class_info hd with
      | Some cl ->
        if cl.cl_strict then
          let undefined = lazy (Evarutil.undefined_evars_of_term sigma concl) in
          let allowed evk = not (Evar.Set.mem evk (Lazy.force undefined)) in
          Evarsolve.AllowedEvars.from_pred allowed
        else all
      | None -> all
      end
    | _ -> all
  in
  let tac_of_hint =
    fun (flags, h) ->
      let name = FullHint.name h in
      let tac = function
        | Res_pf h ->
          let tac =
            with_prods nprods h (unify_resolve ~with_evars:false flags h) in
            Proofview.tclBIND (Proofview.with_shelf tac)
              (fun (gls, ()) -> shelve_dependencies gls)
        | ERes_pf h ->
          let tac =
            with_prods nprods h (unify_resolve ~with_evars:true flags h) in
            Proofview.tclBIND (Proofview.with_shelf tac)
              (fun (gls, ()) -> shelve_dependencies gls)
        | Give_exact h ->
          e_give_exact flags h
      | Res_pf_THEN_trivial_fail h ->
         let fst = with_prods nprods h (unify_resolve ~with_evars:true flags h) in
         let snd = if complete then Tacticals.tclIDTAC
                   else e_trivial_fail_db db_list local_db secvars in
         Tacticals.tclTHEN fst snd
      | Unfold_nth c ->
         Proofview.tclPROGRESS (unfold_in_concl [AllOccurrences,c])
      | Extern (p, tacast) -> conclPattern concl0 p tacast
      in
      let tac = FullHint.run h tac in
      let tac = if complete then Tacticals.tclCOMPLETE tac else tac in
      let extern = match FullHint.repr h with
        | Extern _ -> true
        | _ -> false
      in
      (tac, FullHint.priority h, extern, name, lazy (FullHint.print env sigma h))
  in
  let hint_of_db = hintmap_of env sigma hdc secvars concl in
  let hintl = List.map_filter (fun db -> match hint_of_db db with
      | ModeMatch (m, l) -> Some (db, m, l)
      | ModeMismatch -> None)
      (local_db :: db_list)
  in
  (* In case there is a mode mismatch in all the databases we get stuck.
     Otherwise we consider the hints that match.
     Recall the local database uses the union of all the modes in the other databases. *)
  if List.is_empty hintl then None
  else
    let hintl =
      CList.map
        (fun (db, m, tacs) ->
          let flags = auto_unif_flags ~allowed_evars (Hint_db.transparent_state db) in
          m, List.map (fun x -> tac_of_hint (flags, x)) tacs)
        hintl
    in
    let modes, hintl = List.split hintl in
    let all_mode_match = List.for_all (fun m -> m != NoMode) modes in
    let hintl = match hintl with
      (* Optim: only sort if multiple hint sources were involved *)
      | [hintl] -> hintl
      | _ ->
        let hintl = List.flatten hintl in
        let hintl = List.stable_sort
            (fun (_, pri1, _, _, _) (_, pri2, _, _, _) -> Int.compare pri1 pri2)
            hintl
        in
        hintl
    in
    Some (all_mode_match, hintl)

and e_trivial_resolve db_list local_db secvars env sigma concl =
  let hd = try Some (decompose_app_bound sigma concl) with Bound -> None in
  try
    (match e_my_find_search db_list local_db secvars hd true env sigma concl with
    | Some (_,l) -> l
    | None -> [])
  with Not_found -> []

let e_possible_resolve db_list local_db secvars env sigma concl =
  let hd = try Some (decompose_app_bound sigma concl) with Bound -> None in
  try
    e_my_find_search db_list local_db secvars hd false env sigma concl
  with Not_found -> Some (true, [])

let cut_of_hints h =
  List.fold_left (fun cut db -> PathOr (Hint_db.cut db, cut)) PathEmpty h

let pr_depth l =
  let rec fmt elts =
    match elts with
    | [] -> []
    | [n] -> [string_of_int n]
    | n1::n2::rest ->
       (string_of_int n1 ^ "." ^ string_of_int n2) :: fmt rest
  in
  prlist_with_sep (fun () -> str "-") str (fmt (List.rev l))

let is_Prop env sigma concl =
  let ty = Retyping.get_type_of env sigma concl in
  match EConstr.kind sigma ty with
  | Sort s ->
    begin match ESorts.kind sigma s with
    | Prop -> true
    | _ -> false
    end
  | _ -> false

let is_unique env sigma concl =
  try
    let (cl,u), args = dest_class_app env sigma concl in
    cl.cl_unique
  with e when CErrors.noncritical e -> false

(** Sort the undefined variables from the least-dependent to most dependent. *)
let top_sort evm undefs =
  let l' = ref [] in
  let tosee = ref undefs in
  let cache = Evarutil.create_undefined_evars_cache () in
  let rec visit ev evi =
    let evs = Evarutil.filtered_undefined_evars_of_evar_info ~cache evm evi in
      tosee := Evar.Set.remove ev !tosee;
      Evar.Set.iter (fun ev ->
        if Evar.Set.mem ev !tosee then
          visit ev (Evd.find_undefined evm ev)) evs;
      l' := ev :: !l';
  in
    while not (Evar.Set.is_empty !tosee) do
      let ev = Evar.Set.choose !tosee in
        visit ev (Evd.find_undefined evm ev)
    done;
    List.rev !l'

(** We transform the evars that are concerned by this resolution
    (according to predicate p) into goals.
    Invariant: function p only manipulates and returns undefined evars
*)

let evars_to_goals p evm =
  let goals, nongoals = Evar.Set.partition (p evm) (Evd.get_typeclass_evars evm) in
  if Evar.Set.is_empty goals then None
  else Some (goals, nongoals)

(** Making local hints  *)
let make_resolve_hyp env sigma st only_classes decl db =
  let id = NamedDecl.get_id decl in
  let cty = NamedDecl.get_type decl in
  let is_class =
    let ctx, ar = decompose_prod_decls sigma cty in
      match EConstr.kind sigma (fst (decompose_app sigma ar)) with
      | Const (c,_) -> is_class (GlobRef.ConstRef c)
      | Ind (i,_) -> is_class (GlobRef.IndRef i)
      | _ -> false
  in
  let keep = not only_classes || is_class in
    if keep then
      let id = GlobRef.VarRef id in
      push_resolves env sigma id db
    else db

let make_hints env sigma (modes,st) only_classes sign =
  let db = Hint_db.add_modes modes @@ Hint_db.empty st true in
  List.fold_right
    (fun hyp hints ->
      let consider =
        not only_classes ||
        try let t = hyp |> NamedDecl.get_id |> Global.lookup_named |> NamedDecl.get_type in
            (* Section variable, reindex only if the type changed *)
            not (EConstr.eq_constr sigma (EConstr.of_constr t) (NamedDecl.get_type hyp))
        with Not_found -> true
      in
      if consider then
        make_resolve_hyp env sigma st only_classes hyp hints
      else hints)
    sign db

module Intpart = Unionfind.Make(Evar.Set)(Evar.Map)

type solver = { solver :
  Environ.env ->
  Evd.evar_map ->
  depth:int option ->
  unique:bool ->
  best_effort:bool ->
  goals:Evar.t list ->
  (bool * Evd.evar_map)
}

module Search = struct
  type autoinfo =
    { search_depth : int list;
      last_tac : Pp.t Lazy.t;
      search_dep : bool;
      search_only_classes : bool;
      search_cut : hints_path;
      search_hints : hint_db;
      search_best_effort : bool;
      }

  (** Local hints *)
  let autogoal_cache = Summary.ref ~name:"autogoal_cache"
      (DirPath.empty, true, Context.Named.empty, Hints.Modes.empty,
       Hint_db.empty TransparentState.full true)

  let make_autogoal_hints only_classes (modes,st as mst) gl =
    let env = Proofview.Goal.env gl in
    let sigma = Proofview.Goal.sigma gl in
    let sign = EConstr.named_context env in
    let (dir, onlyc, sign', cached_modes, cached_hints) = !autogoal_cache in
    let cwd = Lib.cwd () in
    let eq c1 c2 = EConstr.eq_constr sigma c1 c2 in
    if DirPath.equal cwd dir &&
         (onlyc == only_classes) &&
           Context.Named.equal (ERelevance.equal sigma) eq sign sign' &&
             cached_modes == modes
    then cached_hints
    else
      let hints = make_hints env sigma mst only_classes sign in
      autogoal_cache := (cwd, only_classes, sign, modes, hints); hints

  let make_autogoal mst only_classes dep cut best_effort i g =
    let hints = make_autogoal_hints only_classes mst g in
    { search_hints = hints;
      search_depth = [i]; last_tac = lazy (str"none");
      search_dep = dep;
      search_only_classes = only_classes;
      search_cut = cut;
      search_best_effort = best_effort }

  (** In the proof engine failures are represented as exceptions *)
  exception ReachedLimit
  exception NoApplicableHint
  exception StuckGoal

  (** ReachedLimit has priority over NoApplicableHint to handle
      iterative deepening: it should fail when no hints are applicable,
      but go to a deeper depth otherwise. *)
  let merge_exceptions e e' =
    match fst e, fst e' with
    | ReachedLimit, _ -> e
    | _, ReachedLimit -> e'
    | _, _ -> e

  (** Determine if backtracking is needed for this goal.
      We generally backtrack except in the following (possibly
      overlapping) cases:
      - [unique_instances] is [true].
        This is the case when the goal's class has [Unique Instances].
      - [indep] is [true] and the current goal has no evars.
        [indep] is generally [true] and only gets set to [false] if the
        current goal's evar is mentioned in other goals.
        ([indep] is the negation of [search_dep].)
      - The current goal is a [Prop] and has no evars. *)
  let needs_backtrack env evd ~unique_instances ~indep concl =
    if unique_instances then false else
    if indep || is_Prop env evd concl then
      occur_existential evd concl
    else true

  exception NonStuckFailure
  (* exception Backtrack *)

  let pr_goals s =
    let open Proofview in
    if get_debug() > 1 then
      tclEVARMAP >>= fun sigma ->
      Unsafe.tclGETGOALS >>= fun gls ->
      let gls = CList.map Proofview.drop_state gls in
      let j = List.length gls in
      let pr_goal gl = pr_ev_with_id sigma gl in
      Feedback.msg_debug
        (s ++ int j ++ str" goals:" ++ spc () ++
         prlist_with_sep Pp.fnl pr_goal gls);
      tclUNIT ()
    else
      tclUNIT ()

  let pr_internal_exception ie =
    match fst ie with
    | ReachedLimit -> str "Proof-search reached its limit."
    | NoApplicableHint -> str "Proof-search failed."
    | StuckGoal | NonStuckFailure -> str "Proof-search got stuck."
    | e -> CErrors.iprint ie

  (* XXX Is this handler needed for something? *)
  let () = CErrors.register_handler begin function
    | NonStuckFailure -> Some (str "NonStuckFailure")
    | NoApplicableHint -> Some (str "NoApplicableHint")
    | _ -> None
    end

  (**
    For each success of tac1 try tac2.
    If tac2 raises NonStuckFailure, try the next success of tac1 until depleted.
    If tac1 finally fails, returns the result of the first tac1 success, if any.
  *)

  type goal_status =
    | IsInitial
    | IsStuckGoal
    | IsNonStuckFailure

  let pr_goal_status = function
    | IsInitial -> str "initial"
    | IsStuckGoal -> str "stuck"
    | IsNonStuckFailure -> str "stuck failure"


  let pr_search_goal sigma (glid, ev, status, _) =
    str"Goal " ++ int glid ++ str" evar: " ++ Evar.print ev ++ str " status: " ++ pr_goal_status status

  let pr_search_goals sigma =
    prlist_with_sep fnl (pr_search_goal sigma)

  let search_fixpoint ~best_effort ~allow_out_of_order tacs =
    let open Pp in
    let open Proofview in
    let open Proofview.Notations in
    let rec fixpoint progress tacs stuck fk =
      let next (glid, ev, status, tac) tacs stuck =
        let () = ppdebug 1 (fun () ->
            str "considering goal " ++ int glid ++
            str " of status " ++ pr_goal_status status)
        in
        let rec kont = function
          | Fail ((NonStuckFailure | StuckGoal as exn), info) when allow_out_of_order ->
            let () = ppdebug 1 (fun () ->
                str "Goal " ++ int glid ++
                str" is stuck or failed without being stuck, trying other tactics.")
            in
            let status =
              match exn with
              | NonStuckFailure -> IsNonStuckFailure
              | StuckGoal -> IsStuckGoal
              | _ -> assert false
            in
            cycle 1 (* Puts the first goal last *) <*>
            fixpoint progress tacs ((glid, ev, status, tac) :: stuck) fk (* Launches the search on the rest of the goals *)
          | Fail ie ->
            let () = ppdebug 1 (fun () ->
                str "Goal " ++ int glid ++ str" has no more solutions, returning exception: "
                ++ pr_internal_exception ie)
            in
            fk ie
          | Next (res, fk') ->
            let () = ppdebug 1 (fun () ->
                str "Goal " ++ int glid ++ str" has a success, continuing resolution")
            in
              (* We try to solve the rest of the constraints, and if that fails
                we backtrack to the next result of tac, etc.... Ultimately if none of the solutions
                for tac work, we will come back to the failure continuation fk in one of
                the above cases *)
            fixpoint true tacs stuck (fun e -> tclCASE (fk' e) >>= kont)
        in tclCASE tac >>= kont
      in
      tclEVARMAP >>= fun sigma ->
      let () = ppdebug 1 (fun () ->
          let stuck, failed = List.partition (fun (_, _, status, _) -> status = IsStuckGoal) stuck in
          str"Calling fixpoint on : " ++
          int (List.length tacs) ++ str" initial goals" ++
          str", " ++ int (List.length stuck) ++ str" stuck goals" ++
          str" and " ++ int (List.length failed) ++ str" non-stuck failures kept" ++
          str" with " ++ str(if progress then "" else "no ") ++
          str"progress made in this run." ++ fnl () ++
          str "Stuck: " ++ pr_search_goals sigma stuck ++ fnl () ++
          str "Failed: " ++ pr_search_goals sigma failed ++ fnl () ++
          str "Initial: " ++ pr_search_goals sigma tacs)
      in
      tclCHECKINTERRUPT <*>
      match tacs with
      | tac :: tacs -> next tac tacs stuck
      | [] -> (* All remaining goals are stuck *)
        match stuck with
        | [] ->
            (* We found a solution! Great, but in case it's not good for the rest of the proof search,
               we might have other solutions available through fk. *)
            tclOR (tclUNIT ()) fk
        | stuck ->
          if progress then fixpoint false stuck [] fk
          else (* No progress can be made on the stuck goals arising from this resolution,
            try a different solution on the non-stuck goals, if any. *)
          begin
            tclORELSE (fk (NoApplicableHint, Exninfo.null))
              (fun (e, info) ->
                 let () = ppdebug 1 (fun () -> int (List.length stuck) ++ str " remaining goals left, no progress, calling continuation failed")
                 in
                 (* We keep the stuck goals to display to the user *)
                 if best_effort then
                   let stuckgls, failedgls = List.partition (fun (_, _, status, _) ->
                       match status with
                       | IsStuckGoal -> true
                       | IsNonStuckFailure -> false
                       (* There should remain no initial goals at this point *)
                       | IsInitial -> assert false)
                       stuck
                   in
                   pr_goals (str "best_effort is on and remaining goals are: ") <*>
                   (* We shelve the stuck goals but we keep the non-stuck failures in the goal list.
                      This is for compat with Coq 8.12 but might not be the wisest choice in the long run.
                   *)
                   let to_shelve = List.map (fun (glid, ev, _, _) -> ev) stuckgls in
                   let () = ppdebug 1 (fun () ->
                       str "Shelving subgoals: " ++
                       prlist_with_sep spc Evar.print to_shelve)
                   in
                   Unsafe.tclNEWSHELVED to_shelve
                 else tclZERO ~info e)
          end
    in
    pr_goals (str"Launching resolution fixpoint on ") <*>
    Unsafe.tclGETGOALS >>= fun gls ->
    (* We wrap all goals with their associated tactic.
      It might happen that an initial goal is solved during the resolution of another goal,
      hence the `tclUNIT` in case there is no goal for the tactic to apply anymore. *)
    let tacs = List.map2_i
      (fun i gls tac -> (succ i, Proofview.drop_state gls, IsInitial, tclFOCUS ~nosuchgoal:(tclUNIT ()) 1 1 tac))
      0 gls tacs
    in
    fixpoint false tacs [] (fun (e, info) -> tclZERO ~info e) <*>
    pr_goals (str "Result goals after fixpoint: ")


  (** The general hint application tactic.
      tac1 + tac2 .... The choice of OR or ORELSE is determined
      depending on the dependencies of the goal and the unique/Prop
      status *)
  let hints_tac_gl hints info kont gl : unit Proofview.tactic =
    let open Proofview in
    let open Proofview.Notations in
    let env = Goal.env gl in
    let concl = Goal.concl gl in
    let sigma = Goal.sigma gl in
    let unique_instances = is_unique env sigma concl in
    let indep = not info.search_dep in
    let backtrack = needs_backtrack env sigma ~unique_instances ~indep concl in
    let () = ppdebug 0 (fun () ->
        pr_depth info.search_depth ++ str": looking for " ++
        Printer.pr_econstr_env (Goal.env gl) sigma concl ++
        (if backtrack then str" with backtracking"
         else str" without backtracking"))
    in
    let secvars = compute_secvars gl in
    match e_possible_resolve hints info.search_hints secvars
            env sigma concl with
    | None ->
      Proofview.tclZERO StuckGoal
    | Some (all_mode_match, poss) ->
    (* If no goal depends on the solution of this one or the
       instances are irrelevant/assumed to be unique, then
       we don't need to backtrack, as long as no evar appears in the goal
       This is an overapproximation. Evars could appear in this goal only
       and not any other *)
    let ortac = if backtrack then Proofview.tclOR else Proofview.tclORELSE in
    let idx = ref 1 in
    let foundone = ref false in
    let rec onetac e (tac, pat, b, name, pp) tl =
      let derivs = path_derivate env info.search_cut name in
      let pr_error ie =
        ppdebug 1 (fun () ->
            let idx = if fst ie == NoApplicableHint then pred !idx else !idx in
            let header =
              pr_depth (idx :: info.search_depth) ++ str": " ++
              Lazy.force pp ++
              (if !foundone != true then
                 str" on" ++ spc () ++ pr_ev sigma (Proofview.Goal.goal gl)
               else mt ())
            in
            (header ++ str " failed with: " ++ pr_internal_exception ie))
      in
      let tac_of gls i j = Goal.enter begin fun gl' ->
        let sigma' = Goal.sigma gl' in
        let () = ppdebug 0 (fun () ->
            pr_depth (succ j :: i :: info.search_depth) ++ str" : " ++
            pr_ev sigma' (Proofview.Goal.goal gl'))
        in
        let eq c1 c2 = EConstr.eq_constr sigma' c1 c2 in
        let hints' =
          if b && not (Context.Named.equal (ERelevance.equal sigma) eq (Goal.hyps gl') (Goal.hyps gl))
          then
            let st = Hint_db.transparent_state info.search_hints in
            let modes = Hint_db.modes info.search_hints in
            make_autogoal_hints info.search_only_classes (modes,st) gl'
          else info.search_hints
        in
        let dep' = info.search_dep || Proofview.unifiable sigma' (Goal.goal gl') gls in
        let info' =
          { search_depth = succ j :: i :: info.search_depth;
            last_tac = pp;
            search_dep = dep';
            search_only_classes = info.search_only_classes;
            search_hints = hints';
            search_cut = derivs;
            search_best_effort = info.search_best_effort }
        in kont info' end
      in
      let rec result (shelf, ()) i k =
        foundone := true;
        Proofview.Unsafe.tclGETGOALS >>= fun gls ->
        let gls = CList.map Proofview.drop_state gls in
        let j = List.length gls in
        let () = ppdebug 0 (fun () ->
            pr_depth (i :: info.search_depth) ++ str": " ++ Lazy.force pp
            ++ str" on" ++ spc () ++ pr_ev sigma (Proofview.Goal.goal gl)
            ++ str", " ++ int j ++ str" subgoal(s)" ++
            (Option.cata (fun k -> str " in addition to the first " ++ int k)
               (mt()) k))
        in
        let res =
          if j = 0 then tclUNIT ()
          else search_fixpoint ~best_effort:false ~allow_out_of_order:false
                 (List.init j (fun j' -> (tac_of gls i (Option.default 0 k + j'))))
        in
        let finish nestedshelf sigma =
          let filter ev =
            try
              let evi = Evd.find_undefined sigma ev in
              if info.search_only_classes then
                Some (ev, not (is_class_evar sigma evi))
              else Some (ev, true)
            with Not_found -> None
          in
          let remaining = CList.map_filter filter shelf in
          let () = ppdebug 1 (fun () ->
              let prunsolved (ev, _) = int (Evar.repr ev) ++ spc () ++ pr_ev sigma ev in
              let unsolved = prlist_with_sep spc prunsolved remaining in
              pr_depth (i :: info.search_depth) ++
              str": after " ++ Lazy.force pp ++ str" finished, " ++
              int (List.length remaining) ++
              str " goals are shelved and unsolved ( " ++
              unsolved ++ str")")
          in
          begin
            (* Some existentials produced by the original tactic were not solved
               in the subgoals, turn them into subgoals now. *)
            let shelved, goals = List.partition (fun (ev, s) -> s) remaining in
            let shelved = List.map fst shelved @ nestedshelf and goals = List.map fst goals in
            let () = if not (List.is_empty shelved && List.is_empty goals) then
                ppdebug 1 (fun () ->
                    str"Adding shelved subgoals to the search: " ++
                    prlist_with_sep spc (pr_ev sigma) goals ++
                    str" while shelving " ++
                    prlist_with_sep spc (pr_ev sigma) shelved)
            in
            shelve_goals shelved <*>
            if List.is_empty goals then tclUNIT ()
            else
              let make_unresolvables = tclEVARMAP >>= fun sigma ->
                let sigma = make_unresolvables (fun x -> List.mem_f Evar.equal x goals) sigma in
                Unsafe.tclEVARS sigma
              in
              let goals = CList.map Proofview.with_empty_state goals in
              with_shelf (make_unresolvables <*> Unsafe.tclNEWGOALS goals) >>= fun s ->
              result s i (Some (Option.default 0 k + j))
          end
        in
        with_shelf res >>= fun (sh, ()) ->
        tclEVARMAP >>= finish sh
      in
      if path_matches_epsilon derivs then aux e tl
      else
        ortac
             (with_shelf tac >>= fun s ->
              let i = !idx in incr idx; result s i None)
             (fun e' ->
                (pr_error e'; aux (merge_exceptions e e') tl))
    and aux e = function
      | tac :: tacs -> onetac e tac tacs
      | [] ->
        let () = if !foundone == false then
            ppdebug 0 (fun () ->
                pr_depth info.search_depth ++ str": no match for " ++
                Printer.pr_econstr_env (Goal.env gl) sigma concl ++
                str ", " ++ int (List.length poss) ++
                str" possibilities")
        in
         match e with
         | (ReachedLimit,ie) -> Proofview.tclZERO ~info:ie ReachedLimit
         | (StuckGoal,ie) -> Proofview.tclZERO ~info:ie StuckGoal
         | (NoApplicableHint,ie) ->
            (* If the constraint abides by the (non-trivial) modes but no
               solution could be found, we consider it a failed goal, and let
               proof search proceed on the rest of the
               constraints, thus giving a more precise error message. *)
            if all_mode_match &&
              info.search_best_effort then
              Proofview.tclZERO ~info:ie NonStuckFailure
            else Proofview.tclZERO ~info:ie NoApplicableHint
         | (_,ie) -> Proofview.tclZERO ~info:ie NoApplicableHint
    in
    if backtrack then aux (NoApplicableHint,Exninfo.null) poss
    else tclONCE (aux (NoApplicableHint,Exninfo.null) poss)

  let hints_tac hints info kont : unit Proofview.tactic =
    Proofview.Goal.enter
      (fun gl -> hints_tac_gl hints info kont gl)

  let intro_tac info kont gl =
    let open Proofview in
    let env = Goal.env gl in
    let sigma = Goal.sigma gl in
    let decl = Tacmach.pf_last_hyp gl in
    let ldb =
      make_resolve_hyp env sigma (Hint_db.transparent_state info.search_hints)
                       info.search_only_classes decl info.search_hints in
    let info' =
      { info with search_hints = ldb; last_tac = lazy (str"intro");
        search_depth = 1 :: 1 :: info.search_depth }
    in kont info'

  let intro info kont =
    Proofview.tclBIND Tactics.intro
     (fun _ -> Proofview.Goal.enter (fun gl -> intro_tac info kont gl))

  let rec search_tac hints limit depth =
    let kont info =
      Proofview.numgoals >>= fun i ->
      let () = ppdebug 1 (fun () ->
          str "calling eauto recursively at depth " ++ int (succ depth) ++
          str " on " ++ int i ++ str " subgoals")
      in
      search_tac hints limit (succ depth) info
    in
    fun info ->
    if Int.equal depth (succ limit) then
      let info = Exninfo.reify () in
      Proofview.tclZERO ~info ReachedLimit
    else
      Proofview.tclOR (hints_tac hints info kont)
                      (fun e -> Proofview.tclOR (intro info kont)
                      (fun e' -> let (e, info) = merge_exceptions e e' in
                              Proofview.tclZERO ~info e))

  let search_tac_gl mst only_classes dep hints best_effort depth i sigma gls gl :
        unit Proofview.tactic =
    let open Proofview in
    let dep = dep || Proofview.unifiable sigma (Goal.goal gl) gls in
    let info = make_autogoal mst only_classes dep (cut_of_hints hints)
      best_effort i gl in
    search_tac hints depth 1 info

  let search_tac mst only_classes best_effort dep hints depth =
    let open Proofview in
    let tac sigma gls i =
      Goal.enter
        begin fun gl ->
          search_tac_gl mst only_classes dep hints best_effort depth (succ i) sigma gls gl end
    in
      Proofview.Unsafe.tclGETGOALS >>= fun gls ->
      let gls = CList.map Proofview.drop_state gls in
      Proofview.tclEVARMAP >>= fun sigma ->
      let j = List.length gls in
      search_fixpoint ~best_effort ~allow_out_of_order:true (List.init j (fun i -> tac sigma gls i))

  let fix_iterative t =
    let rec aux depth =
      Proofview.tclOR
        (t depth)
        (function
         | (ReachedLimit,_) -> aux (succ depth)
         | (e,ie) -> Proofview.tclZERO ~info:ie e)
    in aux 1

  let fix_iterative_limit limit t =
    let open Proofview in
    let rec aux depth =
      if Int.equal depth (succ limit)
      then
        let info = Exninfo.reify () in
        tclZERO ~info ReachedLimit
      else tclOR (t depth) (function
          | (ReachedLimit, _) -> aux (succ depth)
          | (e,ie) -> Proofview.tclZERO ~info:ie e)
    in aux 1

  let eauto_tac_stuck mst ?(unique=false)
                ~only_classes
                ~best_effort
                ?strategy ~depth ~dep hints =
    let open Proofview in
    let tac =
      let search = search_tac mst only_classes best_effort dep hints in
      let dfs =
        match strategy with
        | None -> not (get_typeclasses_iterative_deepening ())
        | Some Dfs -> true
        | Some Bfs -> false
      in
      if dfs then
        let depth = match depth with None -> -1 | Some d -> d in
        search depth
      else
        match depth with
        | None -> fix_iterative search
        | Some l -> fix_iterative_limit l search
    in
    let error (e, info) =
      match e with
      | ReachedLimit ->
        Tacticals.tclFAIL ~info (str"Proof search reached its limit")
      | NoApplicableHint ->
        Tacticals.tclFAIL ~info (str"Proof search failed" ++
                                    (if Option.is_empty depth then mt()
                                     else str" without reaching its limit"))
      | Proofview.MoreThanOneSuccess ->
        Tacticals.tclFAIL ~info (str"Proof search failed: " ++
                                       str"more than one success found")
      | e -> Proofview.tclZERO ~info e
    in
    let tac = Proofview.tclOR tac error in
    let tac =
      if unique then
        Proofview.tclEXACTLY_ONCE Proofview.MoreThanOneSuccess tac
      else tac
    in
    with_shelf numgoals >>= fun (initshelf, i) ->
    let () = ppdebug 1 (fun () ->
        str"Starting resolution with " ++ int i ++
        str" goal(s) under focus and " ++
        int (List.length initshelf) ++ str " shelved goal(s)" ++
        (if only_classes then str " in only_classes mode" else str " in regular mode") ++
        match depth with
        | None -> str ", unbounded"
        | Some i -> str ", with depth limit " ++ int i)
    in
    tac <*> pr_goals (str "after eauto_tac_stuck: ")

  let eauto_tac mst ?unique ~only_classes ~best_effort ?strategy ~depth ~dep hints =
    Hints.wrap_hint_warning @@
      eauto_tac_stuck mst ?unique ~only_classes
          ~best_effort ?strategy ~depth ~dep hints

  let preprocess_goals evm goals =
    let sorted_goals =
      if get_typeclasses_dependency_order () then
        top_sort evm goals
      else Evar.Set.elements goals
    in
    let evm = Evd.set_typeclass_evars evm Evar.Set.empty in
    let evm = Evd.push_future_goals evm in
    evm, sorted_goals


  let run_on_goals env evm tac ~goals =
    let goalsl = List.map Proofview.with_empty_state goals in
    let tac = Proofview.Unsafe.tclNEWGOALS goalsl <*> tac in
    let _, pv = Proofview.init evm [] in
     (* Instance may try to call this before a proof is set up!
       Thus, give_me_the_proof will fail. Beware! *)
    let name, poly =
      (* try
      *   let Proof.{ name; poly } = Proof.data Proof_global.(give_me_the_proof ()) in
      *   name, poly
      * with | Proof_global.NoCurrentProof -> *)
       Id.of_string "instance", false
    in
    let tac =
      if get_debug () > 1 then Proofview.Trace.record_info_trace tac
      else tac
    in
    let (), pv', unsafe, info =
      try Proofview.apply ~name ~poly env tac pv
      with Logic_monad.TacticFailure _ -> raise Not_found
    in
    let () =
      ppdebug 1 (fun () ->
          str"The tactic trace is: " ++ hov 0 (Proofview.Trace.pr_info env evm ~lvl:1 info))
    in
    let finished = Proofview.finished pv' in
    let evm' = Proofview.return pv' in
    (finished, evm')

  let post_process_goals ~goals ~nongoals ~sigma ~finished =
    let _, sigma = Evd.pop_future_goals sigma in
    let tc_evars = Evd.get_typeclass_evars sigma in
    let () = ppdebug 1 (fun () ->
        str"Finished resolution with " ++ str(if finished then "a complete" else "an incomplete") ++
        str" solution." ++ fnl()  ++
        str"Old typeclass evars not concerned by this resolution = " ++
        hov 0 (prlist_with_sep spc (pr_ev_with_id sigma)
                 (Evar.Set.elements tc_evars)) ++ fnl() ++
        str"Shelf = " ++
        hov 0 (prlist_with_sep spc (pr_ev_with_id sigma)
                 (Evar.Set.elements tc_evars)))
    in
    let nongoals =
      Evar.Set.fold (fun ev acc -> match Evarutil.advance sigma ev with
          | Some ev -> Evar.Set.add ev acc
          | None -> acc) (Evar.Set.union goals nongoals) tc_evars
    in
    let sigma = Evd.set_typeclass_evars sigma nongoals in
    let () = ppdebug 1 (fun () ->
        str"New typeclass evars are: " ++
        hov 0 (prlist_with_sep spc (pr_ev_with_id sigma) (Evar.Set.elements nongoals)))
    in
    sigma


  (** Typeclasses eauto is an eauto which tries to resolve only
      goals of typeclass type, and assumes that the initially selected
      evars in evd are independent of the rest of the evars *)
  let typeclasses_eauto env evd ~goals ?depth ~unique ~best_effort st hints =
    let only_classes = true in
    let dep = unique in
    NewProfile.profile "typeclass search" (fun () ->
      run_on_goals env evd (eauto_tac_stuck st ~unique ~only_classes ~best_effort ~depth ~dep hints) ~goals) ()

  let typeclasses_resolve : solver = { solver = fun env evd ~depth ~unique ~best_effort ~goals ->
    let db = searchtable_map typeclasses_db in
    let st = Hint_db.transparent_state db in
    let modes = Hint_db.modes db in
    typeclasses_eauto env evd ~goals ?depth ~best_effort ~unique (modes,st) [db]
  }
end

let typeclasses_eauto ?(only_classes=false)
  ?(best_effort=false)
  ?(st=TransparentState.full)
                      ?strategy ~depth dbs =
  let dbs = List.map_filter
              (fun db -> try Some (searchtable_map db)
                      with e when CErrors.noncritical e -> None)
              dbs
  in
  let st = match dbs with x :: _ -> Hint_db.transparent_state x | _ -> st in
  let modes = List.map Hint_db.modes dbs in
  let modes = List.fold_left Modes.union Modes.empty modes in
  let depth = match depth with None -> get_typeclasses_depth () | Some l -> Some l in
  Proofview.tclIGNORE
    (Search.eauto_tac (modes,st) ~only_classes ?strategy
      ~best_effort ~depth ~dep:true dbs)
    (* Stuck goals can remain here, we could shelve them, but this way
       the user can use `solve [typeclasses eauto]` to  check there are
       no stuck goals remaining, or use [typeclasses eauto; shelve] himself. *)

(** We compute dependencies via a union-find algorithm.
    Beware of the imperative effects on the partition structure,
    it should not be shared, but only used locally. *)

let deps_of_constraints cstrs evm p =
  List.iter (fun (_, _, x, y) ->
    let evx = Evarutil.undefined_evars_of_term evm x in
    let evy = Evarutil.undefined_evars_of_term evm y in
    Intpart.union_set (Evar.Set.union evx evy) p)
    cstrs

let evar_dependencies pred evm p =
  let cache = Evarutil.create_undefined_evars_cache () in
  Evd.fold_undefined
    (fun ev evi _ ->
      if Evd.is_typeclass_evar evm ev && pred evm ev evi then
        let evars = Evar.Set.add ev (Evarutil.filtered_undefined_evars_of_evar_info ~cache evm evi)
        in Intpart.union_set evars p
      else ())
    evm ()

(** [split_evars] returns groups of undefined evars according to dependencies *)

let split_evars pred env evm =
  let p = Intpart.create () in
  evar_dependencies pred evm p;
  deps_of_constraints (snd (extract_all_conv_pbs evm)) evm p;
  let part = Intpart.partition p in
  let is_strictly_unique ev =
    let evi = Evd.find_undefined evm ev in
    let concl = Evd.evar_concl evi in
    match Typeclasses.class_of_constr env evm concl with
    | None -> false
    | Some (_, ((cl, _), _)) ->
      cl.cl_strict && cl.cl_unique
  in
  let fn evs =
    let (strictly_uniques, rest) = Evar.Set.partition is_strictly_unique evs in
    List.rev_append (List.rev_map Evar.Set.singleton (Evar.Set.elements strictly_uniques)) [rest]
  in
  List.concat_map fn part

let is_inference_forced p evd ev =
  try
    if Evar.Set.mem ev (Evd.get_typeclass_evars evd) && p ev
    then
      let (loc, k) = evar_source (Evd.find_undefined evd ev) in
      match k with
        | Evar_kinds.ImplicitArg (_, _, b) -> b
        | Evar_kinds.QuestionMark _ -> false
        | _ -> true
    else true
  with Not_found -> assert false

let is_mandatory p comp evd =
  Evar.Set.exists (is_inference_forced p evd) comp

(** Check if an evar is concerned by the current resolution attempt,
    (and in particular is in the current component).
    Invariant : this should only be applied to undefined evars. *)

let select_and_update_evars p oevd in_comp evd ev =
  try
    if Evd.is_typeclass_evar oevd ev then
      (in_comp ev && p evd ev (Evd.find_undefined evd ev))
    else false
  with Not_found -> false

(** Do we still have unresolved evars that should be resolved ? *)

let has_undefined p oevd evd =
  let check ev evi = p oevd ev in
  Evar.Map.exists check (Evd.undefined_map evd)
let find_undefined p oevd evd =
  let check ev evi = p oevd ev in
  Evar.Map.domain (Evar.Map.filter check (Evd.undefined_map evd))

exception Unresolved of evar_map

type condition = Environ.env -> evar_map -> Evar.Set.t -> bool

type tc_solver = solver * condition

let class_solvers = ref (CString.Map.empty : tc_solver CString.Map.t)

let register_solver ~name ?(override=false) h =
  if not override && CString.Map.mem name !class_solvers then
    CErrors.anomaly ~label:"Class_tactics.register_solver"
      Pp.(str (Printf.sprintf {|Solver "%s" is already registered|} name));
  class_solvers := CString.Map.add name h !class_solvers

let active_solvers = Summary.ref ~name:"typeclass_solvers" ([] : string list)

let deactivate_solver ~name =
  active_solvers := List.filter (fun s -> not (String.equal s name)) !active_solvers

let activate_solver ~name =
  assert (CString.Map.mem name !class_solvers);
  deactivate_solver ~name;
  active_solvers := name :: !active_solvers

let find_solver env evd (s : Intpart.set) =
  let rec find_solver = function
    | [] -> Search.typeclasses_resolve
    | hd :: tl ->
      try
        let (solver,cond) = CString.Map.find hd !class_solvers in
        if cond env evd s then solver else find_solver tl
      with Not_found ->  find_solver tl in
  find_solver !active_solvers

(** If [do_split] is [true], we try to separate the problem in
    several components and then solve them separately *)
let resolve_all_evars depth unique env p oevd fail =
  let () =
    ppdebug 0 (fun () ->
        str"Calling typeclass resolution with flags: "++
        str"depth = " ++ (match depth with None -> str "∞" | Some d -> int d) ++ str"," ++
        str"unique = " ++ bool unique ++ str"," ++
        str"fail = " ++ bool fail);
    ppdebug 2 (fun () ->
        str"Initial evar map: " ++
        Termops.pr_evar_map ~with_univs:!Detyping.print_universes None env oevd)
  in
  let split = split_evars p env oevd in
  let in_comp comp ev = Evar.Set.mem ev comp in
  let rec docomp evd = function
    | [] ->
      let () = ppdebug 2 (fun () ->
          str"Final evar map: " ++
          Termops.pr_evar_map ~with_univs:!Detyping.print_universes None env evd)
      in
      evd
    | comp :: comps ->
      let p = select_and_update_evars p oevd (in_comp comp) in
      try
        (try
          (* evars_to_goals p evd gives none when there's no evar having p *)
          match evars_to_goals p evd with
          | Some (goals, nongoals) ->
            let solver = find_solver env evd comp in
            let evd, sorted_goals = Search.preprocess_goals evd goals in
            let finished, evd = solver.solver env evd ~goals:sorted_goals ~best_effort:true ~depth ~unique in
            let evd = Search.post_process_goals ~goals ~nongoals ~sigma:evd ~finished in
            if has_undefined p oevd evd then
              let () = if finished then ppdebug 1 (fun () ->
                  str"Proof is finished but there remain undefined evars: " ++
                  prlist_with_sep spc (pr_ev evd)
                    (Evar.Set.elements (find_undefined p oevd evd)))
              in
              raise (Unresolved evd)
            else docomp evd comps
          | None -> docomp evd comps (* No typeclass evars left in this component *)
        with Not_found ->
          (* Typeclass resolution failed *)
          raise (Unresolved evd))
      with Unresolved evd' ->
        if fail && is_mandatory (p evd') comp evd'
        then (* Unable to satisfy the constraints. *)
          error_unresolvable env evd' comp
        else (* Best effort: use the best found solution on this component *)
          docomp evd' comps
  in docomp oevd split

let initial_select_evars filter =
  fun evd ev evi ->
    filter ev (Lazy.from_val (snd (Evd.evar_source evi))) &&
    (* Typeclass evars can contain evars whose conclusion is not
       yet determined to be a class or not. *)
    Typeclasses.is_class_evar evd evi


let classes_transparent_state () =
  try Hint_db.transparent_state (searchtable_map typeclasses_db)
  with Not_found -> TransparentState.empty

let resolve_typeclass_evars depth unique env evd filter fail =
  let evd =
    try Evarconv.solve_unif_constraints_with_heuristics
      ~flags:(Evarconv.default_flags_of (classes_transparent_state())) env evd
    with e when CErrors.noncritical e -> evd
  in
    resolve_all_evars depth unique env
      (initial_select_evars filter) evd fail

let solve_inst env evd filter unique fail =
  let ((), sigma) = Hints.wrap_hint_warning_fun env evd begin fun evd ->
    (), resolve_typeclass_evars
    (get_typeclasses_depth ())
    unique env evd filter fail
  end in
  sigma

let () =
  Typeclasses.set_solve_all_instances solve_inst

let resolve_one_typeclass env sigma concl =
  let (term, sigma) = Hints.wrap_hint_warning_fun env sigma begin fun sigma ->
  let hints = searchtable_map typeclasses_db in
  let st = Hint_db.transparent_state hints in
  let modes = Hint_db.modes hints in
  let depth = get_typeclasses_depth () in
  let tac = Tacticals.tclCOMPLETE (Search.eauto_tac (modes,st)
      ~only_classes:true ~best_effort:false
      ~depth [hints] ~dep:true)
  in
  let entry, pv = Proofview.init sigma [env, concl] in
  let pv =
    let name = Names.Id.of_string "legacy_pe" in
    match Proofview.apply ~name ~poly:false (Global.env ()) tac pv with
    | (_, final, _, _) -> final
    | exception (Logic_monad.TacticFailure (Tacticals.FailError _)) ->
      raise Not_found
  in
  let evd = Proofview.return pv in
  let term = match Proofview.partial_proof entry pv with [t] -> t | _ -> assert false in
  term, evd
  end in
  (sigma, term)

let () = (Typeclasses.set_solve_one_instance[@warning "-3"]) resolve_one_typeclass

(** Take the head of the arity of a constr.
    Used in the partial application tactic. *)

let rec head_of_constr sigma t =
  let t = strip_outer_cast sigma t in
    match EConstr.kind sigma t with
    | Prod (_,_,c2)  -> head_of_constr sigma c2
    | LetIn (_,_,_,c2) -> head_of_constr sigma c2
    | App (f,args)  -> head_of_constr sigma f
    | _      -> t

let head_of_constr h c =
  Proofview.tclEVARMAP >>= fun sigma ->
  let c = head_of_constr sigma c in
  letin_tac None (Name h) c None Locusops.allHyps

let not_evar c =
  Proofview.tclEVARMAP >>= fun sigma ->
  match EConstr.kind sigma c with
  | Evar _ -> Tacticals.tclFAIL (str"Evar")
  | _ -> Proofview.tclUNIT ()

let is_ground c =
  let open Tacticals in
  Proofview.tclEVARMAP >>= fun sigma ->
  if Evarutil.is_ground_term sigma c then tclIDTAC
  else tclFAIL (str"Not ground")

let autoapply c i =
  let open Proofview.Notations in
  Hints.wrap_hint_warning @@
  Proofview.Goal.enter begin fun gl ->
  let hintdb = try Hints.searchtable_map i with Not_found ->
    CErrors.user_err (Pp.str ("Unknown hint database " ^ i ^ "."))
  in
  let flags = auto_unif_flags
    (Hints.Hint_db.transparent_state hintdb) in
  let cty = Tacmach.pf_get_type_of gl c in
  let env = Proofview.Goal.env gl in
  let sigma = Proofview.Goal.sigma gl in
  let ce = Clenv.mk_clenv_from env sigma (c,cty) in
  Clenv.res_pf ~with_evars:true ~with_classes:false ~flags ce <*>
      Proofview.tclEVARMAP >>= (fun sigma ->
      let sigma = Typeclasses.make_unresolvables
          (fun ev -> Typeclasses.all_goals ev (Lazy.from_val (snd (Evd.evar_source (Evd.find_undefined sigma ev))))) sigma in
      Proofview.Unsafe.tclEVARS sigma) end

let resolve_tc c =
  let open Proofview.Notations in
  Proofview.tclENV >>= fun env ->
  Proofview.tclEVARMAP >>= fun sigma ->
  let depth = get_typeclasses_depth () in
  let unique = get_typeclasses_unique_solutions () in
  let evars = Evarutil.undefined_evars_of_term sigma c in
  let filter = (fun ev _ -> Evar.Set.mem ev evars) in
  let fail = true in
  let sigma = resolve_all_evars depth unique env (initial_select_evars filter) sigma fail in
  Proofview.Unsafe.tclEVARS sigma
