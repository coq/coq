(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
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
open Clenv
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
let get_typeclasses_depth =
  Goptions.declare_intopt_option_and_ref
    ~depr:false
    ~key:typeclasses_depth_opt_name

let set_typeclasses_depth =
  Goptions.set_int_option_value typeclasses_depth_opt_name

(** When this flag is enabled, the resolution of type classes tries to avoid
    useless introductions. This is no longer useful since we have eta, but is
    here for compatibility purposes. Another compatibility issues is that the
    cost (in terms of search depth) can differ. *)
let get_typeclasses_limit_intros =
  Goptions.declare_bool_option_and_ref
    ~depr:false
    ~key:["Typeclasses";"Limit";"Intros"]
    ~value:true

let get_typeclasses_dependency_order =
  Goptions.declare_bool_option_and_ref
    ~depr:false
    ~key:["Typeclasses";"Dependency";"Order"]
    ~value:false

let iterative_deepening_opt_name = ["Typeclasses";"Iterative";"Deepening"]
let get_typeclasses_iterative_deepening =
  Goptions.declare_bool_option_and_ref
    ~depr:false
    ~key:iterative_deepening_opt_name
    ~value:false

(** [typeclasses_filtered_unif] governs the unification algorithm used by type
    classes. If enabled, a new algorithm based on pattern filtering and refine
    will be used. When disabled, the previous algorithm based on apply will be
    used. *)
let get_typeclasses_filtered_unification =
  Goptions.declare_bool_option_and_ref
    ~depr:true
    ~key:["Typeclasses";"Filtered";"Unification"]
    ~value:false

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
      { optdepr  = false;
        optkey   = ["Typeclasses";"Debug"];
        optread  = get_typeclasses_debug;
        optwrite = set_typeclasses_debug; }

  let () =
    let open Goptions in
    declare_int_option
      { optdepr  = false;
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
  let evi = Evd.find evs ev in
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
  Clenv.unify ~flags t1 <*> exact_no_check c
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
  let clenv = mk_clenv_from_n env sigma diff (c, ty) in
  Clenv.res_pf ~with_evars ~with_classes:false ~flags clenv
  end

(** Application of a lemma using [refine] instead of the old [w_unify] *)
let unify_resolve_refine flags h diff =
  let len = match diff with None -> None | Some (diff, _) -> Some diff in
  Proofview.Goal.enter begin fun gls ->
  let open Clenv in
  let env = Proofview.Goal.env gls in
  let concl = Proofview.Goal.concl gls in
  Refine.refine ~typecheck:false begin fun sigma ->
    let sigma, term = Hints.fresh_hint env sigma h in
    let ty = Retyping.get_type_of env sigma term in
    let sigma, cl = Clenv.make_evar_clause env sigma ?len ty in
    let term = applist (term, List.map (fun x -> x.hole_evar) cl.cl_holes) in
    let flags = Evarconv.default_flags_of flags.core_unify_flags.modulo_delta in
    let sigma = Evarconv.unify_leq_delay ~flags env sigma cl.cl_concl concl in
    (sigma, term)
    end
  end

let unify_resolve_refine flags h diff =
  Proofview.tclORELSE
    (unify_resolve_refine flags h diff)
    (fun (exn,info) ->
      match exn with
      | Evarconv.UnableToUnify _ ->
        Tacticals.tclZEROMSG ~info (str "Unable to unify")
      | e when CErrors.noncritical e ->
        Tacticals.tclZEROMSG ~info (str "Unexpected error")
      | _ ->
        Exninfo.iraise (exn,info))

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

let matches_pattern concl pat =
  let matches env sigma =
    match pat with
    | None -> Proofview.tclUNIT ()
    | Some pat ->
       if Constr_matching.is_matching env sigma pat concl then
         Proofview.tclUNIT ()
       else
         Tacticals.tclZEROMSG (str "pattern does not match")
  in
   Proofview.Goal.enter begin fun gl ->
     let env = Proofview.Goal.env gl in
     let sigma = Proofview.Goal.sigma gl in
       matches env sigma end

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
let rec e_trivial_fail_db only_classes db_list local_db secvars =
  let open Tacticals in
  let open Tacmach in
  let trivial_fail =
    Proofview.Goal.enter
    begin fun gl ->
    let env = Proofview.Goal.env gl in
    let sigma = Tacmach.project gl in
    let d = NamedDecl.get_id @@ pf_last_hyp gl in
    let hints = push_resolve_hyp env sigma d local_db in
      e_trivial_fail_db only_classes db_list hints secvars
      end
  in
  let trivial_resolve =
    Proofview.Goal.enter
    begin fun gl ->
    let tacs = e_trivial_resolve db_list local_db secvars only_classes
                                 (pf_env gl) (project gl) (pf_concl gl) in
      tclFIRST (List.map (fun (x,_,_,_,_) -> x) tacs)
    end
  in
  let tacl =
    Eauto.e_assumption ::
    (tclTHEN Tactics.intro trivial_fail :: [trivial_resolve])
  in
  tclSOLVE tacl

and e_my_find_search db_list local_db secvars hdc complete only_classes env sigma concl0 =
  let open Proofview.Notations in
  let prods, concl = EConstr.decompose_prod_assum sigma concl0 in
  let nprods = List.length prods in
  let allowed_evars =
    try
      match hdc with
      | Some (hd,_) when only_classes ->
         let cl = Typeclasses.class_info env sigma hd in
         if cl.cl_strict then
          let undefined = lazy (Evarutil.undefined_evars_of_term sigma concl) in
          let allowed evk = not (Evar.Set.mem evk (Lazy.force undefined)) in
          Evarsolve.AllowedEvars.from_pred allowed
         else Evarsolve.AllowedEvars.all
      | _ -> Evarsolve.AllowedEvars.all
    with e when CErrors.noncritical e -> Evarsolve.AllowedEvars.all
  in
  let tac_of_hint =
    fun (flags, h) ->
      let p = FullHint.pattern h in
      let name = FullHint.name h in
      let tac = function
        | Res_pf h ->
           if get_typeclasses_filtered_unification () then
             let tac =
               with_prods nprods h
                          (fun diff ->
                             matches_pattern concl p <*>
                               unify_resolve_refine flags h diff)
             in Tacticals.tclTHEN tac Proofview.shelve_unifiable
           else
             let tac =
               with_prods nprods h (unify_resolve ~with_evars:false flags h) in
               Proofview.tclBIND (Proofview.with_shelf tac)
                  (fun (gls, ()) -> shelve_dependencies gls)
        | ERes_pf h ->
           if get_typeclasses_filtered_unification () then
             let tac = (with_prods nprods h
                  (fun diff ->
                             matches_pattern concl p <*>
                             unify_resolve_refine flags h diff)) in
             Tacticals.tclTHEN tac Proofview.shelve_unifiable
           else
             let tac =
               with_prods nprods h (unify_resolve ~with_evars:true flags h) in
               Proofview.tclBIND (Proofview.with_shelf tac)
                  (fun (gls, ()) -> shelve_dependencies gls)
        | Give_exact h ->
           if get_typeclasses_filtered_unification () then
             let tac =
               matches_pattern concl p <*>
                 Proofview.Goal.enter
                   (fun gl -> unify_resolve_refine flags h None) in
             Tacticals.tclTHEN tac Proofview.shelve_unifiable
           else
             e_give_exact flags h
      | Res_pf_THEN_trivial_fail h ->
         let fst = with_prods nprods h (unify_resolve ~with_evars:true flags h) in
         let snd = if complete then Tacticals.tclIDTAC
                   else e_trivial_fail_db only_classes db_list local_db secvars in
         Tacticals.tclTHEN fst snd
      | Unfold_nth c ->
         Proofview.tclPROGRESS (unfold_in_concl [AllOccurrences,c])
      | Extern (p, tacast) -> conclPattern concl0 p tacast
      in
      let tac = FullHint.run h tac in
      let tac = if complete then Tacticals.tclCOMPLETE tac else tac in
      let pp() =
        match p with
        | Some pat when get_typeclasses_filtered_unification () ->
           str " with pattern " ++ Printer.pr_constr_pattern_env env sigma pat
        | _ -> mt ()
      in
      let extern = match FullHint.repr h with
        | Extern _ -> true
        | _ -> false
      in
      (tac, FullHint.priority h, extern, name, lazy (FullHint.print env sigma h ++ pp ()))
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

and e_trivial_resolve db_list local_db secvars only_classes env sigma concl =
  let hd = try Some (decompose_app_bound sigma concl) with Bound -> None in
  try
    (match e_my_find_search db_list local_db secvars hd true only_classes env sigma concl with
    | Some (_,l) -> l
    | None -> [])
  with Not_found -> []

let e_possible_resolve db_list local_db secvars only_classes env sigma concl =
  let hd = try Some (decompose_app_bound sigma concl) with Bound -> None in
  try
    e_my_find_search db_list local_db secvars hd false only_classes env sigma concl
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
  let rec visit ev evi =
    let evs = Evarutil.undefined_evars_of_evar_info evm evi in
      tosee := Evar.Set.remove ev !tosee;
      Evar.Set.iter (fun ev ->
        if Evar.Set.mem ev !tosee then
          visit ev (Evd.find evm ev)) evs;
      l' := ev :: !l';
  in
    while not (Evar.Set.is_empty !tosee) do
      let ev = Evar.Set.choose !tosee in
        visit ev (Evd.find evm ev)
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
  let cty = Evarutil.nf_evar sigma (NamedDecl.get_type decl) in
  let rec iscl env ty =
    let ctx, ar = decompose_prod_assum sigma ty in
      match EConstr.kind sigma (fst (decompose_app sigma ar)) with
      | Const (c,_) -> is_class (GlobRef.ConstRef c)
      | Ind (i,_) -> is_class (GlobRef.IndRef i)
      | _ ->
          let env' = push_rel_context ctx env in
          let ty' = Reductionops.whd_all env' sigma ar in
               if not (EConstr.eq_constr sigma ty' ar) then iscl env' ty'
               else false
  in
  let is_class = iscl env cty in
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
      (DirPath.empty, true, Context.Named.empty, GlobRef.Map.empty,
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
           Context.Named.equal eq sign sign' &&
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
      If the type class is unique or in Prop
      and there are no evars in the goal then we do
      NOT backtrack. *)
  let needs_backtrack env evd unique concl =
    if unique || is_Prop env evd concl then
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

  let _ = CErrors.register_handler begin function
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
          | Fail (e, info) ->
            let () = ppdebug 1 (fun () ->
                str "Goal " ++ int glid ++ str" has no more solutions, returning exception: "
                ++ CErrors.iprint (e, info))
            in
            fk (e, info)
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
    let unique = not info.search_dep || is_unique env sigma concl in
    let backtrack = needs_backtrack env sigma unique concl in
    let () = ppdebug 0 (fun () ->
        pr_depth info.search_depth ++ str": looking for " ++
        Printer.pr_econstr_env (Goal.env gl) sigma concl ++
        (if backtrack then str" with backtracking"
         else str" without backtracking"))
    in
    let secvars = compute_secvars gl in
    match e_possible_resolve hints info.search_hints secvars
            info.search_only_classes env sigma concl with
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
      let derivs = path_derivate info.search_cut name in
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
            let msg =
              match fst ie with
              | Pretype_errors.PretypeError (env, evd, Pretype_errors.CannotUnify (x,y,_)) ->
                str"Cannot unify " ++
                Printer.pr_econstr_env env evd x ++ str" and " ++
                Printer.pr_econstr_env env evd y
              | ReachedLimit -> str "Proof-search reached its limit."
              | NoApplicableHint -> str "Proof-search failed."
              | StuckGoal | NonStuckFailure -> str "Proof-search got stuck."
              | e -> CErrors.iprint ie
            in
            (header ++ str " failed with: " ++ msg))
      in
      let tac_of gls i j = Goal.enter begin fun gl' ->
        let sigma' = Goal.sigma gl' in
        let () = ppdebug 0 (fun () ->
            pr_depth (succ j :: i :: info.search_depth) ++ str" : " ++
            pr_ev sigma' (Proofview.Goal.goal gl'))
        in
        let eq c1 c2 = EConstr.eq_constr sigma' c1 c2 in
        let hints' =
          if b && not (Context.Named.equal eq (Goal.hyps gl') (Goal.hyps gl))
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
      if path_matches derivs [] then aux e tl
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
      (eauto_tac_stuck mst ?unique ~only_classes
          ~best_effort ?strategy ~depth ~dep hints)

  let run_on_goals env evm p tac goals nongoals =
    let goalsl =
      if get_typeclasses_dependency_order () then
        top_sort evm goals
      else Evar.Set.elements goals
    in
    let goalsl = List.map Proofview.with_empty_state goalsl in
    let tac = Proofview.Unsafe.tclNEWGOALS goalsl <*> tac in
    let evm = Evd.set_typeclass_evars evm Evar.Set.empty in
    let evm = Evd.push_future_goals evm in
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
    let shelf = Evd.shelf evm' in
    assert(Evd.fold_undefined (fun ev _ acc ->
        let okev = Evd.mem evm ev || List.mem ev shelf in
          if not okev then
            Feedback.msg_debug
              (str "leaking evar " ++ int (Evar.repr ev) ++
                  spc () ++ pr_ev_with_id evm' ev);
          acc && okev) evm' true);
    let _, evm' = Evd.pop_future_goals evm' in
    let () = ppdebug 1 (fun () ->
        str"Finished resolution with " ++ str(if finished then "a complete" else "an incomplete") ++
        str" solution." ++ fnl()  ++
        str"Old typeclass evars not concerned by this resolution = " ++
        hov 0 (prlist_with_sep spc (pr_ev_with_id evm')
                 (Evar.Set.elements (Evd.get_typeclass_evars evm'))) ++ fnl() ++
        str"Shelf = " ++
        hov 0 (prlist_with_sep spc (pr_ev_with_id evm')
                 (Evar.Set.elements (Evd.get_typeclass_evars evm'))))
    in
    let nongoals' =
      Evar.Set.fold (fun ev acc -> match Evarutil.advance evm' ev with
          | Some ev' -> Evar.Set.add ev acc
          | None -> acc) (Evar.Set.union goals nongoals) (Evd.get_typeclass_evars evm')
    in
    let evm' = evars_reset_evd ~with_conv_pbs:true ~with_univs:false evm' evm in
    let evm' = Evd.set_typeclass_evars evm' nongoals' in
    let () = ppdebug 1 (fun () ->
        str"New typeclass evars are: " ++
        hov 0 (prlist_with_sep spc (pr_ev_with_id evm') (Evar.Set.elements nongoals')))
    in
    Some (finished, evm')

  let run_on_evars env evm p tac =
    match evars_to_goals p evm with
    | None -> None (* This happens only because there's no evar having p *)
    | Some (goals, nongoals) ->
      run_on_goals env evm p tac goals nongoals
  let evars_eauto env evd depth only_classes ~best_effort unique dep mst hints p =
    let eauto_tac = eauto_tac_stuck mst ~unique ~only_classes
      ~best_effort
      ~depth ~dep:(unique || dep) hints in
    run_on_evars env evd p eauto_tac

  let typeclasses_eauto env evd ?depth unique ~best_effort st hints p =
    evars_eauto env evd depth true ~best_effort unique false st hints p
  (** Typeclasses eauto is an eauto which tries to resolve only
      goals of typeclass type, and assumes that the initially selected
      evars in evd are independent of the rest of the evars *)

  let typeclasses_resolve env evd depth unique ~best_effort p =
    let db = searchtable_map typeclasses_db in
    let st = Hint_db.transparent_state db in
    let modes = Hint_db.modes db in
    typeclasses_eauto env evd ?depth ~best_effort unique (modes,st) [db] p
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
  let modes = List.fold_left (GlobRef.Map.union (fun _ m1 m2 -> Some (m1@m2))) GlobRef.Map.empty modes in
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

module Intpart = Unionfind.Make(Evar.Set)(Evar.Map)

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

let split_evars pred evm =
  let p = Intpart.create () in
  evar_dependencies pred evm p;
  deps_of_constraints (snd (extract_all_conv_pbs evm)) evm p;
  Intpart.partition p

let is_inference_forced p evd ev =
  try
    if Evar.Set.mem ev (Evd.get_typeclass_evars evd) && p ev
    then
      let (loc, k) = evar_source ev evd in
      match k with
        | Evar_kinds.ImplicitArg (_, _, b) -> b
        | Evar_kinds.QuestionMark _ -> false
        | _ -> true
    else true
  with Not_found -> assert false

let is_mandatory p comp evd =
  Evar.Set.exists (is_inference_forced p evd) comp

(** In case of unsatisfiable constraints, build a nice error message *)

let error_unresolvable env comp evd =
  let is_part ev = match comp with
  | None -> true
  | Some s -> Evar.Set.mem ev s
  in
  let fold ev evi (found, accu) =
    let ev_class = class_of_constr env evd evi.evar_concl in
    if not (Option.is_empty ev_class) && is_part ev then
      (* focus on one instance if only one was searched for *)
      if not found then (true, Some ev)
      else (found, None)
    else (found, accu)
   in
  let (_, ev) = Evd.fold_undefined fold evd (true, None) in
  Pretype_errors.unsatisfiable_constraints env evd ev comp

(** Check if an evar is concerned by the current resolution attempt,
    (and in particular is in the current component).
    Invariant : this should only be applied to undefined evars. *)

let select_and_update_evars p oevd in_comp evd ev =
  try
    if Evd.is_typeclass_evar oevd ev then
      (in_comp ev && p evd ev (Evd.find evd ev))
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

(** If [do_split] is [true], we try to separate the problem in
    several components and then solve them separately *)
let resolve_all_evars depth unique env p oevd do_split fail =
  let () =
    ppdebug 0 (fun () ->
        str"Calling typeclass resolution with flags: "++
        str"depth = " ++ (match depth with None -> str "∞" | Some d -> int d) ++ str"," ++
        str"unique = " ++ bool unique ++ str"," ++
        str"do_split = " ++ bool do_split ++ str"," ++
        str"fail = " ++ bool fail);
    ppdebug 2 (fun () ->
        str"Initial evar map: " ++
        Termops.pr_evar_map ~with_univs:!Detyping.print_universes None env oevd)
  in
  let tcs = Evd.get_typeclass_evars oevd in
  let split = if do_split then split_evars p oevd else [tcs] in
  let in_comp comp ev = if do_split then Evar.Set.mem ev comp else true in
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
          let res = Search.typeclasses_resolve env evd depth
            ~best_effort:true unique p in
          match res with
          | Some (finished, evd') ->
            if has_undefined p oevd evd' then
              let () = if finished then ppdebug 1 (fun () ->
                  str"Proof is finished but there remain undefined evars: " ++
                  prlist_with_sep spc (pr_ev evd')
                    (Evar.Set.elements (find_undefined p oevd evd')))
              in
              raise (Unresolved evd')
            else docomp evd' comps
          | None -> docomp evd comps (* No typeclass evars left in this component *)
        with Not_found ->
          (* Typeclass resolution failed *)
          raise (Unresolved evd))
      with Unresolved evd' ->
        if fail && (not do_split || is_mandatory (p evd') comp evd')
        then (* Unable to satisfy the constraints. *)
          let comp = if do_split then Some comp else None in
          error_unresolvable env comp evd'
        else (* Best effort: use the best found solution on this component *)
          docomp evd' comps
  in docomp oevd split

let initial_select_evars filter =
  fun evd ev evi ->
    filter ev (Lazy.from_val (snd evi.Evd.evar_source)) &&
    (* Typeclass evars can contain evars whose conclusion is not
       yet determined to be a class or not. *)
    Typeclasses.is_class_evar evd evi


let classes_transparent_state () =
  try Hint_db.transparent_state (searchtable_map typeclasses_db)
  with Not_found -> TransparentState.empty

let resolve_typeclass_evars depth unique env evd filter split fail =
  let evd =
    try Evarconv.solve_unif_constraints_with_heuristics
      ~flags:(Evarconv.default_flags_of (classes_transparent_state())) env evd
    with e when CErrors.noncritical e -> evd
  in
    resolve_all_evars depth unique env
                      (initial_select_evars filter) evd split fail

let solve_inst env evd filter unique split fail =
  let ((), sigma) = Hints.wrap_hint_warning_fun env evd begin fun evd ->
    (), resolve_typeclass_evars
    (get_typeclasses_depth ())
    unique env evd filter split fail
  end in
  sigma

let () =
  Hook.set Typeclasses.solve_all_instances_hook solve_inst

let resolve_one_typeclass env ?(sigma=Evd.from_env env) concl unique =
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

let () =
  Hook.set Typeclasses.solve_one_instance_hook
    (fun x y z w -> resolve_one_typeclass x ~sigma:y z w)

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
  let ce = mk_clenv_from env sigma (c,cty) in
  Clenv.res_pf ~with_evars:true ~with_classes:false ~flags ce <*>
      Proofview.tclEVARMAP >>= (fun sigma ->
      let sigma = Typeclasses.make_unresolvables
          (fun ev -> Typeclasses.all_goals ev (Lazy.from_val (snd (Evd.find sigma ev).evar_source))) sigma in
      Proofview.Unsafe.tclEVARS sigma) end
