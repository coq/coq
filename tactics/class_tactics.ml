(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* TODO:
  - Find an interface allowing eauto to backtrack when shelved goals remain,
   e.g. to force instantiations.
 *)

open Pp
open CErrors
open Util
open Names
open Term
open Constr
open Termops
open EConstr
open Tacmach
open Tactics
open Clenv
open Typeclasses
open Globnames
open Evd
open Locus
open Proofview.Notations
open Hints

module NamedDecl = Context.Named.Declaration

(** Hint database named "typeclass_instances", now created directly in Auto *)

(** Options handling *)

let typeclasses_debug = ref 0
let typeclasses_depth = ref None

(** When this flag is enabled, the resolution of type classes tries to avoid
    useless introductions. This is no longer useful since we have eta, but is
    here for compatibility purposes. Another compatibility issues is that the
    cost (in terms of search depth) can differ. *)
let typeclasses_limit_intros = ref true
let set_typeclasses_limit_intros d = (:=) typeclasses_limit_intros d
let get_typeclasses_limit_intros () = !typeclasses_limit_intros

let typeclasses_dependency_order = ref false
let set_typeclasses_dependency_order d = (:=) typeclasses_dependency_order d
let get_typeclasses_dependency_order () = !typeclasses_dependency_order

let typeclasses_iterative_deepening = ref false
let set_typeclasses_iterative_deepening d = (:=) typeclasses_iterative_deepening d
let get_typeclasses_iterative_deepening () = !typeclasses_iterative_deepening

(** [typeclasses_filtered_unif] governs the unification algorithm used by type
    classes. If enabled, a new algorithm based on pattern filtering and refine
    will be used. When disabled, the previous algorithm based on apply will be
    used. *)
let typeclasses_filtered_unification = ref false
let set_typeclasses_filtered_unification d =
  (:=) typeclasses_filtered_unification d
let get_typeclasses_filtered_unification () =
  !typeclasses_filtered_unification

let set_typeclasses_debug d = (:=) typeclasses_debug (if d then 1 else 0)
let get_typeclasses_debug () = if !typeclasses_debug > 0 then true else false

let set_typeclasses_verbose =
  function None -> typeclasses_debug := 0
         | Some n -> (:=) typeclasses_debug n
let get_typeclasses_verbose () =
  if !typeclasses_debug = 0 then None else Some !typeclasses_debug

let set_typeclasses_depth d = (:=) typeclasses_depth d
let get_typeclasses_depth () = !typeclasses_depth

open Goptions

let _ =
  declare_bool_option
    { optdepr  = false;
      optname  = "do typeclass search avoiding eta-expansions " ^
                   " in proof terms (expensive)";
      optkey   = ["Typeclasses";"Limit";"Intros"];
      optread  = get_typeclasses_limit_intros;
      optwrite = set_typeclasses_limit_intros; }

let _ =
  declare_bool_option
    { optdepr  = false;
      optname  = "during typeclass resolution, solve instances according to their dependency order";
      optkey   = ["Typeclasses";"Dependency";"Order"];
      optread  = get_typeclasses_dependency_order;
      optwrite = set_typeclasses_dependency_order; }

let _ =
  declare_bool_option
    { optdepr  = false;
      optname  = "use iterative deepening strategy";
      optkey   = ["Typeclasses";"Iterative";"Deepening"];
      optread  = get_typeclasses_iterative_deepening;
      optwrite = set_typeclasses_iterative_deepening; }

let _ =
  declare_bool_option
    { optdepr  = false;
      optname  = "compat";
      optkey   = ["Typeclasses";"Filtered";"Unification"];
      optread  = get_typeclasses_filtered_unification;
      optwrite = set_typeclasses_filtered_unification; }

let set_typeclasses_debug =
  declare_bool_option
    { optdepr  = false;
      optname  = "debug output for typeclasses proof search";
      optkey   = ["Typeclasses";"Debug"];
      optread  = get_typeclasses_debug;
      optwrite = set_typeclasses_debug; }

let _ =
  declare_bool_option
    { optdepr  = false;
      optname  = "debug output for typeclasses proof search";
      optkey   = ["Debug";"Typeclasses"];
      optread  = get_typeclasses_debug;
      optwrite = set_typeclasses_debug; }

let _ =
  declare_int_option
    { optdepr  = false;
      optname  = "verbosity of debug output for typeclasses proof search";
      optkey   = ["Typeclasses";"Debug";"Verbosity"];
      optread  = get_typeclasses_verbose;
      optwrite = set_typeclasses_verbose; }

let set_typeclasses_depth =
  declare_int_option
    { optdepr  = false;
      optname  = "depth for typeclasses proof search";
      optkey   = ["Typeclasses";"Depth"];
      optread  = get_typeclasses_depth;
      optwrite = set_typeclasses_depth; }

type search_strategy = Dfs | Bfs

let set_typeclasses_strategy = function
  | Dfs -> set_typeclasses_iterative_deepening false
  | Bfs -> set_typeclasses_iterative_deepening true

let pr_ev evs ev =
  Printer.pr_econstr_env (Goal.V82.env evs ev) evs (Goal.V82.concl evs ev)

(** Typeclasses instance search tactic / eauto *)

open Auto
open Unification

let auto_core_unif_flags st freeze = {
  modulo_conv_on_closed_terms = Some st;
  use_metas_eagerly_in_conv_on_closed_terms = true;
  use_evars_eagerly_in_conv_on_closed_terms = false;
  modulo_delta = st;
  modulo_delta_types = st;
  check_applied_meta_types = false;
  use_pattern_unification = true;
  use_meta_bound_pattern_unification = true;
  frozen_evars = freeze;
  restrict_conv_on_strict_subterms = false; (* ? *)
  modulo_betaiota = true;
  modulo_eta = false;
}

let auto_unif_flags freeze st =
  let fl = auto_core_unif_flags st freeze in
  { core_unify_flags = fl;
    merge_unify_flags = fl;
    subterm_unify_flags = fl;
    allow_K_in_toplevel_higher_order_unification = false;
    resolve_evars = false
}

let e_give_exact flags poly (c,clenv) =
  let open Tacmach.New in
  Proofview.Goal.enter begin fun gl ->
  let sigma = project gl in
  let (c, _, _) = c in
  let c, sigma =
    if poly then
      let clenv', subst = Clenv.refresh_undefined_univs clenv in
      let evd = evars_reset_evd ~with_conv_pbs:true sigma clenv'.evd in
      let c = Vars.subst_univs_level_constr subst c in
        c, evd
    else c, sigma
  in
  let (sigma, t1) = Typing.type_of (pf_env gl) sigma c in
  Proofview.Unsafe.tclEVARS sigma <*>
  Clenvtac.unify ~flags t1 <*> exact_no_check c
  end

let clenv_unique_resolver_tac with_evars ~flags clenv' =
  Proofview.Goal.enter begin fun gls ->
    let resolve =
      try Proofview.tclUNIT (clenv_unique_resolver ~flags clenv' gls)
      with e -> Proofview.tclZERO e
    in resolve >>= fun clenv' ->
       Clenvtac.clenv_refine ~with_evars ~with_classes:false clenv'
  end

let unify_e_resolve poly flags = begin fun gls (c,_,clenv) ->
  let clenv', c = connect_hint_clenv poly c clenv gls in
  clenv_unique_resolver_tac true ~flags clenv' end

let unify_resolve poly flags = begin fun gls (c,_,clenv) ->
  let clenv', _ = connect_hint_clenv poly c clenv gls in
  clenv_unique_resolver_tac false ~flags clenv'
  end

(** Application of a lemma using [refine] instead of the old [w_unify] *)
let unify_resolve_refine poly flags gls ((c, t, ctx),n,clenv) =
  let open Clenv in
  let env = Proofview.Goal.env gls in
  let concl = Proofview.Goal.concl gls in
  Refine.refine ~typecheck:false begin fun sigma ->
      let sigma, term, ty =
        if poly then
          let (subst, ctx) = UnivGen.fresh_universe_context_set_instance ctx in
          let map c = Vars.subst_univs_level_constr subst c in
          let sigma = Evd.merge_context_set Evd.univ_flexible sigma ctx in
          sigma, map c, map t
        else
          let sigma = Evd.merge_context_set Evd.univ_flexible sigma ctx in
          sigma, c, t
      in
      let sigma', cl = Clenv.make_evar_clause env sigma ?len:n ty in
      let term = applist (term, List.map (fun x -> x.hole_evar) cl.cl_holes) in
      let sigma' =
        Evarconv.the_conv_x_leq env ~ts:flags.core_unify_flags.modulo_delta
                                cl.cl_concl concl sigma'
      in (sigma', term) end

let unify_resolve_refine poly flags gl clenv =
  Proofview.tclORELSE
    (unify_resolve_refine poly flags gl clenv)
    (fun ie ->
      match fst ie with
      | Evarconv.UnableToUnify _ ->
         Tacticals.New.tclZEROMSG (str "Unable to unify")
      | e when CErrors.noncritical e ->
         Tacticals.New.tclZEROMSG (str "Unexpected error")
      | _ -> iraise ie)

(** Dealing with goals of the form A -> B and hints of the form
  C -> A -> B.
*)
let clenv_of_prods poly nprods (c, clenv) gl =
  let (c, _, _) = c in
  if poly || Int.equal nprods 0 then Some (None, clenv)
  else
    let sigma = Tacmach.New.project gl in
    let ty = Retyping.get_type_of (Proofview.Goal.env gl) sigma c in
    let diff = nb_prod sigma ty - nprods in
    if Pervasives.(>=) diff 0 then
      (* Was Some clenv... *)
      Some (Some diff,
            mk_clenv_from_n gl (Some diff) (c,ty))
    else None

let with_prods nprods poly (c, clenv) f =
  if get_typeclasses_limit_intros () then
    Proofview.Goal.enter begin fun gl ->
      try match clenv_of_prods poly nprods (c, clenv) gl with
          | None -> Tacticals.New.tclZEROMSG (str"Not enough premisses")
          | Some (diff, clenv') -> f gl (c, diff, clenv')
      with e when CErrors.noncritical e ->
        Tacticals.New.tclZEROMSG (CErrors.print e) end
  else Proofview.Goal.enter
         begin fun gl ->
         if Int.equal nprods 0 then f gl (c, None, clenv)
         else Tacticals.New.tclZEROMSG (str"Not enough premisses") end

let matches_pattern concl pat =
  let matches env sigma =
    match pat with
    | None -> Proofview.tclUNIT ()
    | Some pat ->
       if Constr_matching.is_matching env sigma pat concl then
         Proofview.tclUNIT ()
       else
         Tacticals.New.tclZEROMSG (str "pattern does not match")
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
  tclEVARMAP >>= fun sigma ->
  (if !typeclasses_debug > 1 && List.length gls > 0 then
     Feedback.msg_debug (str" shelving dependent subgoals: " ++ pr_gls sigma gls);
   shelve_goals gls)

let hintmap_of sigma hdc secvars concl =
  match hdc with
  | None -> fun db -> Hint_db.map_none ~secvars db
  | Some hdc ->
     fun db ->
     if Hint_db.use_dn db then (* Using dnet *)
       Hint_db.map_eauto sigma ~secvars hdc concl db
     else Hint_db.map_existential sigma ~secvars hdc concl db

(** Hack to properly solve dependent evars that are typeclasses *)
let rec e_trivial_fail_db only_classes db_list local_db secvars =
  let open Tacticals.New in
  let open Tacmach.New in
  let trivial_fail =
    Proofview.Goal.enter
    begin fun gl ->
    let env = Proofview.Goal.env gl in
    let sigma = Tacmach.New.project gl in
    let d = pf_last_hyp gl in
    let hintl = make_resolve_hyp env sigma d in
    let hints = Hint_db.add_list env sigma hintl local_db in
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
    Eauto.registered_e_assumption ::
    (tclTHEN Tactics.intro trivial_fail :: [trivial_resolve])
  in
  tclFIRST (List.map tclCOMPLETE tacl)

and e_my_find_search db_list local_db secvars hdc complete only_classes env sigma concl =
  let open Proofview.Notations in
  let prods, concl = EConstr.decompose_prod_assum sigma concl in
  let nprods = List.length prods in
  let freeze =
    try
      match hdc with
      | Some (hd,_) when only_classes ->
         let cl = Typeclasses.class_info hd in
         if cl.cl_strict then
           Evarutil.undefined_evars_of_term sigma concl
         else Evar.Set.empty
      | _ -> Evar.Set.empty
    with e when CErrors.noncritical e -> Evar.Set.empty
  in
  let hint_of_db = hintmap_of sigma hdc secvars concl in
  let hintl =
    List.map_append
      (fun db ->
        let tacs = hint_of_db db in
        let flags = auto_unif_flags freeze (Hint_db.transparent_state db) in
          List.map (fun x -> (flags, x)) tacs)
      (local_db::db_list)
  in
  let tac_of_hint =
    fun (flags, {pri = b; pat = p; poly = poly; code = t; secvars; name = name}) ->
      let tac = function
        | Res_pf (term,cl) ->
           if get_typeclasses_filtered_unification () then
             let tac =
               with_prods nprods poly (term,cl)
                          (fun gl clenv ->
                             matches_pattern concl p <*>
                               unify_resolve_refine poly flags gl clenv)
             in Tacticals.New.tclTHEN tac Proofview.shelve_unifiable
           else
             let tac =
               with_prods nprods poly (term,cl) (unify_resolve poly flags) in
               Proofview.tclBIND (Proofview.with_shelf tac)
                  (fun (gls, ()) -> shelve_dependencies gls)
        | ERes_pf (term,cl) ->
           if get_typeclasses_filtered_unification () then
             let tac = (with_prods nprods poly (term,cl)
                  (fun gl clenv ->
                             matches_pattern concl p <*>
                             unify_resolve_refine poly flags gl clenv)) in
             Tacticals.New.tclTHEN tac Proofview.shelve_unifiable
           else
             let tac =
               with_prods nprods poly (term,cl) (unify_e_resolve poly flags) in
               Proofview.tclBIND (Proofview.with_shelf tac)
                  (fun (gls, ()) -> shelve_dependencies gls)
        | Give_exact (c,clenv) ->
           if get_typeclasses_filtered_unification () then
             let tac =
               matches_pattern concl p <*>
                 Proofview.Goal.nf_enter
                   (fun gl -> unify_resolve_refine poly flags gl (c,None,clenv)) in
             Tacticals.New.tclTHEN tac Proofview.shelve_unifiable
           else
             e_give_exact flags poly (c,clenv)
      | Res_pf_THEN_trivial_fail (term,cl) ->
         let fst = with_prods nprods poly (term,cl) (unify_e_resolve poly flags) in
         let snd = if complete then Tacticals.New.tclIDTAC
                   else e_trivial_fail_db only_classes db_list local_db secvars in
         Tacticals.New.tclTHEN fst snd
      | Unfold_nth c ->
         Proofview.tclPROGRESS (unfold_in_concl [AllOccurrences,c])
      | Extern tacast -> conclPattern concl p tacast
      in
      let tac = run_hint t tac in
      let tac = if complete then Tacticals.New.tclCOMPLETE tac else tac in
      let pp =
        match p with
        | Some pat when get_typeclasses_filtered_unification () ->
           str " with pattern " ++ Printer.pr_constr_pattern_env env sigma pat
        | _ -> mt ()
      in
        match repr_hint t with
        | Extern _ -> (tac, b, true, name, lazy (pr_hint env sigma t ++ pp))
        | _ -> (tac, b, false, name, lazy (pr_hint env sigma t ++ pp))
  in List.map tac_of_hint hintl

and e_trivial_resolve db_list local_db secvars only_classes env sigma concl =
  let hd = try Some (decompose_app_bound sigma concl) with Bound -> None in
  try
    e_my_find_search db_list local_db secvars hd true only_classes env sigma concl
  with Not_found -> []

let e_possible_resolve db_list local_db secvars only_classes env sigma concl =
  let hd = try Some (decompose_app_bound sigma concl) with Bound -> None in
  try
    e_my_find_search db_list local_db secvars hd false only_classes env sigma concl
  with Not_found -> []

let cut_of_hints h =
  List.fold_left (fun cut db -> PathOr (Hint_db.cut db, cut)) PathEmpty h

let catchable = function
  | Refiner.FailError _ -> true
  | e -> Logic.catchable_exception e

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
      tosee := Evar.Map.remove ev !tosee;
      Evar.Set.iter (fun ev ->
        if Evar.Map.mem ev !tosee then
          visit ev (Evar.Map.find ev !tosee)) evs;
      l' := ev :: !l';
  in
    while not (Evar.Map.is_empty !tosee) do
      let ev, evi = Evar.Map.min_binding !tosee in
        visit ev evi
    done;
    List.rev !l'

(** We transform the evars that are concerned by this resolution
    (according to predicate p) into goals.
    Invariant: function p only manipulates and returns undefined evars
*)

let evars_to_goals p evm =
  let goals = ref Evar.Map.empty in
  let map ev evi =
    let evi, goal = p evm ev evi in
    let () = if goal then goals := Evar.Map.add ev evi !goals in
    evi
  in
  let evm = Evd.raw_map_undefined map evm in
  if Evar.Map.is_empty !goals then None
  else Some (!goals, evm)

(** Making local hints  *)
let make_resolve_hyp env sigma st flags only_classes pri decl =
  let id = NamedDecl.get_id decl in
  let cty = Evarutil.nf_evar sigma (NamedDecl.get_type decl) in
  let rec iscl env ty =
    let ctx, ar = decompose_prod_assum sigma ty in
      match EConstr.kind sigma (fst (decompose_app sigma ar)) with
      | Const (c,_) -> is_class (ConstRef c)
      | Ind (i,_) -> is_class (IndRef i)
      | _ ->
          let env' = push_rel_context ctx env in
          let ty' = Reductionops.whd_all env' sigma ar in
               if not (EConstr.eq_constr sigma ty' ar) then iscl env' ty'
               else false
  in
  let is_class = iscl env cty in
  let keep = not only_classes || is_class in
    if keep then
      let c = mkVar id in
      let name = PathHints [VarRef id] in
      let hints =
        if is_class then
          let hints = build_subclasses ~check:false env sigma (VarRef id) empty_hint_info in
            (List.map_append
             (fun (path,info,c) ->
              make_resolves env sigma ~name:(PathHints path)
                  (true,false,not !Flags.quiet) info false
                 (IsConstr (EConstr.of_constr c,Univ.ContextSet.empty)))
               hints)
        else []
      in
        (hints @ List.map_filter
         (fun f -> try Some (f (c, cty, Univ.ContextSet.empty))
           with Failure _ | UserError _ -> None)
         [make_exact_entry ~name env sigma pri false;
          make_apply_entry ~name env sigma flags pri false])
    else []

let make_hints g st only_classes sign =
  let hintlist =
    List.fold_left
      (fun hints hyp ->
        let consider =
          not only_classes ||
          try let t = hyp |> NamedDecl.get_id |> Global.lookup_named |> NamedDecl.get_type in
              (* Section variable, reindex only if the type changed *)
              not (EConstr.eq_constr (project g) (EConstr.of_constr t) (NamedDecl.get_type hyp))
          with Not_found -> true
        in
        if consider then
          let hint =
            pf_apply make_resolve_hyp g st (true,false,false) only_classes empty_hint_info hyp
          in hint @ hints
        else hints)
      ([]) sign
  in Hint_db.add_list (pf_env g) (project g) hintlist (Hint_db.empty st true)

module Search = struct
  type autoinfo =
    { search_depth : int list;
      last_tac : Pp.t Lazy.t;
      search_dep : bool;
      search_only_classes : bool;
      search_cut : hints_path;
      search_hints : hint_db; }

  (** Local hints *)
  let autogoal_cache = Summary.ref ~name:"autogoal_cache"
      (DirPath.empty, true, Context.Named.empty,
       Hint_db.empty full_transparent_state true)

  let make_autogoal_hints only_classes ?(st=full_transparent_state) g =
    let open Proofview in
    let open Tacmach.New in
    let sign = Goal.hyps g in
    let (dir, onlyc, sign', cached_hints) = !autogoal_cache in
    let cwd = Lib.cwd () in
    let eq c1 c2 = EConstr.eq_constr (project g) c1 c2 in
    if DirPath.equal cwd dir &&
         (onlyc == only_classes) &&
           Context.Named.equal eq sign sign' &&
             Hint_db.transparent_state cached_hints == st
    then cached_hints
    else
      let hints = make_hints {it = Goal.goal g; sigma = project g}
                             st only_classes sign
      in
      autogoal_cache := (cwd, only_classes, sign, hints); hints

  let make_autogoal ?(st=full_transparent_state) only_classes dep cut i g =
    let hints = make_autogoal_hints only_classes ~st g in
    { search_hints = hints;
      search_depth = [i]; last_tac = lazy (str"none");
      search_dep = dep;
      search_only_classes = only_classes;
      search_cut = cut }

  (** In the proof engine failures are represented as exceptions *)
  exception ReachedLimitEx
  exception NoApplicableEx

  (** ReachedLimitEx has priority over NoApplicableEx to handle
      iterative deepening: it should fail when no hints are applicable,
      but go to a deeper depth otherwise. *)
  let merge_exceptions e e' =
    match fst e, fst e' with
    | ReachedLimitEx, _ -> e
    | _, ReachedLimitEx -> e'
    | _, _ -> e

  (** Determine if backtracking is needed for this goal.
      If the type class is unique or in Prop
      and there are no evars in the goal then we do
      NOT backtrack. *)
  let needs_backtrack env evd unique concl =
    if unique || is_Prop env evd concl then
      occur_existential evd concl
    else true

  let mark_unresolvables sigma goals =
    List.fold_left
      (fun sigma gl ->
        let evi = Evd.find_undefined sigma gl in
	let evi' = Typeclasses.mark_unresolvable evi in
	Evd.add sigma gl evi')
      sigma goals

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
    if !typeclasses_debug > 0 then
      Feedback.msg_debug
        (pr_depth info.search_depth ++ str": looking for " ++
           Printer.pr_econstr_env (Goal.env gl) sigma concl ++
           (if backtrack then str" with backtracking"
            else str" without backtracking"));
    let secvars = compute_secvars gl in
    let poss =
      e_possible_resolve hints info.search_hints secvars info.search_only_classes env sigma concl in
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
        if !typeclasses_debug > 1 then
          let idx = if fst ie == NoApplicableEx then pred !idx else !idx in
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
            | ReachedLimitEx -> str "Proof-search reached its limit."
            | NoApplicableEx -> str "Proof-search failed."
            | e -> CErrors.iprint ie
          in
          Feedback.msg_debug (header ++ str " failed with: " ++ msg)
        else ()
      in
      let tac_of gls i j = Goal.enter begin fun gl' ->
        let sigma' = Goal.sigma gl' in
        let _concl = Goal.concl gl' in
        if !typeclasses_debug > 0 then
          Feedback.msg_debug
            (pr_depth (succ j :: i :: info.search_depth) ++ str" : " ++
               pr_ev sigma' (Proofview.Goal.goal gl'));
        let eq c1 c2 = EConstr.eq_constr sigma' c1 c2 in
        let hints' =
          if b && not (Context.Named.equal eq (Goal.hyps gl') (Goal.hyps gl))
          then
            let st = Hint_db.transparent_state info.search_hints in
            make_autogoal_hints info.search_only_classes ~st gl'
          else info.search_hints
        in
        let dep' = info.search_dep || Proofview.unifiable sigma' (Goal.goal gl') gls in
        let info' =
          { search_depth = succ j :: i :: info.search_depth;
            last_tac = pp;
            search_dep = dep';
            search_only_classes = info.search_only_classes;
            search_hints = hints';
            search_cut = derivs }
        in kont info' end
      in
      let rec result (shelf, ()) i k =
        foundone := true;
        Proofview.Unsafe.tclGETGOALS >>= fun gls ->
        let gls = CList.map Proofview.drop_state gls in
        let j = List.length gls in
        (if !typeclasses_debug > 0 then
           Feedback.msg_debug
             (pr_depth (i :: info.search_depth) ++ str": " ++ Lazy.force pp
              ++ str" on" ++ spc () ++ pr_ev sigma (Proofview.Goal.goal gl)
              ++ str", " ++ int j ++ str" subgoal(s)" ++
                (Option.cata (fun k -> str " in addition to the first " ++ int k)
                             (mt()) k)));
        let res =
          if j = 0 then tclUNIT ()
          else tclDISPATCH
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
          (if !typeclasses_debug > 1 then
             let prunsolved (ev, _) =
               int (Evar.repr ev) ++ spc () ++ pr_ev sigma ev in
             let unsolved = prlist_with_sep spc prunsolved remaining in
             Feedback.msg_debug
               (pr_depth (i :: info.search_depth) ++
                  str": after " ++ Lazy.force pp ++ str" finished, " ++
                  int (List.length remaining) ++
                  str " goals are shelved and unsolved ( " ++
                  unsolved ++ str")"));
          begin
            (* Some existentials produced by the original tactic were not solved
               in the subgoals, turn them into subgoals now. *)
            let shelved, goals = List.partition (fun (ev, s) -> s) remaining in
            let shelved = List.map fst shelved @ nestedshelf and goals = List.map fst goals in
            if !typeclasses_debug > 1 && not (List.is_empty shelved && List.is_empty goals) then
              Feedback.msg_debug
                (str"Adding shelved subgoals to the search: " ++
                 prlist_with_sep spc (pr_ev sigma) goals ++
		 str" while shelving " ++
		 prlist_with_sep spc (pr_ev sigma) shelved);
            shelve_goals shelved <*>
              (if List.is_empty goals then tclUNIT ()
               else
	         let sigma' = mark_unresolvables sigma goals in
                 with_shelf (Unsafe.tclEVARS sigma' <*> Unsafe.tclNEWGOALS (CList.map Proofview.with_empty_state goals)) >>=
                      fun s -> result s i (Some (Option.default 0 k + j)))
          end
        in with_shelf res >>= fun (sh, ()) ->
           tclEVARMAP >>= finish sh
      in
      if path_matches derivs [] then aux e tl
      else
        ortac
             (with_shelf tac >>= fun s ->
              let i = !idx in incr idx; result s i None)
             (fun e' ->
	      if CErrors.noncritical (fst e') then
                (pr_error e'; aux (merge_exceptions e e') tl)
              else iraise e')
    and aux e = function
      | x :: xs -> onetac e x xs
      | [] ->
         if !foundone == false && !typeclasses_debug > 0 then
           Feedback.msg_debug
             (pr_depth info.search_depth ++ str": no match for " ++
                Printer.pr_econstr_env (Goal.env gl) sigma concl ++
                str ", " ++ int (List.length poss) ++
                str" possibilities");
         match e with
         | (ReachedLimitEx,ie) -> Proofview.tclZERO ~info:ie ReachedLimitEx
         | (_,ie) -> Proofview.tclZERO ~info:ie NoApplicableEx
    in
    if backtrack then aux (NoApplicableEx,Exninfo.null) poss
    else tclONCE (aux (NoApplicableEx,Exninfo.null) poss)

  let hints_tac hints info kont : unit Proofview.tactic =
    Proofview.Goal.enter
      (fun gl -> hints_tac_gl hints info kont gl)

  let intro_tac info kont gl =
    let open Proofview in
    let env = Goal.env gl in
    let sigma = Goal.sigma gl in
    let decl = Tacmach.New.pf_last_hyp gl in
    let hint =
      make_resolve_hyp env sigma (Hint_db.transparent_state info.search_hints)
                       (true,false,false) info.search_only_classes empty_hint_info decl in
    let ldb = Hint_db.add_list env sigma hint info.search_hints in
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
      if !typeclasses_debug > 1 then
        Feedback.msg_debug
          (str"calling eauto recursively at depth " ++ int (succ depth)
           ++ str" on " ++ int i ++ str" subgoals");
      search_tac hints limit (succ depth) info
    in
    fun info ->
    if Int.equal depth (succ limit) then Proofview.tclZERO ReachedLimitEx
    else
      Proofview.tclOR (hints_tac hints info kont)
                      (fun e -> Proofview.tclOR (intro info kont)
                      (fun e' -> let (e, info) = merge_exceptions e e' in
                              Proofview.tclZERO ~info e))

  let search_tac_gl ?st only_classes dep hints depth i sigma gls gl :
        unit Proofview.tactic =
    let open Proofview in
    let dep = dep || Proofview.unifiable sigma (Goal.goal gl) gls in
    let info = make_autogoal ?st only_classes dep (cut_of_hints hints) i gl in
    search_tac hints depth 1 info

  let search_tac ?(st=full_transparent_state) only_classes dep hints depth =
    let open Proofview in
    let tac sigma gls i =
      Goal.enter
        begin fun gl ->
          search_tac_gl ~st only_classes dep hints depth (succ i) sigma gls gl end
    in
      Proofview.Unsafe.tclGETGOALS >>= fun gls ->
      let gls = CList.map Proofview.drop_state gls in
      Proofview.tclEVARMAP >>= fun sigma ->
      let j = List.length gls in
      (tclDISPATCH (List.init j (fun i -> tac sigma gls i)))

  let fix_iterative t =
    let rec aux depth =
      Proofview.tclOR
        (t depth)
        (function
         | (ReachedLimitEx,_) -> aux (succ depth)
         | (e,ie) -> Proofview.tclZERO ~info:ie e)
    in aux 1

  let fix_iterative_limit limit t =
    let open Proofview in
    let rec aux depth =
      if Int.equal depth (succ limit) then tclZERO ReachedLimitEx
      else tclOR (t depth) (function (ReachedLimitEx, _) -> aux (succ depth)
                                   | (e,ie) -> Proofview.tclZERO ~info:ie e)
    in aux 1

  let eauto_tac ?(st=full_transparent_state) ?(unique=false)
                ~only_classes ?strategy ~depth ~dep hints =
    let open Proofview in
    let tac =
      let search = search_tac ~st only_classes dep hints in
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
    let error (e, ie) =
      match e with
      | ReachedLimitEx ->
         Tacticals.New.tclFAIL 0 (str"Proof search reached its limit")
      | NoApplicableEx ->
         Tacticals.New.tclFAIL 0 (str"Proof search failed" ++
                                    (if Option.is_empty depth then mt()
                                     else str" without reaching its limit"))
      | Proofview.MoreThanOneSuccess ->
         Tacticals.New.tclFAIL 0 (str"Proof search failed: " ++
                                  str"more than one success found")
      | e -> Proofview.tclZERO ~info:ie e
    in
    let tac = Proofview.tclOR tac error in
    let tac =
      if unique then
        Proofview.tclEXACTLY_ONCE Proofview.MoreThanOneSuccess tac
      else tac
    in
    with_shelf numgoals >>= fun (initshelf, i) ->
    (if !typeclasses_debug > 1 then
       Feedback.msg_debug (str"Starting resolution with " ++ int i ++
                             str" goal(s) under focus and " ++
                             int (List.length initshelf) ++ str " shelved goal(s)" ++
                             (if only_classes then str " in only_classes mode" else str " in regular mode") ++
                             match depth with None -> str ", unbounded"
                                            | Some i -> str ", with depth limit " ++ int i));
    tac

  let run_on_evars env evm p tac =
    match evars_to_goals p evm with
    | None -> None (* This happens only because there's no evar having p *)
    | Some (goals, evm') ->
       let goals =
         if !typeclasses_dependency_order then
           top_sort evm' goals
         else List.map (fun (ev, _) -> ev) (Evar.Map.bindings goals)
       in
       let fgoals = Evd.save_future_goals evm in
       let _, pv = Proofview.init evm' [] in
       let pv = Proofview.unshelve goals pv in
       try
         let (), pv', (unsafe, shelved, gaveup), _ =
           Proofview.apply env tac pv
         in
         if not (List.is_empty gaveup) then
           CErrors.anomaly (Pp.str "run_on_evars not assumed to apply tactics generating given up goals.");
         if Proofview.finished pv' then
           let evm' = Proofview.return pv' in
           assert(Evd.fold_undefined (fun ev _ acc ->
                      let okev = Evd.mem evm ev || List.mem ev shelved in
                      if not okev then
                        Feedback.msg_debug
                          (str "leaking evar " ++ int (Evar.repr ev) ++
                             spc () ++ pr_ev evm' ev);
                      acc && okev) evm' true);
           let fgoals = Evd.shelve_on_future_goals shelved fgoals in
           let evm' = Evd.restore_future_goals evm' fgoals in
           let evm' = evars_reset_evd ~with_conv_pbs:true ~with_univs:false evm' evm in
           Some evm'
         else raise Not_found
       with Logic_monad.TacticFailure _ -> raise Not_found

  let evars_eauto env evd depth only_classes unique dep st hints p =
    let eauto_tac = eauto_tac ~st ~unique ~only_classes ~depth ~dep:(unique || dep) hints in
    let res = run_on_evars env evd p eauto_tac in
    match res with
    | None -> evd
    | Some evd' -> evd'

  let typeclasses_eauto env evd ?depth unique st hints p =
    evars_eauto env evd depth true unique false st hints p
  (** Typeclasses eauto is an eauto which tries to resolve only
      goals of typeclass type, and assumes that the initially selected
      evars in evd are independent of the rest of the evars *)

  let typeclasses_resolve env evd debug depth unique p =
    let db = searchtable_map typeclasses_db in
    typeclasses_eauto env evd ?depth unique (Hint_db.transparent_state db) [db] p
end

(** Binding to either V85 or Search implementations. *)

let typeclasses_eauto ?(only_classes=false) ?(st=full_transparent_state)
                      ?strategy ~depth dbs =
  let dbs = List.map_filter
              (fun db -> try Some (searchtable_map db)
                      with e when CErrors.noncritical e -> None)
              dbs
  in
  let st = match dbs with x :: _ -> Hint_db.transparent_state x | _ -> st in
  let depth = match depth with None -> get_typeclasses_depth () | Some l -> Some l in
  Search.eauto_tac ~st ~only_classes ?strategy ~depth ~dep:true dbs

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
  Evd.fold_undefined
    (fun ev evi _ ->
      if Typeclasses.is_resolvable evi && pred evm ev evi then
        let evars = Evar.Set.add ev (Evarutil.undefined_evars_of_evar_info evm evi)
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
    let evi = Evd.find_undefined evd ev in
    if Typeclasses.is_resolvable evi && snd (p ev evi)
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
    let ev_class = class_of_constr evd evi.evar_concl in
    if not (Option.is_empty ev_class) && is_part ev then
      (* focus on one instance if only one was searched for *)
      if not found then (true, Some ev)
      else (found, None)
    else (found, accu)
   in
  let (_, ev) = Evd.fold_undefined fold evd (true, None) in
  Pretype_errors.unsatisfiable_constraints env evd ev comp

(** Check if an evar is concerned by the current resolution attempt,
    (and in particular is in the current component), and also update
    its evar_info.
    Invariant : this should only be applied to undefined evars,
    and return undefined evar_info *)

let select_and_update_evars p oevd in_comp evd ev evi =
  assert (evi.evar_body == Evar_empty);
  try
    let oevi = Evd.find_undefined oevd ev in
    if Typeclasses.is_resolvable oevi then
      Typeclasses.mark_unresolvable evi,
      (in_comp ev && p evd ev evi)
    else evi, false
  with Not_found ->
    Typeclasses.mark_unresolvable evi, p evd ev evi

(** Do we still have unresolved evars that should be resolved ? *)

let has_undefined p oevd evd =
  let check ev evi = snd (p oevd ev evi) in
  Evar.Map.exists check (Evd.undefined_map evd)

(** Revert the resolvability status of evars after resolution,
    potentially unprotecting some evars that were set unresolvable
    just for this call to resolution. *)

let revert_resolvability oevd evd =
  let map ev evi =
    try
      if not (Typeclasses.is_resolvable evi) then
        let evi' = Evd.find_undefined oevd ev in
        if Typeclasses.is_resolvable evi' then
          Typeclasses.mark_resolvable evi
        else evi
      else evi
    with Not_found -> evi
  in
  Evd.raw_map_undefined map evd

exception Unresolved

(** If [do_split] is [true], we try to separate the problem in
    several components and then solve them separately *)
let resolve_all_evars debug depth unique env p oevd do_split fail =
  let split = if do_split then split_evars p oevd else [Evar.Set.empty] in
  let in_comp comp ev = if do_split then Evar.Set.mem ev comp else true
  in
  let rec docomp evd = function
    | [] -> revert_resolvability oevd evd
    | comp :: comps ->
      let p = select_and_update_evars p oevd (in_comp comp) in
      try
        let evd' = Search.typeclasses_resolve env evd debug depth unique p in
         if has_undefined p oevd evd' then raise Unresolved;
         docomp evd' comps
      with Unresolved | Not_found ->
        if fail && (not do_split || is_mandatory (p evd) comp evd)
        then (* Unable to satisfy the constraints. *)
          let comp = if do_split then Some comp else None in
          error_unresolvable env comp evd
        else (* Best effort: do nothing on this component *)
          docomp evd comps
  in docomp oevd split

let initial_select_evars filter =
  fun evd ev evi ->
    filter ev (snd evi.Evd.evar_source) &&
    Typeclasses.is_class_evar evd evi

let resolve_typeclass_evars debug depth unique env evd filter split fail =
  let evd =
    try Evarconv.solve_unif_constraints_with_heuristics
      ~ts:(Typeclasses.classes_transparent_state ()) env evd
    with e when CErrors.noncritical e -> evd
  in
    resolve_all_evars debug depth unique env
                      (initial_select_evars filter) evd split fail

let solve_inst env evd filter unique split fail =
  resolve_typeclass_evars
    (get_typeclasses_debug ())
    (get_typeclasses_depth ())
    unique env evd filter split fail

let _ =
  Hook.set Typeclasses.solve_all_instances_hook solve_inst

let resolve_one_typeclass env ?(sigma=Evd.from_env env) gl unique =
  let nc, gl, subst, _ = Evarutil.push_rel_context_to_named_context env sigma gl in
  let (gl,t,sigma) =
    Goal.V82.mk_goal sigma nc gl Store.empty in
  let (ev, _) = destEvar sigma t in
  let gls = { it = gl ; sigma = sigma; } in
  let hints = searchtable_map typeclasses_db in
  let st = Hint_db.transparent_state hints in
  let depth = get_typeclasses_depth () in
  let gls' =
      try
        Proofview.V82.of_tactic
        (Search.eauto_tac ~st ~only_classes:true ~depth [hints] ~dep:true) gls
      with Refiner.FailError _ -> raise Not_found
  in
  let evd = sig_sig gls' in
  let t' = mkEvar (ev, Array.of_list subst) in
  let term = Evarutil.nf_evar evd t' in
    evd, term

let _ =
  Hook.set Typeclasses.solve_one_instance_hook
    (fun x y z w -> resolve_one_typeclass x ~sigma:y z w)

(** Take the head of the arity of a constr.
    Used in the partial application tactic. *)

let rec head_of_constr sigma t =
  let t = strip_outer_cast sigma (collapse_appl sigma t) in
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
  | Evar _ -> Tacticals.New.tclFAIL 0 (str"Evar")
  | _ -> Proofview.tclUNIT ()

let is_ground c =
  let open Tacticals.New in
  Proofview.tclEVARMAP >>= fun sigma ->
  if Evarutil.is_ground_term sigma c then tclIDTAC
  else tclFAIL 0 (str"Not ground")

let autoapply c i =
  let open Proofview.Notations in
  Proofview.Goal.enter begin fun gl ->
  let hintdb = try Hints.searchtable_map i with Not_found ->
    CErrors.user_err (Pp.str ("Unknown hint database " ^ i ^ "."))
  in
  let flags = auto_unif_flags Evar.Set.empty
    (Hints.Hint_db.transparent_state hintdb) in
  let cty = Tacmach.New.pf_unsafe_type_of gl c in
  let ce = mk_clenv_from gl (c,cty) in
    unify_e_resolve false flags gl
                                 ((c,cty,Univ.ContextSet.empty),0,ce) <*>
      Proofview.tclEVARMAP >>= (fun sigma ->
      let sigma = Typeclasses.mark_unresolvables ~filter:Typeclasses.all_goals sigma in
      Proofview.Unsafe.tclEVARS sigma) end
