(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* TODO:
  - Find an interface allowing eauto to backtrack when shelved goals remain,
   e.g. to force instantiations.
  - unique solutions
 *)

open Pp
open CErrors
open Util
open Names
open Term
open Termops
open Reduction
open Proof_type
open Tacticals
open Tacmach
open Tactics
open Clenv
open Typeclasses
open Globnames
open Evd
open Locus
open Misctypes
open Proofview.Notations
open Hints

(** Hint database named "typeclass_instances", now created directly in Auto *)

(** Options handling *)

let typeclasses_debug = ref 0
let typeclasses_depth = ref None

let typeclasses_modulo_eta = ref false
let set_typeclasses_modulo_eta d = (:=) typeclasses_modulo_eta d
let get_typeclasses_modulo_eta () = !typeclasses_modulo_eta

let typeclasses_limit_intros = ref false
let set_typeclasses_limit_intros d = (:=) typeclasses_limit_intros d
let get_typeclasses_limit_intros () = !typeclasses_limit_intros

let typeclasses_dependency_order = ref false
let set_typeclasses_dependency_order d = (:=) typeclasses_dependency_order d
let get_typeclasses_dependency_order () = !typeclasses_dependency_order

let typeclasses_iterative_deepening = ref false
let set_typeclasses_iterative_deepening d = (:=) typeclasses_iterative_deepening d
let get_typeclasses_iterative_deepening () = !typeclasses_iterative_deepening

let get_compat_version d =
  match d with
  | "8.5" -> Flags.V8_5
  | _ -> Flags.Current

let typeclasses_unif_compat = ref Flags.V8_5
let set_typeclasses_unif_compat d =
  if d == Flags.Current then set_typeclasses_limit_intros false
  else set_typeclasses_limit_intros true;
  (:=) typeclasses_unif_compat d

let get_typeclasses_unif_compat () = !typeclasses_unif_compat
let set_typeclasses_unif_compat_string d =
  set_typeclasses_unif_compat (get_compat_version d)
let get_typeclasses_unif_compat_string () =
  Flags.pr_version (get_typeclasses_unif_compat ())

let typeclasses_compat = ref Flags.Current
let set_typeclasses_compat d = (:=) typeclasses_compat d
let get_typeclasses_compat () = !typeclasses_compat
let set_typeclasses_compat_string d =
  set_typeclasses_compat (get_compat_version d)

let get_typeclasses_compat_string () =
  Flags.pr_version (get_typeclasses_compat ())

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
    { optsync  = true;
      optdepr  = false;
      optname  = "do typeclass search modulo eta conversion";
      optkey   = ["Typeclasses";"Modulo";"Eta"];
      optread  = get_typeclasses_modulo_eta;
      optwrite = set_typeclasses_modulo_eta; }

let _ =
  declare_bool_option
    { optsync  = true;
      optdepr  = false;
      optname  = "do typeclass search avoiding eta-expansions " ^
                   " in proof terms (expensive)";
      optkey   = ["Typeclasses";"Limit";"Intros"];
      optread  = get_typeclasses_limit_intros;
      optwrite = set_typeclasses_limit_intros; }

let _ =
  declare_bool_option
    { optsync  = true;
      optdepr  = false;
      optname  = "during typeclass resolution, solve instances according to their dependency order";
      optkey   = ["Typeclasses";"Dependency";"Order"];
      optread  = get_typeclasses_dependency_order;
      optwrite = set_typeclasses_dependency_order; }

let _ =
  declare_bool_option
    { optsync  = true;
      optdepr  = false;
      optname  = "use iterative deepening strategy";
      optkey   = ["Typeclasses";"Iterative";"Deepening"];
      optread  = get_typeclasses_iterative_deepening;
      optwrite = set_typeclasses_iterative_deepening; }

let _ =
  declare_string_option
    { optsync  = true;
      optdepr  = false;
      optname  = "compat";
      optkey   = ["Typeclasses";"Compatibility"];
      optread  = get_typeclasses_compat_string;
      optwrite = set_typeclasses_compat_string; }

let _ =
  declare_string_option
    { optsync  = true;
      optdepr  = false;
      optname  = "compat";
      optkey   = ["Typeclasses";"Unification";"Compatibility"];
      optread  = get_typeclasses_unif_compat_string;
      optwrite = set_typeclasses_unif_compat_string; }

let set_typeclasses_debug =
  declare_bool_option
    { optsync  = true;
      optdepr  = false;
      optname  = "debug output for typeclasses proof search";
      optkey   = ["Typeclasses";"Debug"];
      optread  = get_typeclasses_debug;
      optwrite = set_typeclasses_debug; }

let _ =
  declare_bool_option
    { optsync  = true;
      optdepr  = false;
      optname  = "debug output for typeclasses proof search";
      optkey   = ["Debug";"Typeclasses"];
      optread  = get_typeclasses_debug;
      optwrite = set_typeclasses_debug; }

let _ =
  declare_int_option
    { optsync  = true;
      optdepr  = false;
      optname  = "verbosity of debug output for typeclasses proof search";
      optkey   = ["Typeclasses";"Debug";"Verbosity"];
      optread  = get_typeclasses_verbose;
      optwrite = set_typeclasses_verbose; }

let set_typeclasses_depth =
  declare_int_option
    { optsync  = true;
      optdepr  = false;
      optname  = "depth for typeclasses proof search";
      optkey   = ["Typeclasses";"Depth"];
      optread  = get_typeclasses_depth;
      optwrite = set_typeclasses_depth; }

let pr_ev evs ev =
  Printer.pr_constr_env (Goal.V82.env evs ev) evs
                        (Evarutil.nf_evar evs (Goal.V82.concl evs ev))

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
  modulo_eta = !typeclasses_modulo_eta;
}

let auto_unif_flags freeze st =
  let fl = auto_core_unif_flags st freeze in
  { core_unify_flags = fl;
    merge_unify_flags = fl;
    subterm_unify_flags = fl;
    allow_K_in_toplevel_higher_order_unification = false;
    resolve_evars = false
}

let e_give_exact flags poly (c,clenv) gl =
  let (c, _, _) = c in
  let c, gl =
    if poly then
      let clenv', subst = Clenv.refresh_undefined_univs clenv in
      let evd = evars_reset_evd ~with_conv_pbs:true gl.sigma clenv'.evd in
      let c = Vars.subst_univs_level_constr subst c in
        c, {gl with sigma = evd}
    else c, gl
  in
  let t1 = pf_unsafe_type_of gl c in
  Proofview.V82.of_tactic (Clenvtac.unify ~flags t1 <*> exact_no_check c) gl

let unify_e_resolve poly flags = { enter = begin fun gls (c,_,clenv) ->
  let clenv', c = connect_hint_clenv poly c clenv gls in
  let clenv' = Tacmach.New.of_old (clenv_unique_resolver ~flags clenv') gls in
    Clenvtac.clenv_refine true ~with_classes:false clenv'
  end }

let unify_resolve poly flags = { enter = begin fun gls (c,_,clenv) ->
  let clenv', _ = connect_hint_clenv poly c clenv gls in
  let clenv' = Tacmach.New.of_old (clenv_unique_resolver ~flags clenv') gls in
    Clenvtac.clenv_refine false ~with_classes:false clenv'
  end }

(** Application of a lemma using [refine] instead of the old [w_unify] *)
let unify_resolve_refine poly flags =
  let open Clenv in
  { enter = begin fun gls ((c, t, ctx),n,clenv) ->
    let env = Proofview.Goal.env gls in
    let concl = Proofview.Goal.concl gls in
    Refine.refine ~unsafe:true { Sigma.run = fun sigma ->
      let sigma = Sigma.to_evar_map sigma in
      let sigma, term, ty =
        if poly then
          let (subst, ctx) = Universes.fresh_universe_context_set_instance ctx in
          let map c = Vars.subst_univs_level_constr subst c in
          let sigma = Evd.merge_context_set Evd.univ_flexible sigma ctx in
          sigma, map c, map t
        else
          let sigma = Evd.merge_context_set Evd.univ_flexible sigma ctx in
          sigma, c, t
      in
      let sigma', cl = Clenv.make_evar_clause env sigma ?len:n ty in
      let term = applistc term (List.map (fun x -> x.hole_evar) cl.cl_holes) in
      let sigma' =
        let evdref = ref sigma' in
        if not (Evarconv.e_cumul env ~ts:flags.core_unify_flags.modulo_delta
                                      evdref cl.cl_concl concl) then
          Type_errors.error_actual_type env
            {Environ.uj_val = term; Environ.uj_type = cl.cl_concl}
            concl;
        !evdref
      in Sigma.here term (Sigma.Unsafe.of_evar_map sigma') }
  end }

(** Dealing with goals of the form A -> B and hints of the form
  C -> A -> B.
*)
let clenv_of_prods poly nprods (c, clenv) gl =
  let (c, _, _) = c in
  if poly || Int.equal nprods 0 then Some (None, clenv)
  else
    let ty = Retyping.get_type_of (Proofview.Goal.env gl)
                                  (Sigma.to_evar_map (Proofview.Goal.sigma gl)) c in
    let diff = nb_prod ty - nprods in
      if Pervasives.(>=) diff 0 then
        (* Was Some clenv... *)
        Some (Some diff,
              Tacmach.New.of_old (fun gls -> mk_clenv_from_n gls (Some diff) (c,ty)) gl)
      else None

let with_prods nprods poly (c, clenv) f =
  if get_typeclasses_limit_intros () then
    Proofview.Goal.nf_enter { enter = begin fun gl ->
     match clenv_of_prods poly nprods (c, clenv) gl with
     | None -> Tacticals.New.tclZEROMSG (str"Not enough premisses")
     | Some (diff, clenv') -> f.enter gl (c, diff, clenv') end }
  else Proofview.Goal.nf_enter
         { enter = begin fun gl ->
                   if Int.equal nprods 0 then f.enter gl (c, None, clenv)
                   else Tacticals.New.tclZEROMSG (str"Not enough premisses") end }

let matches_pattern concl pat =
  let matches env sigma =
    match pat with
    | None -> Proofview.tclUNIT ()
    | Some pat ->
       let sigma = Sigma.to_evar_map sigma in
       if Constr_matching.is_matching env sigma pat concl then
         Proofview.tclUNIT ()
       else
         Tacticals.New.tclZEROMSG (str "conclPattern")
  in
   Proofview.Goal.enter { enter = fun gl ->
     let env = Proofview.Goal.env gl in
     let sigma = Proofview.Goal.sigma gl in
       matches env sigma }

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
  (if !typeclasses_debug > 1 then
     Feedback.msg_debug (str" shelving goals: " ++ pr_gls sigma gls);
   shelve_goals gls)

(** Hack to properly solve dependent evars that are typeclasses *)
let rec e_trivial_fail_db only_classes db_list local_db =
  let open Tacticals.New in
  let open Tacmach.New in
  let trivial_fail =
    Proofview.Goal.nf_enter { enter =
    begin fun gl ->
    let env = Proofview.Goal.env gl in
    let sigma = Tacmach.New.project gl in
    let d = pf_last_hyp gl in
    let hintl = make_resolve_hyp env sigma d in
    let hints = Hint_db.add_list env sigma hintl local_db in
      e_trivial_fail_db only_classes db_list hints
      end }
  in
  let trivial_resolve =
    Proofview.Goal.nf_enter { enter =
    begin fun gl ->
    let tacs = e_trivial_resolve db_list local_db only_classes
                                 (project gl) (pf_concl gl) in
      tclFIRST (List.map (fun (x,_,_,_,_) -> x) tacs)
    end}
  in
  let tacl =
    Eauto.registered_e_assumption ::
    (tclTHEN Tactics.intro trivial_fail :: [trivial_resolve])
  in
  tclFIRST (List.map tclCOMPLETE tacl)

and e_my_find_search db_list local_db hdc complete only_classes sigma concl =
  let open Proofview.Notations in
  let prods, concl = decompose_prod_assum concl in
  let nprods = List.length prods in
  let freeze =
    try
      let cl = Typeclasses.class_info (fst hdc) in
        if cl.cl_strict then
          Evd.evars_of_term concl
        else Evar.Set.empty
    with e when CErrors.noncritical e -> Evar.Set.empty
  in
  let hintl =
    List.map_append
      (fun db ->
        let tacs =
          if Hint_db.use_dn db then (* Using dnet *)
            Hint_db.map_eauto hdc concl db
          else Hint_db.map_existential hdc concl db
        in
        let flags = auto_unif_flags freeze (Hint_db.transparent_state db) in
          List.map (fun x -> (flags, x)) tacs)
      (local_db::db_list)
  in
  let tac_of_hint =
    fun (flags, {pri = b; pat = p; poly = poly; code = t; name = name}) ->
      let tac = function
        | Res_pf (term,cl) ->
           if get_typeclasses_unif_compat () = Flags.Current then
             let tac =
               with_prods nprods poly (term,cl)
                          ({ enter = fun gl clenv ->
                             (matches_pattern concl p) <*>
                               ((unify_resolve_refine poly flags).enter gl clenv)})
             in Tacticals.New.tclTHEN tac Proofview.shelve_unifiable
           else
             let tac =
               with_prods nprods poly (term,cl) (unify_resolve poly flags) in
             if get_typeclasses_compat () = Flags.V8_5 then
               Tacticals.New.tclTHEN tac Proofview.shelve_unifiable
             else
               Proofview.tclBIND (Proofview.with_shelf tac)
                  (fun (gls, ()) -> shelve_dependencies gls)
        | ERes_pf (term,cl) ->
           if get_typeclasses_unif_compat () = Flags.Current then
             let tac = (with_prods nprods poly (term,cl)
                  ({ enter = fun gl clenv ->
                             (matches_pattern concl p) <*>
                               ((unify_resolve_refine poly flags).enter gl clenv)})) in
             Tacticals.New.tclTHEN tac Proofview.shelve_unifiable
           else
             let tac =
               with_prods nprods poly (term,cl) (unify_e_resolve poly flags) in
             if get_typeclasses_compat () = Flags.V8_5 then
               Tacticals.New.tclTHEN tac Proofview.shelve_unifiable
             else
               Proofview.tclBIND (Proofview.with_shelf tac)
                  (fun (gls, ()) -> shelve_dependencies gls)
      | Give_exact c -> Proofview.V82.tactic (e_give_exact flags poly c)
      | Res_pf_THEN_trivial_fail (term,cl) ->
         let fst = with_prods nprods poly (term,cl) (unify_e_resolve poly flags) in
         let snd = if complete then Tacticals.New.tclIDTAC
                   else e_trivial_fail_db only_classes db_list local_db in
         Tacticals.New.tclTHEN fst snd
      | Unfold_nth c ->
         let tac = Proofview.V82.of_tactic (unfold_in_concl [AllOccurrences,c]) in
         Proofview.V82.tactic (tclWEAK_PROGRESS tac)
      | Extern tacast -> conclPattern concl p tacast
      in
      let tac = run_hint t tac in
      let tac = if complete then Tacticals.New.tclCOMPLETE tac else tac in
      let pp =
        match p with
        | Some pat when get_typeclasses_unif_compat () = Flags.Current ->
           str " with pattern " ++ Printer.pr_constr_pattern pat
        | _ -> mt ()
      in
        match repr_hint t with
        | Extern _ -> (tac, b, true, name, lazy (pr_hint t ++ pp))
        | _ -> (tac, b, false, name, lazy (pr_hint t ++ pp))
  in List.map tac_of_hint hintl

and e_trivial_resolve db_list local_db only_classes sigma concl =
  try
    e_my_find_search db_list local_db
     (decompose_app_bound concl) true only_classes sigma concl
  with Bound | Not_found -> []

let e_possible_resolve db_list local_db only_classes sigma concl =
  try
    e_my_find_search db_list local_db
      (decompose_app_bound concl) false only_classes sigma concl
  with Bound | Not_found -> []

let cut_of_hints h =
  List.fold_left (fun cut db -> PathOr (Hint_db.cut db, cut)) PathEmpty h

let catchable = function
  | Refiner.FailError _ -> true
  | e -> Logic.catchable_exception e

let pr_depth l = prlist_with_sep (fun () -> str ".") int (List.rev l)

let is_Prop env sigma concl =
  let ty = Retyping.get_type_of env sigma concl in
  match kind_of_term ty with
  | Sort (Prop Null) -> true
  | _ -> false

let is_unique env concl =
  try
    let (cl,u), args = dest_class_app env concl in
    cl.cl_unique
  with e when CErrors.noncritical e -> false

(** Sort the undefined variables from the least-dependent to most dependent. *)
let top_sort evm undefs =
  let l' = ref [] in
  let tosee = ref undefs in
  let rec visit ev evi =
    let evs = Evarutil.undefined_evars_of_evar_info evm evi in
      Evar.Set.iter (fun ev ->
        if Evar.Map.mem ev !tosee then
          visit ev (Evar.Map.find ev !tosee)) evs;
      tosee := Evar.Map.remove ev !tosee;
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
  let open Context.Named.Declaration in
  let id = get_id decl in
  let cty = Evarutil.nf_evar sigma (get_type decl) in
  let rec iscl env ty =
    let ctx, ar = decompose_prod_assum ty in
      match kind_of_term (fst (decompose_app ar)) with
      | Const (c,_) -> is_class (ConstRef c)
      | Ind (i,_) -> is_class (IndRef i)
      | _ ->
          let env' = Environ.push_rel_context ctx env in
          let ty' = whd_betadeltaiota env' ar in
               if not (Term.eq_constr ty' ar) then iscl env' ty'
               else false
  in
  let is_class = iscl env cty in
  let keep = not only_classes || is_class in
    if keep then
      let c = mkVar id in
      let name = PathHints [VarRef id] in
      let hints =
        if is_class then
          let hints = build_subclasses ~check:false env sigma (VarRef id) None in
            (List.map_append
               (fun (path,pri, c) -> make_resolves env sigma ~name:(PathHints path)
                  (true,false,Flags.is_verbose()) pri false
                 (IsConstr (c,Univ.ContextSet.empty)))
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
          let open Context.Named.Declaration in
          try let t = Global.lookup_named (get_id hyp) |> get_type in
              (* Section variable, reindex only if the type changed *)
              not (Term.eq_constr t (get_type hyp))
          with Not_found -> true
        in
        if consider then
          let hint =
            pf_apply make_resolve_hyp g st (true,false,false) only_classes None hyp
          in hint @ hints
        else hints)
      ([]) sign
  in Hint_db.add_list (pf_env g) (project g) hintlist (Hint_db.empty st true)

(** <= 8.5 resolution *)
module V85 = struct

  type autoinfo = { hints : hint_db; is_evar: existential_key option;
                    only_classes: bool; unique : bool;
                    auto_depth: int list; auto_last_tac: std_ppcmds Lazy.t;
                    auto_path : global_reference option list;
                    auto_cut : hints_path }
  type autogoal = goal * autoinfo
  type failure = NotApplicable | ReachedLimit
  type 'ans fk = failure -> 'ans
  type ('a,'ans) sk = 'a -> 'ans fk -> 'ans
  type 'a tac = { skft : 'ans. ('a,'ans) sk -> 'ans fk -> autogoal sigma -> 'ans }

  type auto_result = autogoal list sigma

  type atac = auto_result tac

  (* Some utility types to avoid the need of -rectypes *)

  type 'a optionk =
    | Nonek
    | Somek of 'a * 'a optionk fk

  type ('a,'b) optionk2 =
    | Nonek2 of failure
    | Somek2 of 'a * 'b * ('a,'b) optionk2 fk

  let pf_filtered_hyps gls =
    Goal.V82.hyps gls.Evd.sigma (sig_it gls)

  let make_autogoal_hints =
    let cache = ref (true, Environ.empty_named_context_val,
                     Hint_db.empty full_transparent_state true)
    in
    fun only_classes ?(st=full_transparent_state) g ->
    let sign = pf_filtered_hyps g in
    let (onlyc, sign', cached_hints) = !cache in
    if onlyc == only_classes &&
         (sign == sign' || Environ.eq_named_context_val sign sign')
         && Hint_db.transparent_state cached_hints == st
    then
      cached_hints
    else
      let hints = make_hints g st only_classes (Environ.named_context_of_val sign)
      in
      cache := (only_classes, sign, hints); hints

  let lift_tactic tac (f : goal list sigma -> autoinfo -> autogoal list sigma) : 'a tac =
    { skft = fun sk fk {it = gl,hints; sigma=s;} ->
             let res = try Some (tac {it=gl; sigma=s;})
                       with e when catchable e -> None in
             match res with
             | Some gls -> sk (f gls hints) fk
             | None -> fk NotApplicable }

  let intro_tac : atac =
    let tac {it = gls; sigma = s} info =
      let gls' =
        List.map (fun g' ->
            let env = Goal.V82.env s g' in
            let context = Environ.named_context_of_val (Goal.V82.hyps s g') in
            let hint = make_resolve_hyp env s (Hint_db.transparent_state info.hints)
              (true,false,false) info.only_classes None (List.hd context) in
            let ldb = Hint_db.add_list env s hint info.hints in
            (g', { info with is_evar = None; hints = ldb;
                             auto_last_tac = lazy (str"intro") })) gls
      in {it = gls'; sigma = s;}
    in
    lift_tactic (Proofview.V82.of_tactic Tactics.intro) tac

  let normevars_tac : atac =
    { skft = fun sk fk {it = (gl, info); sigma = s;} ->
             let gl', sigma' = Goal.V82.nf_evar s gl in
             let info' = { info with auto_last_tac = lazy (str"normevars") } in
             sk {it = [gl', info']; sigma = sigma';} fk }

  let merge_failures x y =
    match x, y with
    | _, ReachedLimit
      | ReachedLimit, _ -> ReachedLimit
    | NotApplicable, NotApplicable -> NotApplicable

  let or_tac (x : 'a tac) (y : 'a tac) : 'a tac =
    { skft = fun sk fk gls -> x.skft sk
      (fun f -> y.skft sk (fun f' -> fk (merge_failures f f')) gls) gls }

  let or_else_tac (x : 'a tac) (y : failure -> 'a tac) : 'a tac =
    { skft = fun sk fk gls -> x.skft sk
      (fun f -> (y f).skft sk fk gls) gls }

  let needs_backtrack env evd oev concl =
    if Option.is_empty oev || is_Prop env evd concl then
      occur_existential concl
    else true

  let hints_tac hints sk fk {it = gl,info; sigma = s} =
    let env = Goal.V82.env s gl in
    let concl = Goal.V82.concl s gl in
    let tacgl = {it = gl; sigma = s;} in
    let poss = e_possible_resolve hints info.hints info.only_classes s concl in
    let unique = is_unique env concl in
    let rec aux i foundone = function
      | (tac, _, extern, name, pp) :: tl ->
         let derivs = path_derivate info.auto_cut name in
         let res =
           try
             if path_matches derivs [] then None
             else Some (Proofview.V82.of_tactic tac tacgl)
           with e when catchable e -> None
         in
         (match res with
          | None -> aux i foundone tl
          | Some {it = gls; sigma = s';} ->
             if !typeclasses_debug > 0 then
               Feedback.msg_debug
                 (pr_depth (i :: info.auto_depth) ++ str": " ++ Lazy.force pp
                  ++ str" on" ++ spc () ++ pr_ev s gl);
             let sgls =
               evars_to_goals
                 (fun evm ev evi ->
                   if Typeclasses.is_resolvable evi && not (Evd.is_undefined s ev) &&
                        (not info.only_classes || Typeclasses.is_class_evar evm evi)
                   then Typeclasses.mark_unresolvable evi, true
                   else evi, false) s'
             in
             let newgls, s' =
               let gls' = List.map (fun g -> (None, g)) gls in
               match sgls with
               | None -> gls', s'
               | Some (evgls, s') ->
                  if not !typeclasses_dependency_order then
                    (gls' @ List.map (fun (ev,_) -> (Some ev, ev)) (Evar.Map.bindings evgls), s')
                  else
                    (* Reorder with dependent subgoals. *)
                    let evm = List.fold_left
                                (fun acc g -> Evar.Map.add g (Evd.find_undefined s' g) acc) evgls gls in
                    let gls = top_sort s' evm in
                    (List.map (fun ev -> Some ev, ev) gls, s')
             in
             let reindex g =
               let open Goal.V82 in
               extern && not (Environ.eq_named_context_val
                             (hyps s' g) (hyps s' gl))
             in
             let gl' j (evar, g) =
               let hints' =
                 if reindex g then
                   make_autogoal_hints
                     info.only_classes
                     ~st:(Hint_db.transparent_state info.hints)
                     {it = g; sigma = s';}
                 else info.hints
               in
               { info with
                 auto_depth = j :: i :: info.auto_depth;
                 auto_last_tac = pp;
                 is_evar = evar;
                 hints = hints';
                 auto_cut = derivs }
             in
             let gls' = List.map_i (fun i g -> snd g, gl' i g) 1 newgls in
             let glsv = {it = gls'; sigma = s';} in
             let fk' =
               (fun e ->
                 let do_backtrack =
                   if unique then occur_existential concl
                   else if info.unique then true
                   else if List.is_empty gls' then
                     needs_backtrack env s' info.is_evar concl
                   else true
                 in
                 let e' = match foundone with None -> e
                                            | Some e' -> merge_failures e e' in
                 if !typeclasses_debug > 0 then
                   Feedback.msg_debug
                     ((if do_backtrack then str"Backtracking after "
                       else str "Not backtracking after ")
                      ++ Lazy.force pp);
                 if do_backtrack then aux (succ i) (Some e') tl
                 else fk e')
             in
             sk glsv fk')
      | [] ->
         if foundone == None && !typeclasses_debug > 0 then
           Feedback.msg_debug
             (pr_depth info.auto_depth ++ str": no match for " ++
                Printer.pr_constr_env (Goal.V82.env s gl) s concl ++
                spc () ++ str ", " ++ int (List.length poss) ++
                str" possibilities");
         match foundone with
         | Some e -> fk e
         | None -> fk NotApplicable
    in aux 1 None poss

  let hints_tac hints =
  { skft = fun sk fk gls -> hints_tac hints sk fk gls }

  let then_list (second : atac) (sk : (auto_result, 'a) sk) : (auto_result, 'a) sk =
    let rec aux s (acc : autogoal list list) fk = function
      | (gl,info) :: gls ->
         Control.check_for_interrupt ();
         (match info.is_evar with
          | Some ev when Evd.is_defined s ev -> aux s acc fk gls
          | _ ->
             second.skft
               (fun {it=gls';sigma=s'} fk' ->
                 let fk'' =
                   if not info.unique && List.is_empty gls' &&
                        not (needs_backtrack (Goal.V82.env s gl) s
                                           info.is_evar (Goal.V82.concl s gl))
                   then fk
                   else fk'
                 in
                 aux s' (gls'::acc) fk'' gls)
               fk {it = (gl,info); sigma = s; })
      | [] -> Somek2 (List.rev acc, s, fk)
    in fun {it = gls; sigma = s; } fk ->
       let rec aux' = function
         | Nonek2 e -> fk e
         | Somek2 (res, s', fk') ->
            let goals' = List.concat res in
            sk {it = goals'; sigma = s'; } (fun e -> aux' (fk' e))
       in aux' (aux s [] (fun e -> Nonek2 e) gls)

  let then_tac (first : atac) (second : atac) : atac =
    { skft = fun sk fk -> first.skft (then_list second sk) fk }

  let run_tac (t : 'a tac) (gl : autogoal sigma) : auto_result option =
    t.skft (fun x _ -> Some x) (fun _ -> None) gl

  type run_list_res = auto_result optionk

  let run_list_tac (t : 'a tac) p goals (gl : autogoal list sigma) : run_list_res =
    (then_list t (fun x fk -> Somek (x, fk)))
      gl
      (fun _ -> Nonek)

  let fail_tac reason : atac =
    { skft = fun sk fk _ -> fk reason }

  let rec fix (t : 'a tac) : 'a tac =
    then_tac t { skft = fun sk fk -> (fix t).skft sk fk }

  let rec fix_limit limit (t : 'a tac) : 'a tac =
    if Int.equal limit 0 then fail_tac ReachedLimit
    else then_tac t { skft = fun sk fk -> (fix_limit (pred limit) t).skft sk fk }

  let fix_iterative t =
    let rec aux depth =
      or_else_tac (fix_limit depth t)
                  (function
                   | NotApplicable as e -> fail_tac e
                   | ReachedLimit -> aux (succ depth))
    in aux 1

  let fix_iterative_limit limit (t : 'a tac) : 'a tac =
    let rec aux depth =
      if Int.equal limit depth then fail_tac ReachedLimit
      else or_tac (fix_limit depth t)
                  { skft = fun sk fk -> (aux (succ depth)).skft sk fk }
    in aux 1

  let make_autogoal ?(only_classes=true) ?(unique=false) ?(st=full_transparent_state)
                    cut ev g =
    let hints = make_autogoal_hints only_classes ~st g in
    (g.it, { hints = hints ; is_evar = ev; unique = unique;
             only_classes = only_classes; auto_depth = [];
             auto_last_tac = lazy (str"none");
             auto_path = []; auto_cut = cut })


  let make_autogoals ?(only_classes=true) ?(unique=false)
                     ?(st=full_transparent_state) hints gs evm' =
    let cut = cut_of_hints hints in
    let gl i g =
      let (gl, auto) = make_autogoal ~only_classes ~unique
                                     ~st cut (Some g) {it = g; sigma = evm'; } in
      (gl, { auto with auto_depth = [i]})
    in { it = List.map_i gl 1 gs; sigma = evm' }

  let get_result r =
    match r with
    | Nonek -> None
    | Somek (gls, fk) -> Some (gls.sigma,fk)

  let run_on_evars ?(only_classes=true) ?(unique=false) ?(st=full_transparent_state)
                   p evm hints tac =
    match evars_to_goals p evm with
    | None -> None (* This happens only because there's no evar having p *)
    | Some (goals, evm') ->
       let goals =
         if !typeclasses_dependency_order then
           top_sort evm' goals
         else List.map (fun (ev, _) -> ev) (Evar.Map.bindings goals)
       in
       let res = run_list_tac tac p goals
           (make_autogoals ~only_classes ~unique ~st hints goals evm') in
       match get_result res with
       | None -> raise Not_found
       | Some (evm', fk) ->
          Some (evars_reset_evd ~with_conv_pbs:true ~with_univs:false evm' evm, fk)

  let eauto_tac hints =
    then_tac normevars_tac (or_tac (hints_tac hints) intro_tac)

  let eauto_tac depth hints =
    if get_typeclasses_iterative_deepening () then
      match depth with
      | None -> fix_iterative (eauto_tac hints)
      | Some depth -> fix_iterative_limit depth (eauto_tac hints)
    else
      match depth with
      | None -> fix (eauto_tac hints)
      | Some depth -> fix_limit depth (eauto_tac hints)

  let real_eauto ?depth unique st hints p evd =
    let res =
      run_on_evars ~st ~unique p evd hints (eauto_tac depth hints)
    in
    match res with
    | None -> evd
    | Some (evd', fk) ->
       if unique then
         (match get_result (fk NotApplicable) with
          | Some (evd'', fk') -> error "Typeclass resolution gives multiple solutions"
          | None -> evd')
       else evd'

  let resolve_all_evars_once debug depth unique p evd =
    let db = searchtable_map typeclasses_db in
    real_eauto ?depth unique (Hint_db.transparent_state db) [db] p evd

  let eauto85 ?(only_classes=true) ?st depth hints g =
    let gl = { it = make_autogoal ~only_classes ?st
                                  (cut_of_hints hints) None g; sigma = project g; } in
    match run_tac (eauto_tac depth hints) gl with
    | None -> raise Not_found
    | Some {it = goals; sigma = s; } ->
       {it = List.map fst goals; sigma = s;}

end

(** 8.6 resolution *)
module Search = struct
  type autoinfo =
    { search_depth : int list;
      last_tac : Pp.std_ppcmds Lazy.t;
      search_dep : bool;
      search_only_classes : bool;
      search_cut : hints_path;
      search_hints : hint_db; }

  (** Local hints *)
  let autogoal_cache = ref (DirPath.empty, true, Context.Named.empty,
                            Hint_db.empty full_transparent_state true)

  let make_autogoal_hints only_classes ?(st=full_transparent_state) g =
    let open Proofview in
    let open Tacmach.New in
    let sign = Goal.hyps g in
    let (dir, onlyc, sign', cached_hints) = !autogoal_cache in
    let cwd = Lib.cwd () in
    if DirPath.equal cwd dir &&
         (onlyc == only_classes) &&
           Context.Named.equal sign sign' &&
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
  exception NotApplicableEx

  (** ReachedLimitEx has priority over NotApplicableEx to handle
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
      occur_existential concl
    else true

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
    let s = Sigma.to_evar_map sigma in
    let unique = not info.search_dep || is_unique env concl in
    let backtrack = needs_backtrack env s unique concl in
    if !typeclasses_debug > 0 then
      Feedback.msg_debug
        (pr_depth info.search_depth ++ str": looking for " ++
           Printer.pr_constr_env (Goal.env gl) s concl ++
           (if backtrack then str" with backtracking"
            else str" without backtracking"));
    let poss =
      e_possible_resolve hints info.search_hints info.search_only_classes s concl in
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
      (if !typeclasses_debug > 1 then
         Feedback.msg_debug
           (pr_depth (!idx :: info.search_depth) ++ str": trying " ++
              Lazy.force pp ++
              (if !foundone != true then
                 str" on" ++ spc () ++ pr_ev s (Proofview.Goal.goal gl)
               else mt ())));
      let tac_of gls i j = Goal.nf_enter { enter = fun gl' ->
        let sigma' = Goal.sigma gl' in
        let s' = Sigma.to_evar_map sigma' in
        let _concl = Goal.concl gl' in
        if !typeclasses_debug > 0 then
          Feedback.msg_debug
            (pr_depth (succ j :: i :: info.search_depth) ++ str" : " ++
               pr_ev s' (Proofview.Goal.goal gl'));
        let hints' =
          if b && not (Context.Named.equal (Goal.hyps gl') (Goal.hyps gl))
          then
            let st = Hint_db.transparent_state info.search_hints in
            make_autogoal_hints info.search_only_classes ~st gl'
          else info.search_hints
        in
        let dep' = info.search_dep || Proofview.unifiable s' (Goal.goal gl') gls in
        let info' =
          { search_depth = succ j :: i :: info.search_depth;
            last_tac = pp;
            search_dep = dep';
            search_only_classes = info.search_only_classes;
            search_hints = hints';
            search_cut = derivs }
        in kont info' }
      in
      let rec result (shelf, ()) i k =
        foundone := true;
        Proofview.Unsafe.tclGETGOALS >>= fun gls ->
        let j = List.length gls in
        (if !typeclasses_debug > 0 then
           Feedback.msg_debug
             (pr_depth (i :: info.search_depth) ++ str": " ++ Lazy.force pp
              ++ str" on" ++ spc () ++ pr_ev s (Proofview.Goal.goal gl)
              ++ str", " ++ int j ++ str" subgoal(s)" ++
                (Option.cata (fun k -> str " in addition to the first " ++ int k)
                             (mt()) k)));
        let res =
          if j = 0 then tclUNIT ()
          else tclDISPATCH
                 (List.init j (fun j' -> (tac_of gls i (Option.default 0 k + j))))
        in
        let finish sigma =
          let filter ev =
            try
              let evi = Evd.find_undefined sigma ev in
              if info.search_only_classes then
                Some (ev, is_class_type sigma (Evd.evar_concl evi))
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
            let shelved, goals = List.split_when (fun (ev, s) -> s) remaining in
            let shelved = List.map fst shelved and goals = List.map fst goals in
            if !typeclasses_debug > 1 then
              Feedback.msg_debug
                (str"Adding shelved subgoals to the search: " ++
                   prlist_with_sep spc (pr_ev sigma) goals);
            shelve_goals shelved <*>
              (if List.is_empty goals then tclUNIT ()
               else with_shelf (Unsafe.tclNEWGOALS goals) >>=
                      fun s -> result s i (Some (Option.default 0 k + j)))
          end
        in res <*> tclEVARMAP >>= finish
      in
      if path_matches derivs [] then aux e tl
      else ortac
             (with_shelf tac >>= fun s ->
              let i = !idx in incr idx; result s i None)
             (fun e' -> aux (merge_exceptions e e') tl)
    and aux e = function
      | x :: xs -> onetac e x xs
      | [] ->
         if !foundone == false && !typeclasses_debug > 0 then
           Feedback.msg_debug
             (pr_depth info.search_depth ++ str": no match for " ++
                Printer.pr_constr_env (Goal.env gl) s concl ++
                spc () ++ str ", " ++ int (List.length poss) ++
                str" possibilities");
         match e with
         | (ReachedLimitEx,ie) -> Proofview.tclZERO ~info:ie ReachedLimitEx
         | (_,ie) -> Proofview.tclZERO ~info:ie NotApplicableEx
    in
    if backtrack then aux (NotApplicableEx,Exninfo.null) poss
    else tclONCE (aux (NotApplicableEx,Exninfo.null) poss)

  let hints_tac hints info kont : unit Proofview.tactic =
    Proofview.Goal.nf_enter
      { enter = fun gl -> hints_tac_gl hints info kont gl }

  let intro_tac info kont gl =
    let open Proofview in
    let open Proofview.Notations in
    let env = Goal.env gl in
    let sigma = Goal.sigma gl in
    let s = Sigma.to_evar_map sigma in
    let decl = Tacmach.New.pf_last_hyp gl in
    let hint =
      make_resolve_hyp env s (Hint_db.transparent_state info.search_hints)
                       (true,false,false) info.search_only_classes None decl in
    let ldb = Hint_db.add_list env s hint info.search_hints in
    let info' =
      { info with search_hints = ldb; last_tac = lazy (str"intro") }
    in kont info'

  let intro info kont =
    Proofview.tclBIND Tactics.intro
     (fun _ -> Proofview.Goal.nf_enter { enter = fun gl -> intro_tac info kont gl })

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
    let open Proofview.Notations in
    let dep = dep || Proofview.unifiable sigma (Goal.goal gl) gls in
    let info = make_autogoal ?st only_classes dep (cut_of_hints hints) i gl in
    search_tac hints depth 1 info

  exception HasShelvedGoals

  let search_tac ?(st=full_transparent_state) only_classes dep hints depth =
    let open Proofview in
    let tac sigma gls i =
      Goal.nf_enter
        { enter = fun gl ->
          search_tac_gl ~st only_classes dep hints depth (succ i) sigma gls gl }
    in
      Proofview.Unsafe.tclGETGOALS >>= fun gls ->
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

  let eauto_tac ?(st=full_transparent_state) ~only_classes ~depth ~dep hints =
    let tac =
      let search = search_tac ~st only_classes dep hints in
      if get_typeclasses_iterative_deepening () then
        match depth with
        | None -> fix_iterative search
        | Some l -> fix_iterative_limit l search
      else
        let depth = match depth with None -> -1 | Some d -> d in
        search depth
    in
    let error (e, ie) =
      match e with
      | ReachedLimitEx ->
         Tacticals.New.tclFAIL 0 (str"Proof search reached its limit")
      | NotApplicableEx ->
         Tacticals.New.tclFAIL 0 (str"Proof search failed" ++
                                    (if Option.is_empty depth then mt()
                                     else str" without reaching its limit"))
      | e -> Proofview.tclZERO ~info:ie e
    in Proofview.tclORELSE tac error

  let run_on_evars ?(unique=false) p evm tac =
    match evars_to_goals p evm with
    | None -> None (* This happens only because there's no evar having p *)
    | Some (goals, evm') ->
       let goals =
         if !typeclasses_dependency_order then
           top_sort evm' goals
         else List.map (fun (ev, _) -> ev) (Evar.Map.bindings goals)
       in
       let fgoals = Evd.future_goals evm in
       let pgoal = Evd.principal_future_goal evm in
       let _, pv = Proofview.init evm' [] in
       let pv = Proofview.unshelve goals pv in
       try
         let (), pv', (unsafe, shelved, gaveup), _ =
           Proofview.apply (Global.env ()) tac pv
         in
         if Proofview.finished pv' then
           let evm' = Proofview.return pv' in
           assert(Evd.fold_undefined (fun ev _ acc ->
                      let okev = Evd.mem evm ev || List.mem ev shelved in
                      if not okev then
                        Feedback.msg_debug
                          (str "leaking evar " ++ int (Evar.repr ev) ++
                             spc () ++ pr_ev evm' ev);
                      acc && okev) evm' true);
           let evm' = Evd.restore_future_goals evm' (shelved @ fgoals) pgoal in
           let evm' = evars_reset_evd ~with_conv_pbs:true ~with_univs:false evm' evm in
           Some evm'
         else raise Not_found
       with Logic_monad.TacticFailure _ -> raise Not_found

  let eauto depth only_classes unique dep st hints p evd =
    let eauto_tac = eauto_tac ~st ~only_classes ~depth ~dep hints in
    let res = run_on_evars ~unique p evd eauto_tac in
    match res with
    | None -> evd
    | Some evd' -> evd'
  (* TODO treat unique solutions *)

  let typeclasses_eauto ?depth unique st hints p evd =
    eauto depth true unique false st hints p evd
  (** Typeclasses eauto is an eauto which tries to resolve only
      goals of typeclass type, and assumes that the initially selected
      evars in evd are independent of the rest of the evars *)

  let typeclasses_resolve debug depth unique p evd =
    let db = searchtable_map typeclasses_db in
    typeclasses_eauto ?depth unique (Hint_db.transparent_state db) [db] p evd
end

(** Binding to either V85 or Search implementations. *)
let eauto depth ~only_classes ~st ~dep dbs =
  Search.eauto_tac ~st ~only_classes ~depth ~dep dbs

let typeclasses_eauto ?(only_classes=false) ?(st=full_transparent_state)
                      ~depth dbs =
  let dbs = List.map_filter
              (fun db -> try Some (searchtable_map db)
                      with e when CErrors.noncritical e -> None)
              dbs
  in
  let st = match dbs with x :: _ -> Hint_db.transparent_state x | _ -> st in
  let depth = match depth with None -> get_typeclasses_depth () | Some l -> Some l in
  if get_typeclasses_compat () = Flags.V8_5 then
    Tacticals.New.tclORELSE (Proofview.V82.tactic
       (V85.eauto85 depth ~only_classes ~st dbs))
     (Proofview.Goal.nf_enter ({ enter = fun gl ->
       Tacticals.New.tclFAIL 0 (str" typeclasses eauto failed on: " ++
                    Goal.pr_goal (Proofview.Goal.goal gl))}))
  else eauto depth ~only_classes ~st ~dep:true dbs

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

let evar_dependencies evm p =
  Evd.fold_undefined
    (fun ev evi _ ->
      let evars = Evar.Set.add ev (Evarutil.undefined_evars_of_evar_info evm evi)
      in Intpart.union_set evars p)
    evm ()

(** [split_evars] returns groups of undefined evars according to dependencies *)

let split_evars evm =
  let p = Intpart.create () in
  evar_dependencies evm p;
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
  let evd = Evarutil.nf_evar_map_undefined evd in
  let is_part ev = match comp with
  | None -> true
  | Some s -> Evar.Set.mem ev s
  in
  let fold ev evi (found, accu) =
    let ev_class = class_of_constr evi.evar_concl in
    if not (Option.is_empty ev_class) && is_part ev then
      (* focus on one instance if only one was searched for *)
      if not found then (true, Some ev)
      else (found, None)
    else (found, accu)
   in
  let (_, ev) = Evd.fold_undefined fold evd (true, None) in
    Pretype_errors.unsatisfiable_constraints
      (Evarutil.nf_env_evar evd env) evd ev comp

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
  let split = if do_split then split_evars oevd else [Evar.Set.empty] in
  let in_comp comp ev = if do_split then Evar.Set.mem ev comp else true
  in
  let rec docomp evd = function
    | [] -> revert_resolvability oevd evd
    | comp :: comps ->
      let p = select_and_update_evars p oevd (in_comp comp) in
      try
        let evd' =
          if get_typeclasses_compat () = Flags.Current then
            Search.typeclasses_resolve debug depth unique p evd
          else
            V85.resolve_all_evars_once debug depth unique p evd
        in
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
    try Evarconv.consider_remaining_unif_problems
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

let resolve_one_typeclass env ?(sigma=Evd.empty) gl unique =
  let nc, gl, subst, _, _ = Evarutil.push_rel_context_to_named_context env gl in
  let (gl,t,sigma) =
    Goal.V82.mk_goal sigma nc gl Store.empty in
  let gls = { it = gl ; sigma = sigma; } in
  let hints = searchtable_map typeclasses_db in
  let st = Hint_db.transparent_state hints in
  let depth = get_typeclasses_depth () in
  let gls' =
    if get_typeclasses_compat () = Flags.Current then
      try
        Proofview.V82.of_tactic
        (Search.eauto_tac ~st ~only_classes:true ~depth [hints] ~dep:true) gls
      with Refiner.FailError _ -> raise Not_found
    else V85.eauto85 depth ~st [hints] gls
  in
  let evd = sig_sig gls' in
  let t' = let (ev, inst) = destEvar t in
    mkEvar (ev, Array.of_list subst)
  in
  let term = Evarutil.nf_evar evd t' in
    evd, term

let _ =
  Hook.set Typeclasses.solve_one_instance_hook
    (fun x y z w -> resolve_one_typeclass x ~sigma:y z w)

(** Take the head of the arity of a constr.
    Used in the partial application tactic. *)

let rec head_of_constr t =
  let t = strip_outer_cast(collapse_appl t) in
    match kind_of_term t with
    | Prod (_,_,c2)  -> head_of_constr c2
    | LetIn (_,_,_,c2) -> head_of_constr c2
    | App (f,args)  -> head_of_constr f
    | _      -> t

let head_of_constr h c =
  let c = head_of_constr c in
  letin_tac None (Name h) c None Locusops.allHyps

let not_evar c = match kind_of_term c with
| Evar _ -> Tacticals.New.tclFAIL 0 (str"Evar")
| _ -> Proofview.tclUNIT ()

let is_ground c gl =
  if Evarutil.is_ground_term (project gl) c then tclIDTAC gl
  else tclFAIL 0 (str"Not ground") gl

let autoapply c i gl =
  let flags = auto_unif_flags Evar.Set.empty
    (Hints.Hint_db.transparent_state (Hints.searchtable_map i)) in
  let cty = pf_unsafe_type_of gl c in
  let ce = mk_clenv_from gl (c,cty) in
  let tac = { enter = fun gl -> (unify_e_resolve false flags).enter gl
    ((c,cty,Univ.ContextSet.empty),0,ce) } in
  Proofview.V82.of_tactic (Proofview.Goal.nf_enter tac) gl
