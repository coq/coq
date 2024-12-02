(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Univ
open UnivSubst
open InferCumulativity

let _debug_minim, debug = CDebug.create_full ~name:"univMinim" ()
let _debug_minim_each, debug_each = CDebug.create_full ~name:"univMinim_each" ()
let _debug_minim_each, debug_graph = CDebug.create_full ~name:"univMinim_graph" ()
let switch_minim, _ = CDebug.create_full ~name:"switchminim" ()
let () = CDebug.set_flag switch_minim true

(* To disallow minimization to Set *)
let { Goptions.get = get_set_minimization } =
  Goptions.declare_bool_option_and_ref
    ~key:["Universe";"Minimization";"ToSet"]
    ~value:true
    ()

(** Simplification *)

(** Precondition: flexible <= ctx *)

let choose_expr s = LevelExpr.Set.max_elt s

let choose_canonical ctx flexible s =
  let local, global = LevelExpr.Set.partition (fun (l, _k) -> Level.Set.mem l ctx) s in
  let flexible, rigid = LevelExpr.Set.partition (fun (l, _k) -> flexible l) local in
    (* If there is a global universe in the set, choose it *)
    if not (LevelExpr.Set.is_empty global) then
      let canon = choose_expr global in
        canon, (LevelExpr.Set.remove canon global, rigid, flexible)
    else (* No global in the equivalence class, choose a rigid one *)
        if not (LevelExpr.Set.is_empty rigid) then
          let canon = choose_expr rigid in
            canon, (global, LevelExpr.Set.remove canon rigid, flexible)
        else (* There are only flexible universes in the equivalence
                 class, choose an arbitrary one. *)
          let canon = choose_expr flexible in
          canon, (global, rigid, LevelExpr.Set.remove canon flexible)

let variance_info u us (variances : InferCumulativity.variances) =
  let open UVars.Variance in
  match Level.Map.find_opt u variances with
  | None -> if UnivFlex.mem u us then Irrelevant, Irrelevant, false, None else Invariant, Invariant, true, None
  | Some occs ->
    let termv, typev, principal = term_type_variances occs in
    Option.default Irrelevant termv, Option.default Irrelevant typev, principal, occs.infer_under_impred_qvars

let _warn_not_minimizable u =
  Feedback.msg_notice Pp.(str"Universe " ++ Level.raw_pr u ++ str" is not mimimizable as its lower bound \
       is not expressible in terms of other universes")

let update_variance (variances : InferCumulativity.variances) l l' =
  match Level.Map.find_opt l variances with
  | None -> variances
  | Some loccs ->
    let upd = function None -> None | Some l'occs -> Some (sup_occs loccs l'occs) in
    Level.Map.update l' upd variances

let update_variances (variances : InferCumulativity.variances) l ls =
  match Level.Map.find_opt l variances with
  | None -> variances
  | Some loccs ->
    let update_one l' variances =
      let upd = function None -> None | Some l'occs -> Some (sup_occs loccs l'occs) in
      Level.Map.update l' upd variances
    in
    Level.Set.fold update_one ls variances

let set_variance (variances : InferCumulativity.variances) l v =
  Level.Map.add l v variances

let sup_variances (variances : InferCumulativity.variances) ls =
  let fold l acc =
    match Level.Map.find_opt l variances with
    | None -> acc
    | Some occs -> sup_occs occs acc
  in
  Level.Set.fold fold ls InferCumulativity.default_occ

let update_univ_subst (ctx, us, variances, graph) subst =
  let us = List.fold_right (fun (l, u) -> UnivFlex.define l u) subst us in
  let ctx = List.fold_right (fun (l, _) -> Level.Set.remove l) subst ctx in
  let variances = List.fold_right (fun (l, u) variances -> Level.Map.remove l (update_variances variances l (Univ.Universe.levels u))) subst variances in
  (ctx, us, variances, graph)

let pr_subst =
  let open Pp in
  let pr_subst (l, u) = Level.raw_pr l ++ str " := " ++ Universe.pr Level.raw_pr u in
  prlist_with_sep spc pr_subst

let subst_of_equivalences us =
  List.filter_map (fun (l, le) ->
    if UnivFlex.mem l us then
      if not (UnivFlex.is_defined l us) then Some (l, Universe.of_expr le)
      else None
    else None)

let instantiate_variable l (b : Universe.t) (ctx, us, variances, graph) =
  debug Pp.(fun () -> str"Instantiating " ++ Level.raw_pr l ++ str " with " ++ Universe.pr Level.raw_pr b);
  debug Pp.(fun () -> str"Context: " ++ Level.Set.pr Level.raw_pr ctx);
  debug_graph Pp.(fun () -> str"Model: " ++ UGraph.pr_model ~local:true graph);
  let graph, equivs = UGraph.set l b graph in
  let subst = subst_of_equivalences us equivs in
  debug Pp.(fun () -> str "Set affected also: " ++ pr_subst subst);
  debug_graph Pp.(fun () -> str"Model after set: " ++ UGraph.pr_model ~local:true graph);
  update_univ_subst (ctx, us, variances, graph) ((l, b) :: subst)

let update_equivs_bound (_, us, _, _ as acc) l u equivs =
  update_univ_subst acc ((l, u) :: subst_of_equivalences us equivs)

let simplify_variables partial ctx us variances graph =
  let dom = UnivFlex.domain us in
  debug_each Pp.(fun () -> str"Simplifying variables with " ++ (if partial then str"partial" else str"non-partial") ++ str" information about the definition");
  let minimize u (ctx, us, variances, graph) =
    match UGraph.minimize u graph with
    | HasSubst (graph, equivs, lbound) ->
      debug_each Pp.(fun () -> str"Minimizing " ++ Level.raw_pr u ++ str" resulted in lbound: " ++ Universe.pr Level.raw_pr lbound ++ str" and graph " ++ UGraph.pr_model graph);
      update_equivs_bound (ctx, us, variances, graph) u lbound equivs
    | NoBound | CannotSimplify -> (ctx, us, variances, graph)
  in
  let collapse_to_zero u acc =
    try instantiate_variable u Universe.type0 acc
    with UGraph.InconsistentEquality | UGraph.OccurCheck -> acc
  in
  let arbitrary u (ctx, us, variances, graph as acc) =
    match UGraph.minimize u graph with
    | HasSubst (graph, equivs, lbound) ->
      debug_each Pp.(fun () -> str"Minimizing " ++ Level.raw_pr u ++ str" resulted in lbound: " ++ Universe.pr Level.raw_pr lbound ++ str" and graph " ++ UGraph.pr_model graph);
      update_equivs_bound (ctx, us, variances, graph) u lbound equivs
    | NoBound -> (* Not bounded and not appearing anywhere: can collapse *)
      collapse_to_zero u acc
    | CannotSimplify -> acc
  in
  let maximize u (ctx, us, variances, graph as acc) =
    match UGraph.maximize u graph with
    | HasSubst (graph, equivs, ubound) ->
      debug_each Pp.(fun () -> str"Maximizing " ++ Level.raw_pr u ++ str" resulted in ubound: " ++ Universe.pr Level.raw_pr ubound ++ str" and graph " ++ UGraph.pr_model graph);
      update_equivs_bound (ctx, us, variances, graph) u ubound equivs
    | NoBound | CannotSimplify -> acc
  in
  let simplify_min u (ctx, us, variances, graph as acc) =
    (* u is an undefined flexible variable, lookup its variance information *)
    let term_variance, type_variance, principal, impred = variance_info u us variances in
    let open UVars.Variance in
    if not principal then
      (* The universe does not occur in the principal type of the application where it appears *)
      match type_variance with
      | Irrelevant -> arbitrary u acc
      | Covariant -> minimize u acc
      | Contravariant -> maximize u acc
      | Invariant -> acc
    else
      match term_variance, type_variance with
      | Irrelevant, Irrelevant -> arbitrary u acc
      | (Covariant | Irrelevant), Covariant when not partial -> minimize u acc
      | _, _ ->
        match impred with
        | None -> (* Used in some predicative contexts *) acc
        | Some qs ->
          if Sorts.QVar.Set.is_empty qs then collapse_to_zero u acc
          else acc
  in
  let fold_min u (ctx, us, variances, graph as acc) =
    if UnivFlex.is_defined u us then acc
    else simplify_min u acc
  in
  let acc = Level.Set.fold fold_min dom (ctx, us, variances, graph) in
  let simplify_max u (ctx, us, variances, graph as acc) =
    (* u is an undefined flexible variable, lookup its variance information *)
    let term_variance, type_variance, principal, _impred_qvars = variance_info u us variances in
    if not principal then
      maximize u acc
    else
      let open UVars.Variance in
      match term_variance, type_variance with
      | (Covariant | Irrelevant), Contravariant when not partial -> maximize u acc
      | _, _ -> acc
  in
  let fold_max u (ctx, us, variances, graph as acc) =
    if UnivFlex.is_defined u us then acc
    else simplify_max u acc
  in
  Level.Set.fold fold_max dom acc


module UPairs = OrderedType.UnorderedPair(Universe)
module UPairSet = Set.Make (UPairs)

type extra = {
  weak_constraints : UPairSet.t;
  above_prop : Level.Set.t;
}

let empty_extra = {
  weak_constraints = UPairSet.empty;
  above_prop = Level.Set.empty;
}

let extra_union a b = {
  weak_constraints = UPairSet.union a.weak_constraints b.weak_constraints;
  above_prop = Level.Set.union a.above_prop b.above_prop;
}

let _pr_partition prl m =
  let open Pp in
  prlist_with_sep spc (fun s ->
    str "{" ++ LevelExpr.Set.fold (fun lk acc -> LevelExpr.pr prl lk ++ str", " ++ acc) s (mt()) ++ str "}" ++ fnl ())
    m

(** Turn max(l, l') <= u constraints into { l <= u, l' <= u } constraints *)
let decompose_constraints cstrs =
  let fold (l, d, r as cstr) acc =
    match d with
    | Eq -> Constraints.add cstr acc
    | Le ->
      match Universe.repr l with
      | [] -> assert false
      | [_] -> Constraints.add cstr acc
      | l -> List.fold_left (fun acc le -> enforce (Universe.of_list [le]) d r acc) acc l
  in Constraints.fold fold cstrs Constraints.empty

let simplify_cstr (l, d, r) =
  (Universe.unrepr (Universe.repr l), d, Universe.unrepr (Universe.repr r))


let partition_to_constraints partition cstrs =
  let fold le le' cstrs = Constraints.add (Universe.of_expr le, Eq, Universe.of_expr le') cstrs in
  List.fold_left (fun cstrs eqs ->
    let canon = LevelExpr.Set.choose eqs in
    let rest = LevelExpr.Set.remove canon eqs in
    LevelExpr.Set.fold (fold canon) rest cstrs) cstrs partition

let new_minimize_weak_pre us weak smallles =
  UPairSet.fold (fun (u,v) smallles ->
    let norm = Universe.subst_fn (level_subst_of (UnivFlex.normalize_univ_variable us)) in
    let u = norm u and v = norm v in
    if (Universe.is_type0 u || Universe.is_type0 v) then begin
      if get_set_minimization() then begin
        if Universe.is_type0 u then (Constraints.add (u,Le,v) smallles)
        else (Constraints.add (v,Le,u) smallles)
      end else smallles
    end else smallles)
    weak smallles

let new_minimize_weak ctx us weak (g, variances) =
  UPairSet.fold (fun (u,v) (ctx, us, variances, g as acc) ->
    let norm = Universe.subst_fn (level_subst_of (UnivFlex.normalize_univ_variable us)) in
    let u = norm u and v = norm v in
    if (Universe.is_type0 u || Universe.is_type0 v) then acc
    else
      let set_to a b =
        debug Pp.(fun () -> str"Minimize_weak: setting " ++ Level.raw_pr a ++ str" to " ++ Universe.pr Level.raw_pr b);
        let levels = Universe.levels b in
        let sup_variances = sup_variances variances (Level.Set.add a levels) in
        match InferCumulativity.term_type_variances sup_variances with
        | (None | Some UVars.Variance.Irrelevant), (None | Some UVars.Variance.Irrelevant), false -> (* Irrelevant *)
          let variances =
            Level.Set.fold (fun bl variances -> set_variance variances bl sup_variances) levels variances
          in
          (try let g, equivs = UGraph.set a b g in
            update_equivs_bound (ctx, us, variances, g) a b equivs
          with UGraph.InconsistentEquality | UGraph.OccurCheck -> acc)
        | _, _, _ -> (* One universe is not irrelevant *)
          (ctx,us, variances, g)
      in
      let check_le a b = UGraph.check_constraint g (a,Le,b) in
      if check_le u v || check_le v u
      then acc
      else match Universe.level u with
      | Some u when UnivFlex.mem u us -> set_to u v
      | _ ->
        match Universe.level v with
        | Some v when UnivFlex.mem v us -> set_to v u
        | _ -> acc)
    weak (ctx, us, variances, g)


let normalize_context_set ~lbound ~variances ~partial g ctx (us:UnivFlex.t) ?binders {weak_constraints=weak;above_prop} =
  let prl = UnivNames.pr_level_with_global_universes ?binders in
  debug Pp.(fun () -> str "Minimizing context: " ++ pr_universe_context_set prl ctx ++ spc () ++
    UnivFlex.pr Level.raw_pr us ++ fnl () ++
    str"Variances: " ++ pr_variances prl variances ++ fnl () ++
    str"Weak constraints " ++
    prlist_with_sep spc (fun (u,v) -> Universe.pr Level.raw_pr u ++ str" ~ " ++ Universe.pr Level.raw_pr v)
     (UPairSet.elements weak) ++
     (if partial then str"In partial mode" else str"In non-partial mode") );
  debug_graph Pp.(fun () ->
     str"Graph: " ++ UGraph.pr_model g);
  if CDebug.get_flag _debug_minim then
    if not (Level.Set.is_empty (Univ.ContextSet.levels ctx)) && InferCumulativity.is_empty_variances variances then
      Feedback.msg_debug Pp.(str"normalize_context_set called with empty variance information");
  let (ctx, csts) = ContextSet.levels ctx, ContextSet.constraints ctx in
  (* Keep the Prop/Set <= i constraints separate for minimization *)
  let csts = decompose_constraints csts in
  let smallles, csts =
    Constraints.partition (fun (l,d,r) -> d == Le && Universe.is_type0 l) csts
  in
  (* Process weak constraints: when one side is flexible and the 2
     universes are unrelated unify them. *)
  let smallles, csts, g, variances =
    (new_minimize_weak_pre us weak smallles, csts, g, variances)
  in
  let smallles = match (lbound : UGraph.Bound.t) with
    | Prop -> smallles
    | Set when get_set_minimization () ->
      Constraints.filter (fun (l,d,r) -> match Universe.level r with Some r -> UnivFlex.mem r us | None -> false) smallles
    | Set -> Constraints.empty (* constraints Set <= u may be dropped *)
  in
  let smallles = if get_set_minimization() then
      let fold u accu = if UnivFlex.mem u us then enforce_leq Universe.type0 (Universe.make u) accu else accu in
      Level.Set.fold fold above_prop smallles
    else smallles
  in
  let graph =
    (* We first put constraints in a normal-form: all self-loops are collapsed
       to equalities. *)
    let g = UGraph.clear_constraints g in
    let g = UGraph.set_local g in
    (* use lbound:Set to collapse [u <= v <= Set] into [u = v = Set] *)
    let g = Level.Set.fold (fun v g -> fst (UGraph.enforce_constraint (Universe.type0, Le, Universe.make v) g))
        ctx g
    in
    let add_soft u g =
      if not (Level.is_set u || Level.Set.mem u ctx)
      then try UGraph.add_universe ~lbound:Set ~strict:false u g with UGraph.AlreadyDeclared -> g
      else g
    in
    let g = Constraints.fold
        (fun (l, d, r) g ->
          let levels = Level.Set.union (Universe.levels l) (Universe.levels r) in
          Level.Set.fold add_soft levels g)
        csts g
    in
    debug Pp.(fun () -> str "Merging constraints: " ++ pr_universe_context_set prl (ctx, csts));
    let atomic, nonatomic =
     Constraints.partition (fun (_l, d, r) -> not (d == Le && not (Univ.Universe.is_level r))) csts in
    let g, _ = UGraph.merge_constraints atomic g in
    Constraints.fold (fun cstr g ->
      if UGraph.check_constraint g cstr then g
      else fst (UGraph.enforce_constraint (simplify_cstr cstr) g))
      nonatomic g
  in
  (* debug Pp.(fun () -> str "Local graph: " ++ UGraph.pr_model graph); *)
  let locals, cstrs, partition = UGraph.constraints_of_universes ~only_local:true graph in
  (* debug Pp.(fun () -> str "Local universes: " ++ pr_universe_context_set prl (locals, cstrs)); *)
  (* debug Pp.(fun () -> str "New universe context: " ++ pr_universe_context_set prl (ctx, cstrs)); *)
  (* debug Pp.(fun () -> str "Partition: " ++ pr_partition prl partition); *)
(* Ignore constraints from lbound:Set *)
  let noneqs =
    Constraints.filter
      (fun (l,d,r) -> not (d == Le && Universe.is_type0 l))
      cstrs
  in
  (* Put back constraints [Set <= u] from type inference *)
  let noneqs = Constraints.union noneqs smallles in
  let flex x = UnivFlex.mem x us in
  let ctx, us, variances, eqs = List.fold_left (fun (ctx, us, variances, cstrs) eqs ->
      let canon, (global, rigid, flexible) = choose_canonical ctx flex eqs in
      (* Add equalities for globals which can't be merged anymore. *)
      let canonu = Universe.of_expr canon in
      let cstrs = LevelExpr.Set.fold (fun g cst ->
          enforce_eq canonu (Universe.of_expr g) cst) global
          cstrs
      in
      (* Also add equalities for rigid variables *)
      let cstrs = LevelExpr.Set.fold (fun g cst ->
          enforce_eq canonu (Universe.of_expr g) cst) rigid cstrs
      in
      if UnivFlex.mem (fst canon) us then
        (* canon + k = l + k' ... <-> l = canon + k - k' (k' <= k by invariant of choose_canonical) *)
        let fold (f, k') (ctx, us, variances) =
          (Level.Set.remove f ctx, UnivFlex.define f (Universe.addn canonu (-k')) us,
           Level.Map.remove f (update_variance variances f (fst canon)))
        in
        let ctx, us, variances = LevelExpr.Set.fold fold flexible (ctx, us, variances) in
        ctx, us, variances, cstrs
      else
        if LevelExpr.Set.is_empty flexible then (ctx, us, variances, cstrs) else
        (* We need to find the max of canon and flexibles *)
        let (canon', canonk' as can') = LevelExpr.Set.max_elt flexible in
        let ctx, us, variances =
          let fold (f, k') (ctx, us, variances) =
            (Level.Set.remove f ctx, UnivFlex.define f (Universe.addn (Universe.of_expr can') (-k')) us,
             Level.Map.remove f (update_variance variances f (fst can')))
          in
          LevelExpr.Set.fold fold (LevelExpr.Set.remove (canon', canonk') flexible) (ctx, us, variances)
        in
        if snd canon < canonk' then
          ctx, us, variances, enforce_eq canonu (Universe.of_expr can') cstrs
        else
          let ctx, us = Level.Set.remove canon' ctx, UnivFlex.define canon' (Universe.addn canonu (-canonk')) us in
          let variances = update_variance variances canon' (fst canon) in
          ctx, us, Level.Map.remove canon' variances, cstrs)
      (ctx, us, variances, Constraints.empty)
      partition
  in
  (* Noneqs is now in canonical form w.r.t. equality constraints,
     and contains only inequality constraints. *)
  let noneqs =
    let norm = (UnivFlex.normalize_universe us) in
    let fold (u,d,v) noneqs =
      let u = norm u and v = norm v in
      if Universe.equal u v then noneqs
      else Constraints.add (u,d,v) noneqs
    in
    Constraints.fold fold noneqs Constraints.empty
  in
  (* Now we construct the instantiation of each variable. *)
  debug Pp.(fun () -> str "Starting minimization with: " ++ pr_universe_context_set prl (ctx, noneqs) ++
    UnivFlex.pr Level.raw_pr us);
  let ctx', us, variances, noneqs =
    let smalllesu = Constraints.fold (fun (l, d, r) acc ->
      match Universe.level r with Some r -> Level.Set.add r acc | None -> acc) smallles Level.Set.empty in
    (* debug Pp.(fun () -> str"Model before removal: " ++ UGraph.pr_model graph); *)
    let graph = UnivFlex.fold (fun l ~is_defined graph ->
      if not is_defined && not (Level.Set.mem l smalllesu) then
        (debug Pp.(fun () -> str"Removing " ++ Level.raw_pr l ++ str" -> Set constraints");
          UGraph.remove_set_clauses l graph)
      else graph)
      us graph
    in
    (* debug Pp.(fun () -> str"Model after removal: " ++ UGraph.pr_model graph); *)
    let ctx', us, variances, graph = simplify_variables partial ctx us variances graph in
    debug_graph Pp.(fun () -> str"Model after simplification: " ++ UGraph.pr_model graph ++ fnl () ++ UnivFlex.pr Level.raw_pr us);
    let ctx', us, variances, graph = new_minimize_weak ctx' us weak (graph, variances) in
    let locals, cstrs, partition = UGraph.constraints_of_universes ~only_local:true graph in
    let cstrs = partition_to_constraints partition cstrs in
    let cstrs =
      Constraints.filter
        (fun (l,d,r) -> not (d == Le && Universe.is_type0 l))
        cstrs
    in
    let cstrs = Constraints.union smallles cstrs in
    ctx', us, variances, cstrs
  in
  let us = UnivFlex.normalize us in
  let noneqs = UnivSubst.subst_univs_constraints (UnivFlex.normalize_univ_variable us) noneqs in
  let ctx = (ctx', Constraints.union noneqs eqs) in
  debug Pp.(fun () -> str "After minimization: " ++ pr_universe_context_set prl ctx ++ fnl () ++
    UnivFlex.pr Level.raw_pr us ++ fnl () ++
    str"VARIANCES: " ++ InferCumulativity.pr_variances Level.raw_pr variances);
  (us, variances), ctx
