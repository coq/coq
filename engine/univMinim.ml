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

let variance_info u flex (variances : InferCumulativity.variances) =
  let open UVars.Variance in
  match Level.Map.find_opt u variances with
  | None -> if Level.Set.mem u flex then Irrelevant, Irrelevant, Irrelevant, None else Invariant, Invariant, Invariant, None
  | Some occs ->
    let termv, typev, principal = term_type_variances occs in
    Option.default Irrelevant termv, Option.default Irrelevant typev, Option.default Irrelevant principal, occs.infer_under_impred_qvars

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

let update_univ_subst (ctx, flex, variances, graph) subst =
  let flex = List.fold_right (fun (l, u) -> Level.Set.remove l) subst flex in
  let ctx = List.fold_right (fun (l, _) -> Level.Set.remove l) subst ctx in
  let variances = List.fold_right (fun (l, u) variances -> Level.Map.remove l (update_variances variances l (Univ.Universe.levels u))) subst variances in
  (ctx, flex, variances, graph)

let pr_subst =
  let open Pp in
  let pr_subst (l, u) = Level.raw_pr l ++ str " := " ++ Universe.pr Level.raw_pr u in
  prlist_with_sep spc pr_subst

let subst_of_equivalences us =
  List.filter_map (fun (l, le) ->
    if Level.Set.mem l us then Some (l, Universe.of_expr le)
    else None)

let instantiate_variable l (b : Universe.t) (ctx, flex, variances, graph) =
  debug Pp.(fun () -> str"Instantiating " ++ Level.raw_pr l ++ str " with " ++ Universe.pr Level.raw_pr b);
  debug Pp.(fun () -> str"Context: " ++ Level.Set.pr Level.raw_pr ctx);
  debug_graph Pp.(fun () -> str"Model: " ++ UGraph.pr_model ~local:true graph);
  let graph, equivs = UGraph.set l b graph in
  let subst = subst_of_equivalences flex equivs in
  debug Pp.(fun () -> str "Set affected also: " ++ pr_subst subst);
  debug_graph Pp.(fun () -> str"Model after set: " ++ UGraph.pr_model ~local:true graph);
  update_univ_subst (ctx, flex, variances, graph) ((l, b) :: subst)

let update_equivs_bound (_, us, _, _ as acc) l u equivs =
  update_univ_subst acc ((l, u) :: subst_of_equivalences us equivs)

(** [partial]: we have type information only, not term information (i.e. Axiom, Definition/Lemma type only) *)
let simplify_variables solve_flexibles above_prop above_zero partial ctx flex variances graph =
  let open UVars.Variance in
  debug_each Pp.(fun () -> str"Simplifying variables with " ++ (if partial then str"partial" else str"non-partial") ++ str" information about the definition");
  let allowed_instance ~allow_collapse_to_zero u lbound =
    if Universe.is_type0 lbound then
      solve_flexibles || (get_set_minimization () &&
      (allow_collapse_to_zero || Level.Set.mem u above_prop || Level.Set.mem u above_zero))
    else true
  in
  let minimize ~allow_collapse_to_zero u (ctx, flex, variances, graph as acc) =
    match UGraph.minimize u graph with
    | HasSubst (graph, equivs, lbound) ->
      debug_each Pp.(fun () -> str"Minimizing " ++ Level.raw_pr u ++ str" resulted in lbound: " ++ Universe.pr Level.raw_pr lbound);
      if not (allowed_instance ~allow_collapse_to_zero u lbound) then acc
      else update_equivs_bound (ctx, flex, variances, graph) u lbound equivs
    | NoBound | CannotSimplify -> acc
  in
  let collapse_to_zero u acc =
    try instantiate_variable u Universe.type0 acc
    with Loop_checking.NotCanonical -> assert false
       | UGraph.InconsistentEquality | UGraph.OccurCheck -> acc
  in
  let maximize u (ctx, flex, variances, graph as acc) =
    match UGraph.maximize u graph with
    | HasSubst (graph, equivs, ubound) ->
      debug_each Pp.(fun () -> str"Maximizing " ++ Level.raw_pr u ++ str" resulted in ubound: " ++ Universe.pr Level.raw_pr ubound);
      update_equivs_bound (ctx, flex, variances, graph) u ubound equivs
    | NoBound | CannotSimplify -> acc
  in
  let arbitrary ~allow_collapse_to_zero u (ctx, flex, variances, graph as acc) =
    match UGraph.minimize u graph with
      | HasSubst (graph, equivs, lbound) ->
        debug_each Pp.(fun () -> str"Minimizing " ++ Level.raw_pr u ++ str" resulted in lbound: " ++ Universe.pr Level.raw_pr lbound);
        if not (allowed_instance ~allow_collapse_to_zero u lbound) then acc
        else update_equivs_bound (ctx, flex, variances, graph) u lbound equivs
      | NoBound -> (* Not bounded and not appearing anywhere: can collapse *)
        if allow_collapse_to_zero && not (Level.Set.mem u above_prop) then collapse_to_zero u acc
        else maximize u acc
      | CannotSimplify -> maximize u acc
  in
  let simplify_impred u acc = function
    | None -> (* Unused variable *) acc
    | Some UVars.Predicative -> (* Used in some predicative contexts *) acc
    | Some (UVars.Impredicative qs) ->
      if not partial && Sorts.QVar.Set.is_empty qs then collapse_to_zero u acc
      else acc
  in
  let simplify_min u (ctx, flex, variances, graph as acc) =
    (* u is an undefined flexible variable, lookup its variance information *)
    let term_variance, type_variance, typing_variance, impred = variance_info u flex variances in
    debug_each Pp.(fun () -> str"Trying to minimize flexible " ++ Level.raw_pr u ++ str" arbitrarily, type variance: " ++ UVars.Variance.pr type_variance ++
      str " typing_variance: " ++ UVars.Variance.pr typing_variance);
    if typing_variance == Irrelevant then
      (* The universe does not occur relevantly in the principal type of the expressions where it appears *)
      match type_variance with
      | Irrelevant -> arbitrary ~allow_collapse_to_zero:true u acc
      | Covariant -> minimize ~allow_collapse_to_zero:false u acc
      | Contravariant -> acc (* Do not maximize at first, as it would break the template hacks with max (0, ...) *)
      | Invariant -> acc
    else
      match typing_variance with
      | Covariant when not partial -> minimize ~allow_collapse_to_zero:false u acc
      | Contravariant when not partial ->
        (* Do not maximize at first, as it would break template hacks with max(0,_) *)
        simplify_impred u acc impred
      | _ -> simplify_impred u acc impred

  in
  let (_, flex, _, _ as acc) = Level.Set.fold simplify_min flex (ctx, flex, variances, graph) in
  let simplify_max u (ctx, flex, variances, graph as acc) =
    (* u is an undefined flexible variable, lookup its variance information *)
    let term_variance, type_variance, typing_variance, _impred_qvars = variance_info u flex variances in
    if typing_variance == Irrelevant && type_variance == Irrelevant then
      maximize u acc
    else
      let open UVars.Variance in
      match term_variance, type_variance, typing_variance with
      | (Covariant | Irrelevant), Contravariant, (Irrelevant | Contravariant) when not partial -> maximize u acc
      | _, _, _ -> acc
  in
  let (_, flex, _, _ as acc) = Level.Set.fold simplify_max flex acc in
  let simplify_arbitrary u (ctx, flex, variances, graph as acc) =
    (* u is an undefined flexible variable, lookup its variance information *)
    let term_variance, type_variance, typing_variance, _impred_qvars = variance_info u flex variances in
    debug_each Pp.(fun () -> str"Simplifying flexible " ++ Level.raw_pr u ++ str" arbitrarily, type variance: " ++ UVars.Variance.pr type_variance ++
      str " typing_variance: " ++ UVars.Variance.pr typing_variance);
    match type_variance with
    | Irrelevant -> arbitrary ~allow_collapse_to_zero:true u acc
    | Covariant -> minimize ~allow_collapse_to_zero:true u acc
    | Contravariant -> maximize u acc
    | Invariant -> acc
  in
  if solve_flexibles then
    let fold_arbitrary u (ctx, flex, variances, graph as acc) =
      if not (Level.Set.mem u flex) then acc
      else simplify_arbitrary u acc
    in
    Level.Set.fold fold_arbitrary flex acc
  else acc

module UPairs = OrderedType.UnorderedPair(Universe)
module UPairSet = Set.Make (UPairs)

type extra = {
  weak_constraints : UPairSet.t;
  above_prop : Level.Set.t;
  above_zero : Level.Set.t;
}

let empty_extra = {
  weak_constraints = UPairSet.empty;
  above_prop = Level.Set.empty;
  above_zero = Level.Set.empty;
}

let extra_union a b = {
  weak_constraints = UPairSet.union a.weak_constraints b.weak_constraints;
  above_prop = Level.Set.union a.above_prop b.above_prop;
  above_zero = Level.Set.union a.above_zero b.above_zero;
}

let remove_from_extra removed a =
  let filter (l, r) =
    Level.Set.subset removed (Universe.levels l) ||
    Level.Set.subset removed (Universe.levels r)
  in
  { weak_constraints = UPairSet.filter filter a.weak_constraints;
    above_zero = Level.Set.diff a.above_zero removed;
    above_prop = Level.Set.diff a.above_prop removed; }

(* let pr_universe_set prl s =
  let open Pp in
  str "{" ++ LevelExpr.Set.fold (fun lk acc -> LevelExpr.pr prl lk ++ str", " ++ acc) s (mt()) ++ str "}"  *)

let pr_universe_set prl s =
  let open Pp in
  str "{" ++ Universe.Set.fold (fun lk acc -> Universe.pr prl lk ++ str", " ++ acc) s (mt()) ++ str "}"

let _pr_partition prl m =
  let open Pp in
  prlist_with_sep spc (fun s -> pr_universe_set prl s ++ fnl ()) m

let _pr_substitution prl m =
  let open Pp in
  prlist_with_sep spc (fun (l, u) -> prl l ++ str" := " ++ Universe.pr prl u ++ fnl ()) (Level.Map.bindings m)

let new_minimize_weak ctx flex weak (g, variances) =
  UPairSet.fold (fun (u,v) (ctx, flex, variances, g as acc) ->
    let norm = Universe.subst_fn (level_subst_of (UGraph.normalize g)) in
    let u = norm u and v = norm v in
    if (Universe.is_type0 u || Universe.is_type0 v) then acc
    else
      let set_to a b =
        let levels = Universe.levels b in
        let sup_variances = sup_variances variances (Level.Set.add a levels) in
        match InferCumulativity.term_type_variances sup_variances with
        | (None | Some UVars.Variance.Irrelevant), (None | Some UVars.Variance.Irrelevant),
          (None | Some Irrelevant) -> (* Irrelevant *)
          let variances =
            Level.Set.fold (fun bl variances -> set_variance variances bl sup_variances) levels variances
          in
          (try
            let g, equivs = UGraph.set a b g in
            debug Pp.(fun () -> str"Minimize_weak: setting " ++ Level.raw_pr a ++ str" to " ++ Universe.pr Level.raw_pr b);
            update_equivs_bound (ctx, flex, variances, g) a b equivs
           with Loop_checking.NotCanonical -> assert false
              | UGraph.InconsistentEquality | UGraph.OccurCheck -> acc)
        | _, _, _ -> (* One universe is not irrelevant *)
          (ctx, flex, variances, g)
      in
      let check_le a b = UGraph.check_constraint g (a,Le,b) in
      if check_le u v || check_le v u
      then acc
      else match Universe.level u with
      | Some u when Level.Set.mem u flex -> set_to u v
      | _ ->
        match Universe.level v with
        | Some v when Level.Set.mem v flex -> set_to v u
        | _ -> acc)
    weak (ctx, flex, variances, g)

let normalize_context_set ~solve_flexibles ~variances ~partial graph
  ~local_variables ~flexible_variables ?binders
  {weak_constraints=weak;above_prop; above_zero} =
  let prl = UnivNames.pr_level_with_global_universes ?binders in
  debug Pp.(fun () -> str "Minimizing context: " ++ UGraph.pr_universes prl (UGraph.repr ~local:true graph) ++ spc () ++
    str"Local variables: " ++ Level.Set.pr Level.raw_pr local_variables ++ fnl () ++
    str"Flexible variables: " ++ Level.Set.pr Level.raw_pr flexible_variables ++ fnl () ++
    str"Variances: " ++ pr_variances prl variances ++ fnl () ++
    str"Above prop: " ++ Level.Set.pr Level.raw_pr above_prop ++ fnl () ++
    str"Above zero: " ++ Level.Set.pr Level.raw_pr above_zero ++ fnl () ++
    str"Weak constraints " ++
    prlist_with_sep spc (fun (u,v) -> Universe.pr Level.raw_pr u ++ str" ~ " ++ Universe.pr Level.raw_pr v)
     (UPairSet.elements weak) ++ spc () ++
     (if partial then str"In partial mode" else str"In non-partial mode") ++ spc () ++
    if solve_flexibles then str "solving all flexibles" else str" solving flexibles respecting variances information");
  debug_graph Pp.(fun () ->
     str"Graph: " ++ UGraph.pr_model graph);
  if CDebug.get_flag _debug_minim then
    if not (Level.Set.is_empty local_variables) && InferCumulativity.is_empty_variances variances then
      Feedback.msg_debug Pp.(str"normalize_context_set called with empty variance information");
  (* Now we construct the instantiation of each variable. *)
  let local_variables, flexible_variables, variances, graph =
    (* debug Pp.(fun () -> str"Model after removal: " ++ UGraph.pr_model graph); *)
    let ctx', flex, variances, graph = simplify_variables solve_flexibles above_prop above_zero partial local_variables flexible_variables variances graph in
    debug_graph Pp.(fun () -> str"Model after simplification: " ++ UGraph.pr_model graph ++ fnl () ++ Level.Set.pr Level.raw_pr flex);
    new_minimize_weak ctx' flex weak (graph, variances)
  in
  debug Pp.(fun () ->
    str "After minimization: " ++ fnl () ++
    str"Local variables: " ++ Level.Set.pr Level.raw_pr local_variables ++ fnl () ++
    str"Flexible variables: " ++ Level.Set.pr Level.raw_pr flexible_variables ++ fnl () ++
    str"Variances: " ++ pr_variances prl variances ++ fnl () ++
    UGraph.pr_universes prl (UGraph.repr ~local:true graph));
  local_variables, flexible_variables, variances, graph
