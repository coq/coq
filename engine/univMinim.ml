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

type lowermap = int Level.Map.t

let lower_union =
  let merge k a b =
    match a, b with
    | Some _, None -> a
    | None, Some _ -> b
    | None, None -> None
    | Some l, Some r ->
       if Int.compare l r >= 0 then a
       else b
  in Level.Map.merge merge

let lower_add l c m =
  try let c' = Level.Map.find l m in
      if Int.compare c c' > 0 then
        Level.Map.add l c m
      else m
  with Not_found -> Level.Map.add l c m

let lower_of_list l =
  List.fold_left (fun acc (k,l) -> Level.Map.add l k acc) Level.Map.empty l

type lbound = { enforce : bool; inst: Universe.t; lower : lowermap }

module LBMap :
sig
  type t = private { lbmap : lbound Level.Map.t; lbrev : (Level.t * lowermap) Universe.Map.t }
  val empty : t
  val add : Level.t -> lbound -> t -> t
end =
struct
  type t = { lbmap : lbound Level.Map.t; lbrev : (Level.t * lowermap) Universe.Map.t }
  (* lbrev is uniquely given from lbmap as a partial reverse mapping *)
  let empty = { lbmap = Level.Map.empty; lbrev = Universe.Map.empty }
  let add u bnd m =
    let lbmap = Level.Map.add u bnd m.lbmap in
    let lbrev = m.lbrev in
    { lbmap; lbrev }
end

let compute_lbound left =
 (* The universe variable was not fixed yet.
    Compute its level using its lower bound. *)
  let sup l lbound =
    match lbound with
    | None -> Some l
    | Some l' -> Some (Universe.sup l l')
  in
    List.fold_left (fun lbound (k, l) -> sup (Universe.addn l k) lbound) None left

let instantiate u inst lower ~enforce (ctx, us, seen, insts, cstrs) =
  (debug Pp.(fun () -> str"Instantiating " ++ Level.raw_pr u ++ str" with " ++ Universe.pr Level.raw_pr inst);
  (Level.Set.remove u ctx, UnivFlex.define u inst us, seen,
   LBMap.add u {enforce;inst;lower} insts, cstrs),
  {enforce; inst; lower})


let instantiate_with_lbound u inst lower ~enforce (ctx, us, seen, insts, cstrs as acc) =
  let flexible = try not (UnivFlex.is_defined u us) with Not_found -> false in
  if enforce || not flexible then
    let uinst = Universe.make u in
    let cstrs' = enforce_leq inst uinst cstrs in
      (ctx, us, seen, LBMap.add u {enforce;inst;lower} insts, cstrs'),
      {enforce; inst; lower}
  else (* Actually instantiate *)
  instantiate u inst lower ~enforce acc

type constraints_map = (constraint_type * Level.Map.key) list Level.Map.t

let _pr_constraints_map (cmap:constraints_map) =
  let open Pp in
  Level.Map.fold (fun l cstrs acc ->
    Level.raw_pr l ++ str " => " ++
      prlist_with_sep spc (fun (d,r) -> pr_constraint_type d ++ Level.raw_pr r) cstrs ++
      fnl () ++ acc)
    cmap (mt ())

let not_lower lower (k,l) =
  (* We're checking if (k,l) is already implied by the lower
     constraints on some level u. If it represents l < u (k is > 0
     or k = 0 and i > 0, the i < 0 case is impossible due to
     invariants of Univ), and the lower constraints only have l <=
     u then it is not implied. *)
  Universe.exists
    (fun (l,i) ->
      let k = k + i in
       try let k' = Level.Map.find l lower in
         (* If k is stronger than the already implied lower
          * constraints we must keep it. *)
         k > k'
       with Not_found ->
         (* No constraint existing on l *) true) l

(** [enforce_uppers upper lbound cstrs] interprets [upper] as upper
   constraints to [lbound], adding them to [cstrs]. *)
let enforce_uppers upper lbound cstrs =
  List.fold_left (fun cstrs (k, r) -> (* lbound + k <= r *)
      if Int.equal k 0 then
        enforce_leq lbound (Universe.make r) cstrs
      else
        Constraints.add (Universe.addn lbound k, Le, Universe.make r) cstrs)
    cstrs upper

let is_set_increment u =
  match Universe.repr u with
  | [] -> false
  | [(l, k)] -> Level.is_set l
  | _ -> false

let term_type_variances_irrel u us (variances : InferCumulativity.variances) =
  let open UVars.Variance in
  match Level.Map.find_opt u variances with
  | None -> if UnivFlex.mem u us then Irrelevant, Irrelevant else Invariant, Invariant
  | Some occs ->
    let termv, typev = term_type_variances occs in
    Option.default Irrelevant termv, Option.default Irrelevant typev

(* let term_type_variances u us variances =
  match Level.Map.find_opt u variances with
  | None -> None, None
  | Some (_mode, pos) -> term_type_variances pos *)

let minimize_univ_variables partial ctx us variances left right cstrs =
  let left, lbounds =
    Level.Map.fold (fun r lower (left, lbounds as acc)  ->
      if UnivFlex.mem r us || not (Level.Set.mem r ctx) then acc
      else (* Fixed universe, just compute its glb for sharing *)
        let lbounds =
          match compute_lbound (List.map (fun (d,l) -> d, Universe.make l) lower) with
          | None -> lbounds
          | Some inst -> LBMap.add r {enforce=true; inst; lower=lower_of_list lower}
                                   lbounds
        in (Level.Map.remove r left, lbounds))
      left (left, LBMap.empty)
  in
  let rec instance (ctx, us, seen, insts, cstrs as acc) u =
    let acc, left, lower =
      match Level.Map.find u left with
      | exception Not_found -> acc, [], Level.Map.empty
      | l ->
        let acc, left, newlow, lower =
          List.fold_left
          (fun (acc, left, newlow, lower') (d, l) ->
           let acc', {enforce=enf;inst=l';lower} = aux acc l in
           let l' =
             if enf then Universe.make l
             else l'
           in acc', (d, l') :: left,
              lower_add l d newlow, lower_union lower lower')
          (acc, [], Level.Map.empty, Level.Map.empty) l
        in
        let left = CList.uniquize (List.filter (not_lower lower) left) in
        (acc, left, Level.Map.lunion newlow lower)
    in
    let term_variance, type_variance = term_type_variances_irrel u us variances in
    let instantiate_lbound lbound =
      if is_set_increment lbound && not (get_set_minimization()) then
        (* Minim to Set disabled, do not instantiate with Set *)
        instantiate_with_lbound u lbound lower ~enforce:(term_variance <> Irrelevant) acc
      else (* u is algebraic: we instantiate it with its lower bound, if any,
              or enforce the constraints if it is bounded from the top. *)
        let lower = Level.Set.fold Level.Map.remove (Universe.levels lbound) lower in
        instantiate_with_lbound u lbound lower ~enforce:false acc
    in
    let enforce_uppers ((ctx,us,seen,insts,cstrs), b as acc) =
      debug Pp.(fun () -> str"Looking for " ++ Level.raw_pr u ++ str" in right map");
      match Level.Map.find u right with
      | exception Not_found ->
        debug Pp.(fun () -> str"Looking for " ++ Level.raw_pr u ++ str" in right map: not found");
        acc
      | upper ->
        debug Pp.(fun () -> str"Enforcing upper bound of " ++ Universe.pr Level.raw_pr b.inst ++ str":" ++ Universe.pr Level.raw_pr (Universe.of_list (List.map (fun (d, r) -> r, d) upper)));
        let upper = List.filter (fun (d, r) -> not (UnivFlex.mem r us)) upper in
        debug Pp.(fun () -> str"Enforcing upper bound of " ++ Universe.pr Level.raw_pr b.inst ++ str":" ++ Universe.pr Level.raw_pr (Universe.of_list (List.map (fun (d, r) -> r, d) upper)));
        let cstrs = enforce_uppers upper b.inst cstrs in
        (ctx, us, seen, insts, cstrs), b
    in
    if not (Level.Set.mem u ctx)
    then enforce_uppers (acc, {enforce=true; inst=Universe.make u; lower})
    else
      let lbound = match compute_lbound left with None -> Universe.type0 | Some lbound -> lbound in
      debug Pp.(fun () -> str"Lower bound of " ++ Level.raw_pr u ++ str":" ++ Universe.pr Level.raw_pr lbound);
      if Level.Set.mem u (Universe.levels lbound) then
        (* let cstrs' = enforce_leq (Univ.univ_level_rem u lbound lbound) (Universe.make u) cstrs in *)
        (ctx, us, seen, insts, cstrs), { enforce = true; inst = Universe.make u; lower }
      else
      let open UVars.Variance in
      match term_variance, type_variance with
      | Irrelevant, Irrelevant ->
        (* This keeps principal typings, as instantiating to e.g. Set in a covariant position allows to use Set <= i for any i *)
        enforce_uppers (instantiate_lbound lbound)
      | (Covariant | Irrelevant), Covariant when not partial ->
        enforce_uppers (instantiate_lbound lbound)
      | _, _ ->
        if Universe.is_type0 lbound then enforce_uppers (acc, {enforce = true; inst = Universe.make u; lower})
        else enforce_uppers (instantiate_with_lbound u lbound lower ~enforce:true acc)
  and aux (ctx, us, seen, insts, cstrs as acc) u =
    debug Pp.(fun () -> str"Calling minim on " ++ Level.raw_pr u);
    try let lbound = Level.Map.find u insts.LBMap.lbmap in
      debug Pp.(fun () -> str" = " ++ Universe.pr Level.raw_pr lbound.inst);
      acc, lbound
    with Not_found ->
      debug Pp.(fun () -> str"Calling minim on " ++ Level.raw_pr u ++ str" not found");
      if Level.Set.mem u seen then
        (debug Pp.(fun () -> str"Calling minim on " ++ Level.raw_pr u ++ str" not found but seen");
        (* Loop in the contraints *)
        let bnd = {enforce=true; inst=Universe.make u; lower = Level.Map.empty} in
        acc, bnd)
      else
        (let acc = instance (ctx, us, Level.Set.add u seen, insts, cstrs) u in
          debug Pp.(fun () -> str"Calling minim on " ++ Level.raw_pr u ++ str" computed an instance");
          acc)
  in
  let (ctx, us, _, _, cstrs as acc) =
    UnivFlex.fold (fun u ~is_defined (ctx, us, seen, insts, cstrs as acc) ->
      if not is_defined then
        (debug Pp.(fun () -> str"Calling aux on " ++ Level.raw_pr u);
         fst (aux acc u))
      else Level.Set.remove u ctx, us, seen, insts, cstrs)
      us (ctx, us, Level.Set.empty, lbounds, cstrs)
  in
  let () = debug Pp.(fun () -> str"Maximising contravariant universes") in
  let instantiate_ubound (ctx, us, cstrs as acc) u ubound =
    match ubound with
    | Some [(0,e)] -> (* u + i <= e *)
      let univ = Universe.of_expr (e, 0) in
      let univ = UnivFlex.normalize_universe us univ in
      if Universe.mem u univ then acc else
      let () = debug Pp.(fun () -> str"Instantiating "++ Level.raw_pr u ++ str" with " ++ Level.raw_pr e) in
      (Level.Set.remove u ctx, UnivFlex.define u univ us,
       subst_univs_level_constraints (Level.Map.singleton u univ) cstrs)
    | _ ->  acc
  in
  let maximize_contravariant (ctx, us, cstrs as acc) u =
    let term_variance, type_variance = term_type_variances_irrel u us variances in
    match term_variance, type_variance with
    | (Covariant | Irrelevant), Contravariant when not partial ->
      let ubound = Level.Map.find_opt u right in
      instantiate_ubound acc u ubound
    | _, _ -> acc
  in
    UnivFlex.fold (fun u ~is_defined acc ->
      if not is_defined then maximize_contravariant acc u
      else acc) us (ctx, us, cstrs)

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
  if Level.Set.is_empty ls then InferCumulativity.default_occ else
  let def = Level.Set.choose ls in
  Level.Set.fold fold ls (Option.get (Level.Map.find_opt def variances))

let simplify_variables partial ctx us variances graph =
  let dom = UnivFlex.domain us in
  debug_each Pp.(fun () -> str"Simplifying variables with " ++ (if partial then str"partial" else str"non-partial") ++ str" information about the definition");
  let minimize u (ctx, us, variances, graph) =
    match UGraph.minimize u graph with
    | HasSubst (graph, lbound) ->
      debug_each Pp.(fun () -> str"Minimizing " ++ Level.raw_pr u ++ str" resulted in lbound: " ++ Universe.pr Level.raw_pr lbound ++ str" and graph " ++ UGraph.pr_model graph);
      let variances = update_variances variances u (Universe.levels lbound) in
      (Level.Set.remove u ctx, UnivFlex.define u lbound us,
       Level.Map.remove u variances, graph)
    | NoBound | CannotSimplify -> (ctx, us, variances, graph)
  in
  let collapse_to_set u (ctx, us, variances, graph as acc) =
    try
      let graph = UGraph.set u Universe.type0 graph in
      (Level.Set.remove u ctx, UnivFlex.define u Universe.type0 us,
       Level.Map.remove u variances, graph)
    with UGraph.InconsistentEquality -> acc
  in
  let arbitrary u (ctx, us, variances, graph as acc) =
    match UGraph.minimize u graph with
    | HasSubst (graph, lbound) ->
      debug_each Pp.(fun () -> str"Minimizing " ++ Level.raw_pr u ++ str" resulted in lbound: " ++ Universe.pr Level.raw_pr lbound ++ str" and graph " ++ UGraph.pr_model graph);
      let variances = update_variances variances u (Universe.levels lbound) in
      (Level.Set.remove u ctx, UnivFlex.define u lbound us,
       Level.Map.remove u variances, graph)
    | NoBound -> (* Not bounded and not appearing anywhere: can collapse *)
      collapse_to_set u acc
    | CannotSimplify -> acc
  in
  let maximize u (ctx, us, variances, graph as acc) =
    match UGraph.maximize u graph with
    | HasSubst (graph, ubound) ->
      debug_each Pp.(fun () -> str"Maximizing " ++ Level.raw_pr u ++ str" resulted in ubound: " ++ Universe.pr Level.raw_pr ubound ++ str" and graph " ++ UGraph.pr_model graph);
      let variances = update_variances variances u (Universe.levels ubound) in
      (Level.Set.remove u ctx, UnivFlex.define u ubound us,
       Level.Map.remove u variances, graph)
    | NoBound | CannotSimplify -> acc
  in
  let simplify_min u (ctx, us, variances, graph as acc) =
    (* u is an undefined flexible variable, lookup its variance information *)
    let term_variance, type_variance = term_type_variances_irrel u us variances in
    let open UVars.Variance in
    match term_variance, type_variance with
    | Irrelevant, Irrelevant -> arbitrary u acc
    | (Covariant | Irrelevant), Covariant when not partial -> minimize u acc
    | _, _ -> acc
  in
  let fold_min u (ctx, us, variances, graph as acc) =
    if UnivFlex.is_defined u us then acc
    else simplify_min u acc
  in
  let acc = Level.Set.fold fold_min dom (ctx, us, variances, graph) in
  let simplify_max u (ctx, us, variances, graph as acc) =
    (* u is an undefined flexible variable, lookup its variance information *)
    let term_variance, type_variance = term_type_variances_irrel u us variances in
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

let add_list_map u t map =
  try
    let l = Level.Map.find u map in
    Level.Map.set u (t :: l) map
  with Not_found ->
    Level.Map.add u [t] map

let pr_partition prl m =
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


let minimize_weak us weak (smallles, csts, g, variances) =
  UPairSet.fold (fun (u,v) (smallles, csts, g, variances as acc) ->
    let norm = Universe.subst_fn (level_subst_of (UnivFlex.normalize_univ_variable us)) in
    let u = norm u and v = norm v in
    if (Universe.is_type0 u || Universe.is_type0 v) then begin
      if get_set_minimization() then begin
        if Universe.is_type0 u then (Constraints.add (u,Le,v) smallles,csts,g,variances)
        else (Constraints.add (v,Le,u) smallles,csts,g,variances)
      end else acc
    end else
      let set_to a b =
        let levels = Level.Set.add a (Universe.levels b) in
        let sup_variances = sup_variances variances levels in
        match InferCumulativity.term_type_variances sup_variances with
        | (None | Some UVars.Variance.Irrelevant), (None | Some UVars.Variance.Irrelevant) -> (* Irrelevant *)
          (smallles,
          Constraints.add (Universe.make a,Eq,b) csts,
          UGraph.enforce_constraint (Universe.make a,Eq,b) g,
          Level.Set.fold (fun bl variances -> set_variance variances bl sup_variances) levels variances)
        | _, _ -> (* One universe is not irrelevant *)
          (smallles, csts, g, variances)
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
    weak (smallles, csts, g, variances)

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
  UPairSet.fold (fun (u,v) (ctx, us, g, variances as acc) ->
    let norm = Universe.subst_fn (level_subst_of (UnivFlex.normalize_univ_variable us)) in
    let u = norm u and v = norm v in
    if (Universe.is_type0 u || Universe.is_type0 v) then begin
      if get_set_minimization() then begin
        if Universe.is_type0 u then (ctx,us,g,variances)
        else (ctx,us,g,variances)
      end else acc
    end else
      let set_to a b =
        debug Pp.(fun () -> str"Minimize_weak: setting " ++ Level.raw_pr a ++ str" to " ++ Universe.pr Level.raw_pr b);
        let levels = Universe.levels b in
        let sup_variances = sup_variances variances (Level.Set.add a levels) in
        match InferCumulativity.term_type_variances sup_variances with
        | (None | Some UVars.Variance.Irrelevant), (None | Some UVars.Variance.Irrelevant) -> (* Irrelevant *)
          let variances =
            Level.Set.fold (fun bl variances -> set_variance variances bl sup_variances) levels variances
          in
          (Level.Set.remove a ctx, UnivFlex.define a b us, UGraph.set a b g, Level.Map.remove a variances)
        | _, _ -> (* One universe is not irrelevant *)
          (ctx,us, g, variances)
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
    weak (ctx, us, g, variances)


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
    if not (CDebug.get_flag switch_minim) then
      minimize_weak us weak (smallles, csts, g, variances)
    else (new_minimize_weak_pre us weak smallles, csts, g, variances)
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
    (* use lbound:Set to collapse [u <= v <= Set] into [u = v = Set] *)
    let g = Level.Set.fold (fun v g -> UGraph.enforce_constraint (Universe.type0, Le, Universe.make v) g)
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
    let g = UGraph.merge_constraints atomic g in
    Constraints.fold (fun cstr g ->
      if UGraph.check_constraint g cstr then g
      else UGraph.enforce_constraint (simplify_cstr cstr) g)
      nonatomic g
  in
  let locals, cstrs, partition = UGraph.constraints_of_universes ~only_local:true graph in
  debug Pp.(fun () -> str "Local universes: " ++ pr_universe_context_set prl (locals, cstrs));
  debug Pp.(fun () -> str "New universe context: " ++ pr_universe_context_set prl (ctx, cstrs));
  debug Pp.(fun () -> str "Partition: " ++ pr_partition prl partition);
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
    if not (CDebug.get_flag switch_minim) then
      (* Compute the left and right set of flexible variables, constraints
        mentioning other variables remain in noneqs. *)
       let filter, noneqs, ucstrsl, ucstrsr =
        Constraints.fold (fun (l,d,r) (filter, noneq, ucstrsl, ucstrsr as acc) ->
          let analyse l k r (filter, noneq, ucstrsl, ucstrsr) =
            let lus = UnivFlex.mem l us and rus = UnivFlex.mem r us in
            let ucstrsl' =
              if lus then add_list_map l (k, r) ucstrsl
              else ucstrsl
            and ucstrsr' =
              add_list_map r (k, l) ucstrsr
            in
            let noneqs =
              if lus || rus then noneq
              else Constraints.add (Universe.addn (Universe.make l) k, Le, Universe.make r) noneq
            in (filter, noneqs, ucstrsl', ucstrsr')
          in
          match Universe.level r with
          | Some r -> List.fold_left (fun acc (l, k) -> analyse l k r acc) acc (Univ.Universe.repr l)
          | None -> (Level.Set.union filter (Universe.levels r), Constraints.add (l, d, r) noneqs, ucstrsl, ucstrsr))
        noneqs (Level.Set.empty, Constraints.empty, Level.Map.empty, Level.Map.empty)
      in
          let us = Level.Set.fold (fun l us -> UnivFlex.remove l us) filter us in
      let ctx, us, noneqs = minimize_univ_variables partial ctx us variances ucstrsr ucstrsl noneqs in
      ctx, us, variances, noneqs
    else
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
      let ctx', us, graph, variances = new_minimize_weak ctx' us weak (graph, variances) in
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
