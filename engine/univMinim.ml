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

type lbound = { enforce : bool; lbound: Universe.t; lower : lowermap }

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

let instantiate_with_lbound u lbound lower ~enforce (ctx, us, seen, insts, cstrs) =
  let flexible = try not (UnivFlex.is_defined u us) with Not_found -> false in
  if enforce || not flexible then
    let inst = Universe.make u in
    let cstrs' = enforce_leq lbound inst cstrs in
      (ctx, us, seen, LBMap.add u {enforce;lbound;lower} insts, cstrs'),
      {enforce; lbound=inst; lower}
  else (* Actually instantiate *)
    (debug Pp.(fun () -> str"Instantiating " ++ Level.raw_pr u ++ str" with " ++ Universe.pr Level.raw_pr lbound);
    (Level.Set.remove u ctx, UnivFlex.define u lbound us, seen,
     LBMap.add u {enforce;lbound;lower} insts, cstrs),
    {enforce; lbound; lower})

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

let minimize_univ_variables ctx us variances left right cstrs =
  let left, lbounds =
    Level.Map.fold (fun r lower (left, lbounds as acc)  ->
      if UnivFlex.mem r us || not (Level.Set.mem r ctx) then acc
      else (* Fixed universe, just compute its glb for sharing *)
        let lbounds =
          match compute_lbound (List.map (fun (d,l) -> d, Universe.make l) lower) with
          | None -> lbounds
          | Some lbound -> LBMap.add r {enforce=true; lbound; lower=lower_of_list lower}
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
           let acc', {enforce=enf;lbound=l';lower} = aux acc l in
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
    let term_variance, type_variance =
      let open UVars.Variance in
      match Level.Map.find_opt u variances with
      | None -> if UnivFlex.mem u us then Irrelevant, Irrelevant else Invariant, Invariant
      | Some pos ->
        let termv, typev = term_type_variances pos in
        (* No recorded variance for this universe *)
         Option.default Irrelevant termv, Option.default Irrelevant typev
    in
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
      match Level.Map.find u right with
      | exception Not_found -> acc
      | upper ->
        let upper = List.filter (fun (d, r) -> not (UnivFlex.mem r us)) upper in
        let cstrs = enforce_uppers upper b.lbound cstrs in
        (ctx, us, seen, insts, cstrs), b
    in
    if not (Level.Set.mem u ctx)
    then enforce_uppers (acc, {enforce=true; lbound=Universe.make u; lower})
    else
      let lbound = match compute_lbound left with None -> Universe.type0 | Some lbound -> lbound in
      debug Pp.(fun () -> str"Lower bound of " ++ Level.raw_pr u ++ str":" ++ Universe.pr Level.raw_pr lbound);
      let open UVars.Variance in
      match term_variance, type_variance with
      | Irrelevant, (Irrelevant | Covariant) ->
        (* This keeps principal typings, as instantiating to e.g. Set in a covariant position allows to use Set <= i for any i *)
        enforce_uppers (instantiate_lbound lbound)
      | _, _ ->
        if Universe.is_type0 lbound then enforce_uppers (acc, {enforce = true; lbound = Universe.make u; lower})
        else enforce_uppers (instantiate_with_lbound u lbound lower ~enforce:true acc)
  and aux (ctx, us, seen, insts, cstrs as acc) u =
    debug Pp.(fun () -> str"Calling minim on " ++ Level.raw_pr u);
    try let lbound = Level.Map.find u insts.LBMap.lbmap in
      debug Pp.(fun () -> str" = " ++ Universe.pr Level.raw_pr lbound.lbound);
      acc, lbound
    with Not_found ->
      if Level.Set.mem u seen then
        (* Loop in the contraints *)
        let bnd = {enforce=true; lbound=Universe.make u; lower = Level.Map.empty} in
        acc, bnd
      else instance (ctx, us, Level.Set.add u seen, insts, cstrs) u
  in
    UnivFlex.fold (fun u ~is_defined (ctx, us, seen, insts, cstrs as acc) ->
      if not is_defined then fst (aux acc u)
      else Level.Set.remove u ctx, us, seen, insts, cstrs)
      us (ctx, us, Level.Set.empty, lbounds, cstrs)

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

let normalize_context_set ~lbound ~variances g ctx (us:UnivFlex.t) ?binders {weak_constraints=weak;above_prop} =
  let prl = UnivNames.pr_level_with_global_universes ?binders in
  debug Pp.(fun () -> str "Minimizing context: " ++ pr_universe_context_set prl ctx ++ spc () ++
    UnivFlex.pr Level.raw_pr us ++ fnl () ++
    str"Variances: " ++ pr_variances prl variances ++ fnl () ++
    str"Weak constraints " ++
    prlist_with_sep spc (fun (u,v) -> Universe.pr Level.raw_pr u ++ str" ~ " ++ Universe.pr Level.raw_pr v)
     (UPairSet.elements weak));
  let (ctx, csts) = ContextSet.levels ctx, ContextSet.constraints ctx in
  (* Keep the Prop/Set <= i constraints separate for minimization *)
  let csts = decompose_constraints csts in
  let smallles, csts =
    Constraints.partition (fun (l,d,r) -> d == Le && Universe.is_type0 l) csts
  in
  (* Process weak constraints: when one side is flexible and the 2
     universes are unrelated unify them. *)
  let smallles, csts, g = UPairSet.fold (fun (u,v) (smallles, csts, g as acc) ->
      let norm = Universe.subst_fn (level_subst_of (UnivFlex.normalize_univ_variable us)) in
      let u = norm u and v = norm v in
      if (Universe.is_type0 u || Universe.is_type0 v) then begin
        if get_set_minimization() then begin
          if Universe.is_type0 u then (Constraints.add (u,Le,v) smallles,csts,g)
          else (Constraints.add (v,Le,u) smallles,csts,g)
        end else acc
      end else
        let set_to a b =
          (smallles,
           Constraints.add (Universe.make a,Eq,b) csts,
           UGraph.enforce_constraint (Universe.make a,Eq,b) g)
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
      weak (smallles, csts, g)
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
  let csts, partition =
    (* We first put constraints in a normal-form: all self-loops are collapsed
       to equalities. *)
    let g = UGraph.initial_universes_with g in
    (* use lbound:Set to collapse [u <= v <= Set] into [u = v = Set] *)
    let g = Level.Set.fold (fun v g -> UGraph.add_universe ~lbound:Set ~strict:false v g)
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
    let g =
      Constraints.fold (fun cstr g ->
        if UGraph.check_constraint g cstr then g
        else UGraph.enforce_constraint (simplify_cstr cstr) g)
      nonatomic g in
    let cstrs = UGraph.constraints_of_universes g in
    debug Pp.(fun () -> str "New universe context: " ++ pr_universe_context_set prl (ctx, fst cstrs));
    debug Pp.(fun () -> str "Partition: " ++ pr_partition prl (snd cstrs));
    cstrs
  in
  (* Ignore constraints from lbound:Set *)
  let noneqs =
    Constraints.filter
      (fun (l,d,r) -> not (d == Le && Universe.is_type0 l))
      csts
  in
  (* Put back constraints [Set <= u] from type inference *)
  let noneqs = Constraints.union noneqs smallles in
  let flex x = UnivFlex.mem x us in
  let ctx, us, eqs = List.fold_left (fun (ctx, us, cstrs) eqs ->
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
        let ctx, us = LevelExpr.Set.fold (fun (f, k') (ctx, us) -> (Level.Set.remove f ctx, UnivFlex.define f (Universe.addn canonu (-k')) us)) flexible (ctx, us) in
        ctx, us, cstrs
      else
        if LevelExpr.Set.is_empty flexible then (ctx, us, cstrs) else
        (* We need to find the max of canon and flexibles *)
        let (canon', canonk' as can') = LevelExpr.Set.max_elt flexible in
        let ctx, us = LevelExpr.Set.fold (fun (f, k') (ctx, us) ->
          (Level.Set.remove f ctx, UnivFlex.define f (Universe.addn (Universe.of_expr can') (-k')) us))
          (LevelExpr.Set.remove (canon', canonk') flexible) (ctx, us)
        in
        if snd canon < canonk' then
          ctx, us, enforce_eq canonu (Universe.of_expr can') cstrs
        else Level.Set.remove canon' ctx, UnivFlex.define canon' (Universe.addn canonu (-canonk')) us, cstrs)
      (ctx, us, Constraints.empty)
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
  (* Now we construct the instantiation of each variable. *)
  debug Pp.(fun () -> str "Starting minimization with: " ++ pr_universe_context_set prl (ctx, noneqs) ++
    UnivFlex.pr Level.raw_pr us);
  let ctx', us, seen, inst, noneqs =
    minimize_univ_variables ctx us variances ucstrsr ucstrsl noneqs
  in
  let us = UnivFlex.normalize us in
  let noneqs = UnivSubst.subst_univs_constraints (UnivFlex.normalize_univ_variable us) noneqs in
  let ctx = (ctx', Constraints.union noneqs eqs) in
  debug Pp.(fun () -> str "After minimization: " ++ pr_universe_context_set prl ctx ++
    UnivFlex.pr Level.raw_pr us);
  us, ctx
