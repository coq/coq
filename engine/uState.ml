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
open CErrors
open Util
open Names
open Univ

module UNameMap = Names.Id.Map

type uinfo = {
  uname : Id.t option;
  uloc : Loc.t option;
}

module UPairSet = UnivMinim.UPairSet

(* 2nd part used to check consistency on the fly. *)
type t =
 { names : UnivNames.universe_binders * uinfo LMap.t;
   local : ContextSet.t; (** The local context of variables *)
   seff_univs : LSet.t; (** Local universes used through private constants *)
   univ_variables : UnivSubst.universe_opt_subst;
   (** The local universes that are unification variables *)
   univ_algebraic : LSet.t;
   (** The subset of unification variables that can be instantiated with
        algebraic universes as they appear in inferred types only. *)
   universes : UGraph.t; (** The current graph extended with the local constraints *)
   universes_lbound : UGraph.Bound.t; (** The lower bound on universes (e.g. Set or Prop) *)
   initial_universes : UGraph.t; (** The graph at the creation of the evar_map *)
   weak_constraints : UPairSet.t
 }

let initial_sprop_cumulative = UGraph.set_cumulative_sprop true UGraph.initial_universes

let empty =
  { names = UNameMap.empty, LMap.empty;
    local = ContextSet.empty;
    seff_univs = LSet.empty;
    univ_variables = LMap.empty;
    univ_algebraic = LSet.empty;
    universes = initial_sprop_cumulative;
    universes_lbound = UGraph.Bound.Set;
    initial_universes = initial_sprop_cumulative;
    weak_constraints = UPairSet.empty; }

let elaboration_sprop_cumul =
  Goptions.declare_bool_option_and_ref ~depr:false
    ~key:["Elaboration";"StrictProp";"Cumulativity"] ~value:true

let make ~lbound u =
  let u = UGraph.set_cumulative_sprop (elaboration_sprop_cumul ()) u in
  { empty with
    universes = u;
    universes_lbound = lbound;
    initial_universes = u}

let from_env e = make ~lbound:(Environ.universes_lbound e) (Environ.universes e)

let is_empty ctx =
  ContextSet.is_empty ctx.local &&
    LMap.is_empty ctx.univ_variables

let uname_union s t =
  if s == t then s
  else
    UNameMap.merge (fun k l r ->
        match l, r with
        | Some _, _ -> l
        | _, _ -> r) s t

let union ctx ctx' =
  if ctx == ctx' then ctx
  else if is_empty ctx' then ctx
  else
    let local = ContextSet.union ctx.local ctx'.local in
    let seff = LSet.union ctx.seff_univs ctx'.seff_univs in
    let names = uname_union (fst ctx.names) (fst ctx'.names) in
    let newus = LSet.diff (ContextSet.levels ctx'.local)
                               (ContextSet.levels ctx.local) in
    let newus = LSet.diff newus (LMap.domain ctx.univ_variables) in
    let weak = UPairSet.union ctx.weak_constraints ctx'.weak_constraints in
    let declarenew g =
      LSet.fold (fun u g -> UGraph.add_universe u ~lbound:ctx.universes_lbound ~strict:false g) newus g
    in
    let names_rev = LMap.lunion (snd ctx.names) (snd ctx'.names) in
      { names = (names, names_rev);
        local = local;
        seff_univs = seff;
        univ_variables =
          LMap.subst_union ctx.univ_variables ctx'.univ_variables;
        univ_algebraic =
          LSet.union ctx.univ_algebraic ctx'.univ_algebraic;
        initial_universes = declarenew ctx.initial_universes;
        universes =
          (if local == ctx.local then ctx.universes
           else
             let cstrsr = ContextSet.constraints ctx'.local in
             UGraph.merge_constraints cstrsr (declarenew ctx.universes));
        universes_lbound = ctx.universes_lbound;
        weak_constraints = weak}

let context_set ctx = ctx.local

let constraints ctx = snd ctx.local

let context ctx = ContextSet.to_context ctx.local

let compute_instance_binders inst ubinders =
  let revmap = Id.Map.fold (fun id lvl accu -> LMap.add lvl id accu) ubinders LMap.empty in
  let map lvl =
    try Name (LMap.find lvl revmap)
    with Not_found -> Anonymous
  in
  Array.map map (Instance.to_array inst)

let univ_entry ~poly uctx =
  let open Entries in
  if poly then
    let (binders, _) = uctx.names in
    let uctx = context uctx in
    let nas = compute_instance_binders (UContext.instance uctx) binders in
    Polymorphic_entry (nas, uctx)
  else Monomorphic_entry (context_set uctx)

let of_context_set ctx = { empty with local = ctx }

let subst ctx = ctx.univ_variables

let ugraph ctx = ctx.universes

let initial_graph ctx = ctx.initial_universes

let algebraics ctx = ctx.univ_algebraic

let add_names ?loc s l (names, names_rev) =
  if UNameMap.mem s names
  then user_err ?loc ~hdr:"add_names"
      Pp.(str "Universe " ++ Names.Id.print s ++ str" already bound.");
  (UNameMap.add s l names, LMap.add l { uname = Some s; uloc = loc } names_rev)

let add_loc l loc (names, names_rev) =
  match loc with
  | None -> (names, names_rev)
  | Some _ -> (names, LMap.add l { uname = None; uloc = loc } names_rev)

let of_binders b =
  let ctx = empty in
  let rmap =
    UNameMap.fold (fun id l rmap ->
        LMap.add l { uname = Some id; uloc = None } rmap)
      b LMap.empty
  in
  { ctx with names = b, rmap }

let invent_name (named,cnt) u =
  let rec aux i =
    let na = Id.of_string ("u"^(string_of_int i)) in
    if Id.Map.mem na named then aux (i+1)
    else Id.Map.add na u named, i+1
  in
  aux cnt

let universe_binders ctx =
  let named, rev = ctx.names in
  let named, _ = LSet.fold (fun u named ->
      match LMap.find u rev with
      | exception Not_found -> (* not sure if possible *) invent_name named u
      | { uname = None } -> invent_name named u
      | { uname = Some _ } -> named)
      (ContextSet.levels ctx.local) (named, 0)
  in
  named

let instantiate_variable l b v =
  try v := LMap.set l (Some b) !v
  with Not_found -> assert false

exception UniversesDiffer

let drop_weak_constraints =
  Goptions.declare_bool_option_and_ref
    ~depr:false
    ~key:["Cumulativity";"Weak";"Constraints"]
    ~value:false

let process_universe_constraints ctx cstrs =
  let open UnivSubst in
  let open UnivProblem in
  let univs = ctx.universes in
  let vars = ref ctx.univ_variables in
  let weak = ref ctx.weak_constraints in
  let normalize u = normalize_univ_variable_opt_subst !vars u in
  let nf_constraint = function
    | ULub (u, v) -> ULub (level_subst_of normalize u, level_subst_of normalize v)
    | UWeak (u, v) -> UWeak (level_subst_of normalize u, level_subst_of normalize v)
    | UEq (u, v) -> UEq (subst_univs_universe normalize u, subst_univs_universe normalize v)
    | ULe (u, v) -> ULe (subst_univs_universe normalize u, subst_univs_universe normalize v)
  in
  let is_local l = LMap.mem l !vars in
  let varinfo x =
    match Universe.level x with
    | None -> Inl x
    | Some l -> Inr l
  in
  let equalize_variables fo l l' r r' local =
    (* Assumes l = [l',0] and r = [r',0] *)
    let () =
      if is_local l' then
        instantiate_variable l' r vars
      else if is_local r' then
        instantiate_variable r' l vars
      else if not (UGraph.check_eq_level univs l' r') then
        (* Two rigid/global levels, none of them being local,
            one of them being Prop/Set, disallow *)
        if Level.is_small l' || Level.is_small r' then
          raise (UniverseInconsistency (Eq, l, r, None))
        else if fo then
          raise UniversesDiffer
    in
    enforce_eq_level l' r' local
  in
  let equalize_universes l r local = match varinfo l, varinfo r with
  | Inr l', Inr r' -> equalize_variables false l l' r r' local
  | Inr l, Inl r | Inl r, Inr l ->
    let alg = LSet.mem l ctx.univ_algebraic in
    let inst = univ_level_rem l r r in
      if alg && not (LSet.mem l (Universe.levels inst)) then
        (instantiate_variable l inst vars; local)
      else
        let lu = Universe.make l in
        if univ_level_mem l r then
          enforce_leq inst lu local
        else raise (UniverseInconsistency (Eq, lu, r, None))
  | Inl _, Inl _ (* both are algebraic *) ->
    if UGraph.check_eq univs l r then local
    else raise (UniverseInconsistency (Eq, l, r, None))
  in
  let unify_universes cst local =
    let cst = nf_constraint cst in
      if UnivProblem.is_trivial cst then local
      else
          match cst with
          | ULe (l, r) ->
            begin match Univ.Universe.level r with
            | None ->
              if UGraph.check_leq univs l r then local
              else user_err Pp.(str "Algebraic universe on the right")
            | Some r' ->
              if Level.is_small r' then
                  if not (Universe.is_levels l)
                  then (* l contains a +1 and r=r' small so l <= r impossible *)
                    raise (UniverseInconsistency (Le, l, r, None))
                  else
                    if UGraph.check_leq univs l r then match Univ.Universe.level l with
                    | Some l ->
                      Univ.Constraint.add (l, Le, r') local
                    | None -> local
                    else
                    let levels = Universe.levels l in
                    let fold l' local =
                      let l = Universe.make l' in
                      if Level.is_small l' || is_local l' then
                        equalize_variables false l l' r r' local
                      else raise (UniverseInconsistency (Le, l, r, None))
                    in
                    LSet.fold fold levels local
              else
                match Univ.Universe.level l with
                | Some l ->
                  Univ.Constraint.add (l, Le, r') local
                | None ->
                  if UGraph.check_leq univs l r then local else enforce_leq l r local
              end
          | ULub (l, r) ->
              equalize_variables true (Universe.make l) l (Universe.make r) r local
          | UWeak (l, r) ->
            if not (drop_weak_constraints ()) then weak := UPairSet.add (l,r) !weak; local
          | UEq (l, r) -> equalize_universes l r local
  in
  let local =
    UnivProblem.Set.fold unify_universes cstrs Constraint.empty
  in
    !vars, !weak, local

let add_constraints ctx cstrs =
  let univs, local = ctx.local in
  let cstrs' = Constraint.fold (fun (l,d,r) acc ->
    let l = Universe.make l and r = Universe.make r in
    let cstr' = let open UnivProblem in
      match d with
      | Lt ->
        ULe (Universe.super l, r)
      | Le -> ULe (l, r)
      | Eq -> UEq (l, r)
    in UnivProblem.Set.add cstr' acc)
    cstrs UnivProblem.Set.empty
  in
  let vars, weak, local' = process_universe_constraints ctx cstrs' in
  { ctx with
    local = (univs, Constraint.union local local');
    univ_variables = vars;
    universes = UGraph.merge_constraints local' ctx.universes;
    weak_constraints = weak; }

(* let addconstrkey = CProfile.declare_profile "add_constraints_context";; *)
(* let add_constraints_context = CProfile.profile2 addconstrkey add_constraints_context;; *)

let add_universe_constraints ctx cstrs =
  let univs, local = ctx.local in
  let vars, weak, local' = process_universe_constraints ctx cstrs in
  { ctx with
    local = (univs, Constraint.union local local');
    univ_variables = vars;
    universes = UGraph.merge_constraints local' ctx.universes;
    weak_constraints = weak; }

let constrain_variables diff ctx =
  let univs, local = ctx.local in
  let univs, vars, local =
    LSet.fold
      (fun l (univs, vars, cstrs) ->
        try
          match LMap.find l vars with
          | Some u ->
             (LSet.add l univs,
              LMap.remove l vars,
              Constraint.add (l, Eq, Option.get (Universe.level u)) cstrs)
          | None -> (univs, vars, cstrs)
        with Not_found | Option.IsNone -> (univs, vars, cstrs))
      diff (univs, ctx.univ_variables, local)
  in
  { ctx with local = (univs, local); univ_variables = vars }

let qualid_of_level uctx =
  let map, map_rev = uctx.names in
    fun l ->
      try Some (Libnames.qualid_of_ident (Option.get (LMap.find l map_rev).uname))
      with Not_found | Option.IsNone ->
        UnivNames.qualid_of_level l

let pr_uctx_level uctx l =
  match qualid_of_level uctx l with
  | Some qid -> Libnames.pr_qualid qid
  | None -> Level.pr l

type ('a, 'b) gen_universe_decl = {
  univdecl_instance : 'a; (* Declared universes *)
  univdecl_extensible_instance : bool; (* Can new universes be added *)
  univdecl_constraints : 'b; (* Declared constraints *)
  univdecl_extensible_constraints : bool (* Can new constraints be added *) }

type universe_decl =
  (lident list, Constraint.t) gen_universe_decl

let default_univ_decl =
  { univdecl_instance = [];
    univdecl_extensible_instance = true;
    univdecl_constraints = Constraint.empty;
    univdecl_extensible_constraints = true }

let error_unbound_universes left uctx =
  let n = LSet.cardinal left in
  let loc =
    try
      let info =
        LMap.find (LSet.choose left) (snd uctx.names) in
      info.uloc
    with Not_found -> None
  in
  user_err ?loc ~hdr:"universe_context"
    ((str(CString.plural n "Universe") ++ spc () ++
      LSet.pr (pr_uctx_level uctx) left ++
      spc () ++ str (CString.conjugate_verb_to_be n) ++
      str" unbound."))

let universe_context ~names ~extensible uctx =
  let levels = ContextSet.levels uctx.local in
  let newinst, left =
    List.fold_right
      (fun { CAst.loc; v = id } (newinst, acc) ->
         let l =
           try UNameMap.find id (fst uctx.names)
           with Not_found -> assert false
         in (l :: newinst, LSet.remove l acc))
      names ([], levels)
  in
  if not extensible && not (LSet.is_empty left)
  then error_unbound_universes left uctx
  else
    let left = ContextSet.sort_levels (Array.of_list (LSet.elements left)) in
    let inst = Array.append (Array.of_list newinst) left in
    let inst = Instance.of_array inst in
    let ctx = UContext.make (inst, ContextSet.constraints uctx.local) in
    ctx

let check_universe_context_set ~names ~extensible uctx =
  if extensible then ()
  else
    let left = List.fold_left (fun left { CAst.loc; v = id } ->
        let l =
          try UNameMap.find id (fst uctx.names)
          with Not_found -> assert false
        in LSet.remove l left)
        (ContextSet.levels uctx.local) names
    in
    if not (LSet.is_empty left)
    then error_unbound_universes left uctx

let check_implication uctx cstrs cstrs' =
  let gr = initial_graph uctx in
  let grext = UGraph.merge_constraints cstrs gr in
  if UGraph.check_constraints cstrs' grext then ()
  else CErrors.user_err ~hdr:"check_univ_decl"
      (str "Universe constraints are not implied by the ones declared.")

let check_mono_univ_decl uctx decl =
  let () =
    let names = decl.univdecl_instance in
    let extensible = decl.univdecl_extensible_instance in
    check_universe_context_set ~names ~extensible uctx
  in
  if not decl.univdecl_extensible_constraints then
    check_implication uctx
      decl.univdecl_constraints
      (ContextSet.constraints uctx.local);
  uctx.local

let check_univ_decl ~poly uctx decl =
  let ctx =
    let names = decl.univdecl_instance in
    let extensible = decl.univdecl_extensible_instance in
    if poly then
      let (binders, _) = uctx.names in
      let uctx = universe_context ~names ~extensible uctx in
      let nas = compute_instance_binders (UContext.instance uctx) binders in
      Entries.Polymorphic_entry (nas, uctx)
    else
      let () = check_universe_context_set ~names ~extensible uctx in
      Entries.Monomorphic_entry uctx.local
  in
  if not decl.univdecl_extensible_constraints then
    check_implication uctx
      decl.univdecl_constraints
      (ContextSet.constraints uctx.local);
  ctx

let is_bound l lbound = match lbound with
| UGraph.Bound.Prop -> Level.is_prop l
| UGraph.Bound.Set -> Level.is_set l

let restrict_universe_context ~lbound (univs, csts) keep =
  let removed = LSet.diff univs keep in
  if LSet.is_empty removed then univs, csts
  else
  let allunivs = Constraint.fold (fun (u,_,v) all -> LSet.add u (LSet.add v all)) csts univs in
  let g = UGraph.initial_universes in
  let g = LSet.fold (fun v g -> if Level.is_small v then g else
                        UGraph.add_universe v ~lbound ~strict:false g) allunivs g in
  let g = UGraph.merge_constraints csts g in
  let allkept = LSet.union (UGraph.domain UGraph.initial_universes) (LSet.diff allunivs removed) in
  let csts = UGraph.constraints_for ~kept:allkept g in
  let csts = Constraint.filter (fun (l,d,r) ->
      not ((is_bound l lbound && d == Le) || (Level.is_prop l && d == Lt && Level.is_set r))) csts in
  (LSet.inter univs keep, csts)

let restrict ctx vars =
  let vars = LSet.union vars ctx.seff_univs in
  let vars = Names.Id.Map.fold (fun na l vars -> LSet.add l vars)
      (fst ctx.names) vars
  in
  let uctx' = restrict_universe_context ~lbound:ctx.universes_lbound ctx.local vars in
  { ctx with local = uctx' }

type rigid =
  | UnivRigid
  | UnivFlexible of bool (** Is substitution by an algebraic ok? *)

let univ_rigid = UnivRigid
let univ_flexible = UnivFlexible false
let univ_flexible_alg = UnivFlexible true

(** ~sideff indicates that it is ok to redeclare a universe.
    ~extend also merges the universe context in the local constraint structures
    and not only in the graph. This depends if the
    context we merge comes from a side effect that is already inlined
    or defined separately. In the later case, there is no extension,
    see [emit_side_effects] for example. *)
let merge ?loc ~sideff rigid uctx ctx' =
  let levels = ContextSet.levels ctx' in
  let uctx =
    match rigid with
    | UnivRigid -> uctx
    | UnivFlexible b ->
      let fold u accu =
        if LMap.mem u accu then accu
        else LMap.add u None accu
      in
      let uvars' = LSet.fold fold levels uctx.univ_variables in
      if b then
        { uctx with univ_variables = uvars';
                    univ_algebraic = LSet.union uctx.univ_algebraic levels }
      else { uctx with univ_variables = uvars' }
  in
  let local = ContextSet.append ctx' uctx.local in
  let declare g =
    LSet.fold (fun u g ->
        try UGraph.add_universe ~lbound:uctx.universes_lbound ~strict:false u g
        with UGraph.AlreadyDeclared when sideff -> g)
      levels g
  in
  let names =
    let fold u accu =
      let modify _ info = match info.uloc with
        | None -> { info with uloc = loc }
        | Some _ -> info
      in
      try LMap.modify u modify accu
      with Not_found -> LMap.add u { uname = None; uloc = loc } accu
    in
    (fst uctx.names, LSet.fold fold levels (snd uctx.names))
  in
  let initial = declare uctx.initial_universes in
  let univs = declare uctx.universes in
  let universes = UGraph.merge_constraints (ContextSet.constraints ctx') univs in
  { uctx with names; local; universes;
              initial_universes = initial }

let merge_subst uctx s =
  { uctx with univ_variables = LMap.subst_union uctx.univ_variables s }

let demote_seff_univs univs uctx =
  let seff = LSet.union uctx.seff_univs univs in
  { uctx with seff_univs = seff }

let demote_global_univs env uctx =
  let env_ugraph = Environ.universes env in
  let global_univs = UGraph.domain env_ugraph in
  let global_constraints, _ = UGraph.constraints_of_universes env_ugraph in
  let promoted_uctx =
    ContextSet.(of_set global_univs |> add_constraints global_constraints) in
  { uctx with local = ContextSet.diff uctx.local promoted_uctx }

let merge_seff uctx ctx' =
  let levels = ContextSet.levels ctx' in
  let declare g =
    LSet.fold (fun u g ->
        try UGraph.add_universe ~lbound:uctx.universes_lbound ~strict:false u g
        with UGraph.AlreadyDeclared -> g)
      levels g
  in
  let initial = declare uctx.initial_universes in
  let univs = declare uctx.universes in
  let universes = UGraph.merge_constraints (ContextSet.constraints ctx') univs in
  { uctx with universes;
              initial_universes = initial }

let emit_side_effects eff u =
  let uctx = Safe_typing.universes_of_private eff in
  let u = demote_seff_univs (fst uctx) u in
  merge_seff u uctx

let update_sigma_env uctx env =
  let univs = UGraph.set_cumulative_sprop (elaboration_sprop_cumul()) (Environ.universes env) in
  let eunivs =
    { uctx with
      initial_universes = univs;
      universes = univs }
  in
  merge_seff eunivs eunivs.local

let new_univ_variable ?loc rigid name
  ({ local = ctx; univ_variables = uvars; univ_algebraic = avars} as uctx) =
  let u = UnivGen.fresh_level () in
  let ctx' = ContextSet.add_universe u ctx in
  let uctx', pred =
    match rigid with
    | UnivRigid -> uctx, true
    | UnivFlexible b ->
      let uvars' = LMap.add u None uvars in
        if b then {uctx with univ_variables = uvars';
          univ_algebraic = LSet.add u avars}, false
        else {uctx with univ_variables = uvars'}, false
  in
  let names =
    match name with
    | Some n -> add_names ?loc n u uctx.names
    | None -> add_loc u loc uctx.names
  in
  let initial =
    UGraph.add_universe ~lbound:uctx.universes_lbound ~strict:false u uctx.initial_universes
  in
  let uctx' =
    {uctx' with names = names; local = ctx';
                universes = UGraph.add_universe ~lbound:uctx.universes_lbound ~strict:false
                    u uctx.universes;
                initial_universes = initial}
  in uctx', u

let make_with_initial_binders ~lbound e us =
  let uctx = make ~lbound e in
  List.fold_left
    (fun uctx { CAst.loc; v = id } ->
       fst (new_univ_variable ?loc univ_rigid (Some id) uctx))
    uctx us

let add_global_univ uctx u =
  let initial =
    UGraph.add_universe ~lbound:UGraph.Bound.Set ~strict:true u uctx.initial_universes
  in
  let univs =
    UGraph.add_universe ~lbound:UGraph.Bound.Set ~strict:true u uctx.universes
  in
  { uctx with local = ContextSet.add_universe u uctx.local;
                                     initial_universes = initial;
                                     universes = univs }

let make_flexible_variable ctx ~algebraic u =
  let {local = cstrs; univ_variables = uvars;
       univ_algebraic = avars; universes=g; } = ctx in
  assert (try LMap.find u uvars == None with Not_found -> true);
  match UGraph.choose (fun v -> not (Level.equal u v) && (algebraic || not (LSet.mem v avars))) g u with
  | Some v ->
    let uvars' = LMap.add u (Some (Universe.make v)) uvars in
    { ctx with univ_variables = uvars'; }
  | None ->
    let uvars' = LMap.add u None uvars in
    let avars' =
      if algebraic then
        let uu = Universe.make u in
        let substu_not_alg u' v =
          Option.cata (fun vu -> Universe.equal uu vu && not (LSet.mem u' avars)) false v
        in
        let has_upper_constraint () =
          Constraint.exists
            (fun (l,d,r) -> d == Lt && Level.equal l u)
            (ContextSet.constraints cstrs)
        in
        if not (LMap.exists substu_not_alg uvars || has_upper_constraint ())
        then LSet.add u avars else avars
      else avars
    in
    {ctx with univ_variables = uvars';
              univ_algebraic = avars'}

let make_nonalgebraic_variable ctx u =
  { ctx with univ_algebraic = LSet.remove u ctx.univ_algebraic }

let make_flexible_nonalgebraic ctx =
  {ctx with univ_algebraic = LSet.empty}

let is_sort_variable uctx s =
  match s with
  | Sorts.Type u ->
    (match universe_level u with
    | Some l as x ->
        if LSet.mem l (ContextSet.levels uctx.local) then x
        else None
    | None -> None)
  | _ -> None

let subst_univs_context_with_def def usubst (ctx, cst) =
  (LSet.diff ctx def, UnivSubst.subst_univs_constraints usubst cst)

let is_trivial_leq (l,d,r) =
  Level.is_prop l && (d == Le || (d == Lt && Level.is_set r))

(* Prop < i <-> Set+1 <= i <-> Set < i *)
let translate_cstr (l,d,r as cstr) =
  if Level.equal Level.prop l && d == Lt && not (Level.equal Level.set r) then
    (Level.set, d, r)
  else cstr

let refresh_constraints univs (ctx, cstrs) =
  let cstrs', univs' =
    Constraint.fold (fun c (cstrs', univs as acc) ->
      let c = translate_cstr c in
      if is_trivial_leq c then acc
      else (Constraint.add c cstrs', UGraph.enforce_constraint c univs))
      cstrs (Constraint.empty, univs)
  in ((ctx, cstrs'), univs')

let normalize_variables uctx =
  let normalized_variables, def, subst =
    UnivSubst.normalize_univ_variables uctx.univ_variables
  in
  let ctx_local = subst_univs_context_with_def def (make_subst subst) uctx.local in
  let ctx_local', univs = refresh_constraints uctx.initial_universes ctx_local in
    subst, { uctx with local = ctx_local';
      univ_variables = normalized_variables;
      universes = univs }

let abstract_undefined_variables uctx =
  let vars' =
    LMap.fold (fun u v acc ->
      if v == None then LSet.remove u acc
      else acc)
    uctx.univ_variables uctx.univ_algebraic
  in { uctx with local = ContextSet.empty;
      univ_algebraic = vars' }

let fix_undefined_variables uctx =
  let algs', vars' =
    LMap.fold (fun u v (algs, vars as acc) ->
      if v == None then (LSet.remove u algs, LMap.remove u vars)
      else acc)
      uctx.univ_variables
      (uctx.univ_algebraic, uctx.univ_variables)
  in
  { uctx with univ_variables = vars';
    univ_algebraic = algs' }

let refresh_undefined_univ_variables uctx =
  let subst, ctx' = UnivGen.fresh_universe_context_set_instance uctx.local in
  let subst_fn u = subst_univs_level_level subst u in
  let alg = LSet.fold (fun u acc -> LSet.add (subst_fn u) acc)
    uctx.univ_algebraic LSet.empty
  in
  let vars =
    LMap.fold
      (fun u v acc ->
        LMap.add (subst_fn u)
          (Option.map (subst_univs_level_universe subst) v) acc)
      uctx.univ_variables LMap.empty
  in
  let weak = UPairSet.fold (fun (u,v) acc -> UPairSet.add (subst_fn u, subst_fn v) acc) uctx.weak_constraints UPairSet.empty in
  let lbound = uctx.universes_lbound in
  let declare g = LSet.fold (fun u g -> UGraph.add_universe u ~lbound ~strict:false g)
      (ContextSet.levels ctx') g in
  let initial = declare uctx.initial_universes in
  let univs = declare UGraph.initial_universes in
  let uctx' = {names = uctx.names;
               local = ctx';
               seff_univs = uctx.seff_univs;
               univ_variables = vars; univ_algebraic = alg;
               universes = univs;
               universes_lbound = lbound;
               initial_universes = initial;
               weak_constraints = weak; } in
    uctx', subst

let minimize uctx =
  let open UnivMinim in
  let lbound = uctx.universes_lbound in
  let ((vars',algs'), us') =
    normalize_context_set ~lbound uctx.universes uctx.local uctx.univ_variables
      uctx.univ_algebraic uctx.weak_constraints
  in
  if ContextSet.equal us' uctx.local then uctx
  else
    let us', universes =
      refresh_constraints uctx.initial_universes us'
    in
      { names = uctx.names;
        local = us';
        seff_univs = uctx.seff_univs; (* not sure about this *)
        univ_variables = vars';
        univ_algebraic = algs';
        universes = universes;
        universes_lbound = lbound;
        initial_universes = uctx.initial_universes;
        weak_constraints = UPairSet.empty; (* weak constraints are consumed *) }

let universe_of_name uctx s =
  UNameMap.find s (fst uctx.names)

let pr_weak prl {weak_constraints=weak} =
  let open Pp in
  prlist_with_sep fnl (fun (u,v) -> prl u ++ str " ~ " ++ prl v) (UPairSet.elements weak)
