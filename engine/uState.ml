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
 { names : UnivNames.universe_binders * uinfo LMap.t; (** Printing/location information *)
   local : ContextSet.t; (** The local graph of universes (variables and constraints) *)
   seff_univs : LSet.t; (** Local universes used through private constants *)
   univ_variables : UnivSubst.universe_opt_subst;
   (** The local universes that are unification variables *)
   univ_algebraic : LSet.t;
   (** The subset of unification variables that can be instantiated with
        algebraic universes as they appear in inferred types only. *)
   universes : UGraph.t; (** The current graph extended with the local constraints *)
   universes_lbound : UGraph.Bound.t; (** The lower bound on universes (e.g. Set or Prop) *)
   initial_universes : UGraph.t; (** The graph at the creation of the evar_map *)
   weak_constraints : UPairSet.t;
   pseudo_monomorphic_instances : Instance.t GlobRef.Map.t;
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
    weak_constraints = UPairSet.empty;
    pseudo_monomorphic_instances = GlobRef.Map.empty;
  }

let elaboration_sprop_cumul =
  Goptions.declare_bool_option_and_ref ~depr:false
    ~key:["Elaboration";"StrictProp";"Cumulativity"] ~value:true

let make ~lbound univs =
  let univs = UGraph.set_cumulative_sprop (elaboration_sprop_cumul ()) univs in
  { empty with
    universes = univs;
    universes_lbound = lbound;
    initial_universes = univs}

let is_empty uctx =
  ContextSet.is_empty uctx.local &&
    LMap.is_empty uctx.univ_variables

let uname_union s t =
  if s == t then s
  else
    UNameMap.merge (fun k l r ->
        match l, r with
        | Some _, _ -> l
        | _, _ -> r) s t

let union uctx uctx' =
  if uctx == uctx' then uctx
  else if is_empty uctx' then uctx
  else
    let local = ContextSet.union uctx.local uctx'.local in
    let seff = LSet.union uctx.seff_univs uctx'.seff_univs in
    let names = uname_union (fst uctx.names) (fst uctx'.names) in
    let names_rev = LMap.lunion (snd uctx.names) (snd uctx'.names) in
    let newus = LSet.diff (ContextSet.levels uctx'.local)
                               (ContextSet.levels uctx.local) in
    let newus = LSet.diff newus (LMap.domain uctx.univ_variables) in
    let weak = UPairSet.union uctx.weak_constraints uctx'.weak_constraints in
    let csts' = ref (snd uctx'.local) in
    let p_m_instances = GlobRef.Map.union
        (fun _ l r ->
           if not (Instance.equal l r)
           then csts' := enforce_eq_instances l r !csts';
           Some l)
        uctx.pseudo_monomorphic_instances
        uctx'.pseudo_monomorphic_instances
    in
    let csts' = !csts' in
    let declarenew g =
      LSet.fold (fun u g -> UGraph.add_universe u ~lbound:uctx.universes_lbound ~strict:false g) newus g
    in
    { names = (names, names_rev);
      local = local;
      seff_univs = seff;
      univ_variables =
        LMap.subst_union uctx.univ_variables uctx'.univ_variables;
      univ_algebraic =
        LSet.union uctx.univ_algebraic uctx'.univ_algebraic;
      initial_universes = declarenew uctx.initial_universes;
      universes =
        (if local == uctx.local then uctx.universes
         else UGraph.merge_constraints csts' (declarenew uctx.universes));
      universes_lbound = uctx.universes_lbound;
      weak_constraints = weak;
      pseudo_monomorphic_instances = p_m_instances;
    }

let context_set uctx = uctx.local

let constraints uctx = snd uctx.local

let context uctx = ContextSet.to_context uctx.local

let compute_instance_binders inst ubinders =
  let map lvl =
    try Name (Option.get (LMap.find lvl ubinders).uname)
    with Option.IsNone | Not_found -> Anonymous
  in
  Array.map map (Instance.to_array inst)

let univ_entry ~poly uctx =
  let open Entries in
  if poly then
    let (_, rbinders) = uctx.names in
    let uctx = context uctx in
    let nas = compute_instance_binders (UContext.instance uctx) rbinders in
    Polymorphic_entry (nas, uctx)
  else Monomorphic_entry (context_set uctx)

let of_context_set local = { empty with local }

let subst uctx = uctx.univ_variables

let ugraph uctx = uctx.universes

let initial_graph uctx = uctx.initial_universes

let algebraics uctx = uctx.univ_algebraic

let add_names ?loc s l (names, names_rev) =
  if UNameMap.mem s names
  then user_err ?loc ~hdr:"add_names"
      Pp.(str "Universe " ++ Names.Id.print s ++ str" already bound.");
  (UNameMap.add s l names, LMap.add l { uname = Some s; uloc = loc } names_rev)

let add_loc l loc (names, names_rev) =
  match loc with
  | None -> (names, names_rev)
  | Some _ -> (names, LMap.add l { uname = None; uloc = loc } names_rev)

let of_binders names =
  let rev_map =
    UNameMap.fold (fun id l rmap ->
        LMap.add l { uname = Some id; uloc = None } rmap)
      names LMap.empty
  in
  { empty with names = (names, rev_map) }

let universe_binders uctx =
  let named, _ = uctx.names in
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

let process_universe_constraints uctx cstrs =
  let open UnivSubst in
  let open UnivProblem in
  let univs = uctx.universes in
  let vars = ref uctx.univ_variables in
  let weak = ref uctx.weak_constraints in
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
    let alg = LSet.mem l uctx.univ_algebraic in
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
                  (* We insert the constraint in the graph even if the graph
                     already contains it.  Indeed, checking the existance of the
                     constraint is costly when the constraint does not already
                     exist directly as a single edge in the graph, but adding an
                     edge in the graph which is implied by others is cheap.
                     Hence, by doing this, we avoid a costly check here, and
                     make further checks of this constraint easier since it will
                     exist directly in the graph. *)
                  enforce_leq l r local
              end
          | ULub (l, r) ->
              equalize_variables true (Universe.make l) l (Universe.make r) r local
          | UWeak (l, r) ->
            if not (drop_weak_constraints ()) then weak := UPairSet.add (l,r) !weak; local
          | UEq (l, r) -> equalize_universes l r local
  in
  let unify_universes cst local =
    if not (UGraph.type_in_type univs) then unify_universes cst local
    else try unify_universes cst local with UniverseInconsistency _ -> local
  in
  let local =
    UnivProblem.Set.fold unify_universes cstrs Constraint.empty
  in
    !vars, !weak, local

let add_constraints uctx cstrs =
  let univs, old_cstrs = uctx.local in
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
  let vars, weak, cstrs' = process_universe_constraints uctx cstrs' in
  { uctx with
    local = (univs, Constraint.union old_cstrs cstrs');
    univ_variables = vars;
    universes = UGraph.merge_constraints cstrs' uctx.universes;
    weak_constraints = weak; }

let add_universe_constraints uctx cstrs =
  let univs, local = uctx.local in
  let vars, weak, local' = process_universe_constraints uctx cstrs in
  { uctx with
    local = (univs, Constraint.union local local');
    univ_variables = vars;
    universes = UGraph.merge_constraints local' uctx.universes;
    weak_constraints = weak; }

let constrain_variables diff uctx =
  let univs, local = uctx.local in
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
      diff (univs, uctx.univ_variables, local)
  in
  { uctx with local = (univs, local); univ_variables = vars }

let id_of_level uctx l =
  try Some (Option.get (LMap.find l (snd uctx.names)).uname)
  with Not_found | Option.IsNone ->
    None

let qualid_of_level uctx l =
  let map, map_rev = uctx.names in
  try Some (Libnames.qualid_of_ident (Option.get (LMap.find l map_rev).uname))
  with Not_found | Option.IsNone ->
    UnivNames.qualid_of_level map l

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
    let uctx = UContext.make (inst, ContextSet.constraints uctx.local) in
    uctx

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
  if not decl.univdecl_extensible_constraints then
    check_implication uctx
      decl.univdecl_constraints
      (ContextSet.constraints uctx.local);
  let names = decl.univdecl_instance in
  let extensible = decl.univdecl_extensible_instance in
  if poly then
    let (_, rbinders) = uctx.names in
    let uctx = universe_context ~names ~extensible uctx in
    let nas = compute_instance_binders (UContext.instance uctx) rbinders in
    Entries.Polymorphic_entry (nas, uctx)
  else
    let () = check_universe_context_set ~names ~extensible uctx in
    Entries.Monomorphic_entry uctx.local

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

let restrict uctx vars =
  let vars = LSet.union vars uctx.seff_univs in
  let vars = Names.Id.Map.fold (fun na l vars -> LSet.add l vars)
      (fst uctx.names) vars
  in
  let uctx' = restrict_universe_context ~lbound:uctx.universes_lbound uctx.local vars in
  { uctx with local = uctx' }

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
let merge ?loc ~sideff rigid uctx uctx' =
  let levels = ContextSet.levels uctx' in
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
  let local = ContextSet.append uctx' uctx.local in
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
  let universes = UGraph.merge_constraints (ContextSet.constraints uctx') univs in
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

let merge_seff uctx uctx' =
  let levels = ContextSet.levels uctx' in
  let declare g =
    LSet.fold (fun u g ->
        try UGraph.add_universe ~lbound:uctx.universes_lbound ~strict:false u g
        with UGraph.AlreadyDeclared -> g)
      levels g
  in
  let initial_universes = declare uctx.initial_universes in
  let univs = declare uctx.universes in
  let universes = UGraph.merge_constraints (ContextSet.constraints uctx') univs in
  { uctx with universes; initial_universes }

let emit_side_effects eff u =
  let uctx = Safe_typing.universes_of_private eff in
  let u = demote_seff_univs (fst uctx) u in
  merge_seff u uctx

let update_sigma_univs uctx ugraph =
  let univs = UGraph.set_cumulative_sprop (elaboration_sprop_cumul()) ugraph in
  let eunivs =
    { uctx with
      initial_universes = univs;
      universes = univs }
  in
  merge_seff eunivs eunivs.local

let add_universe ?loc name strict lbound uctx u =
  let initial_universes = UGraph.add_universe ~lbound ~strict u uctx.initial_universes in
  let universes = UGraph.add_universe ~lbound ~strict u uctx.universes in
  let local = ContextSet.add_universe u uctx.local in
  let names =
    match name with
    | Some n -> add_names ?loc n u uctx.names
    | None -> add_loc u loc uctx.names
  in
  { uctx with names; local; initial_universes; universes }

let new_univ_variable ?loc rigid name uctx =
  let u = UnivGen.fresh_level () in
  let uctx =
    match rigid with
    | UnivRigid -> uctx
    | UnivFlexible allow_alg ->
      let univ_variables = LMap.add u None uctx.univ_variables in
      if allow_alg
      then
        let univ_algebraic = LSet.add u uctx.univ_algebraic in
        { uctx with univ_variables; univ_algebraic }
      else
        { uctx with univ_variables }
  in
  let uctx = add_universe ?loc name false uctx.universes_lbound uctx u in
  uctx, u

let add_global_univ uctx u = add_universe None true UGraph.Bound.Set uctx u

let fresh_instance_for_global ?loc ?(rigid=univ_flexible) ?names env uctx gr =
  let u, ctx = UnivGen.fresh_instance_for_global ?loc ?names env gr in
  u, merge ?loc ~sideff:false rigid uctx ctx

let pseudo_monomorphic = Goptions.declare_bool_option_and_ref ~depr:false
    ~key:["Pseudo";"Monomorphic";"Instances"] ~value:false

let fresh_instance_for_global ?loc ?rigid ?names env uctx gr =
  let fallback () = fresh_instance_for_global ?loc ?rigid ?names env uctx gr in
  (* with explicitly provided instance, we add constraints. no memoization since no fresh univs  *)
  if Option.has_some names || not (pseudo_monomorphic ()) then fallback ()
  else match GlobRef.Map.find_opt gr uctx.pseudo_monomorphic_instances with
    | None ->
      let u, uctx = fallback () in
      let uctx =
        { uctx with
          pseudo_monomorphic_instances =
            GlobRef.Map.add gr u uctx.pseudo_monomorphic_instances;
        }
      in
      u, uctx
    | Some u -> u, uctx

let make_with_initial_binders ~lbound univs us =
  let uctx = make ~lbound univs in
  List.fold_left
    (fun uctx { CAst.loc; v = id } ->
       fst (new_univ_variable ?loc univ_rigid (Some id) uctx))
    uctx us

let from_env ?(binders=[]) env =
  make_with_initial_binders ~lbound:(Environ.universes_lbound env) (Environ.universes env) binders

let make_flexible_variable uctx ~algebraic u =
  let {local = cstrs; univ_variables = uvars;
       univ_algebraic = avars; universes=g; } = uctx in
  assert (try LMap.find u uvars == None with Not_found -> true);
  match UGraph.choose (fun v -> not (Level.equal u v) && (algebraic || not (LSet.mem v avars))) g u with
  | Some v ->
    let uvars' = LMap.add u (Some (Universe.make v)) uvars in
    { uctx with univ_variables = uvars'; }
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
    { uctx with univ_variables = uvars'; univ_algebraic = avars' }

let make_nonalgebraic_variable uctx u =
  { uctx with univ_algebraic = LSet.remove u uctx.univ_algebraic }

let make_flexible_nonalgebraic uctx =
  { uctx with univ_algebraic = LSet.empty }

let is_sort_variable uctx s =
  match s with
  | Sorts.Type u ->
    (match universe_level u with
    | Some l as x ->
        if LSet.mem l (ContextSet.levels uctx.local) then x
        else None
    | None -> None)
  | _ -> None

let subst_univs_context_with_def def usubst (uctx, cst) =
  (LSet.diff uctx def, UnivSubst.subst_univs_constraints usubst cst)

let is_trivial_leq (l,d,r) =
  Level.is_prop l && (d == Le || d == Lt) && Level.is_set r

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
  let uctx_local = subst_univs_context_with_def def (make_subst subst) uctx.local in
  let uctx_local', univs = refresh_constraints uctx.initial_universes uctx_local in
  { uctx with
    local = uctx_local';
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
      weak_constraints = UPairSet.empty; (* weak constraints are consumed *)
      pseudo_monomorphic_instances = uctx.pseudo_monomorphic_instances;
    }

let universe_of_name uctx s =
  UNameMap.find s (fst uctx.names)

let pr_weak prl {weak_constraints=weak} =
  let open Pp in
  prlist_with_sep fnl (fun (u,v) -> prl u ++ str " ~ " ++ prl v) (UPairSet.elements weak)
