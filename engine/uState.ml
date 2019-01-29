(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
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
 { uctx_names : UnivNames.universe_binders * uinfo LMap.t;
   uctx_local : ContextSet.t; (** The local context of variables *)
   uctx_seff_univs : LSet.t; (** Local universes used through private constants *)
   uctx_univ_variables : UnivSubst.universe_opt_subst;
   (** The local universes that are unification variables *)
   uctx_univ_algebraic : LSet.t;
   (** The subset of unification variables that can be instantiated with
        algebraic universes as they appear in inferred types only. *)
   uctx_universes : UGraph.t; (** The current graph extended with the local constraints *)
   uctx_universes_lbound : Univ.Level.t; (** The lower bound on universes (e.g. Set or Prop) *)
   uctx_initial_universes : UGraph.t; (** The graph at the creation of the evar_map *)
   uctx_weak_constraints : UPairSet.t
 }

let initial_sprop_cumulative = UGraph.make_sprop_cumulative UGraph.initial_universes

let empty =
  { uctx_names = UNameMap.empty, LMap.empty;
    uctx_local = ContextSet.empty;
    uctx_seff_univs = LSet.empty;
    uctx_univ_variables = LMap.empty;
    uctx_univ_algebraic = LSet.empty;
    uctx_universes = initial_sprop_cumulative;
    uctx_universes_lbound = Univ.Level.set;
    uctx_initial_universes = initial_sprop_cumulative;
    uctx_weak_constraints = UPairSet.empty; }

let elaboration_sprop_cumul =
  Goptions.declare_bool_option_and_ref ~depr:false ~name:"SProp cumulativity during elaboration"
    ~key:["Elaboration";"StrictProp";"Cumulativity"] ~value:true

let make ~lbound u =
  let u = if elaboration_sprop_cumul () then UGraph.make_sprop_cumulative u else u in
    { empty with
      uctx_universes = u;
      uctx_universes_lbound = lbound;
      uctx_initial_universes = u}

let is_empty ctx =
  ContextSet.is_empty ctx.uctx_local &&
    LMap.is_empty ctx.uctx_univ_variables

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
    let local = ContextSet.union ctx.uctx_local ctx'.uctx_local in
    let seff = LSet.union ctx.uctx_seff_univs ctx'.uctx_seff_univs in
    let names = uname_union (fst ctx.uctx_names) (fst ctx'.uctx_names) in
    let newus = LSet.diff (ContextSet.levels ctx'.uctx_local)
                               (ContextSet.levels ctx.uctx_local) in
    let newus = LSet.diff newus (LMap.domain ctx.uctx_univ_variables) in
    let weak = UPairSet.union ctx.uctx_weak_constraints ctx'.uctx_weak_constraints in
    let declarenew g =
      LSet.fold (fun u g -> UGraph.add_universe u ~lbound:ctx.uctx_universes_lbound ~strict:false g) newus g
    in
    let names_rev = LMap.lunion (snd ctx.uctx_names) (snd ctx'.uctx_names) in
      { uctx_names = (names, names_rev);
        uctx_local = local;
        uctx_seff_univs = seff;
        uctx_univ_variables = 
          LMap.subst_union ctx.uctx_univ_variables ctx'.uctx_univ_variables;
        uctx_univ_algebraic = 
          LSet.union ctx.uctx_univ_algebraic ctx'.uctx_univ_algebraic;
        uctx_initial_universes = declarenew ctx.uctx_initial_universes;
        uctx_universes = 
          (if local == ctx.uctx_local then ctx.uctx_universes
           else
             let cstrsr = ContextSet.constraints ctx'.uctx_local in
             UGraph.merge_constraints cstrsr (declarenew ctx.uctx_universes));
        uctx_universes_lbound = ctx.uctx_universes_lbound;
        uctx_weak_constraints = weak}

let context_set ctx = ctx.uctx_local

let constraints ctx = snd ctx.uctx_local

let context ctx = ContextSet.to_context ctx.uctx_local

let univ_entry ~poly uctx =
  let open Entries in
  if poly then
    let (binders, _) = uctx.uctx_names in
    let uctx = context uctx in
    let nas = UnivNames.compute_instance_binders (UContext.instance uctx) binders in
    Polymorphic_entry (nas, uctx)
  else Monomorphic_entry (context_set uctx)

let const_univ_entry = univ_entry

let of_context_set ctx = { empty with uctx_local = ctx }

let subst ctx = ctx.uctx_univ_variables

let ugraph ctx = ctx.uctx_universes

let initial_graph ctx = ctx.uctx_initial_universes

let algebraics ctx = ctx.uctx_univ_algebraic

let add_uctx_names ?loc s l (names, names_rev) =
  if UNameMap.mem s names
  then user_err ?loc ~hdr:"add_uctx_names"
      Pp.(str "Universe " ++ Names.Id.print s ++ str" already bound.");
  (UNameMap.add s l names, LMap.add l { uname = Some s; uloc = loc } names_rev)

let add_uctx_loc l loc (names, names_rev) =
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
  { ctx with uctx_names = b, rmap }

let invent_name (named,cnt) u =
  let rec aux i =
    let na = Id.of_string ("u"^(string_of_int i)) in
    if Id.Map.mem na named then aux (i+1)
    else Id.Map.add na u named, i+1
  in
  aux cnt

let universe_binders ctx =
  let named, rev = ctx.uctx_names in
  let named, _ = LSet.fold (fun u named ->
      match LMap.find u rev with
      | exception Not_found -> (* not sure if possible *) invent_name named u
      | { uname = None } -> invent_name named u
      | { uname = Some _ } -> named)
      (ContextSet.levels ctx.uctx_local) (named, 0)
  in
  named

let instantiate_variable l b v =
  try v := LMap.set l (Some b) !v
  with Not_found -> assert false

exception UniversesDiffer

let drop_weak_constraints = ref false

let process_universe_constraints ctx cstrs =
  let open UnivSubst in
  let open UnivProblem in
  let univs = ctx.uctx_universes in
  let vars = ref ctx.uctx_univ_variables in
  let weak = ref ctx.uctx_weak_constraints in
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
    let alg = LSet.mem l ctx.uctx_univ_algebraic in
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
            if UGraph.check_leq univs l r then
              (* Keep Prop/Set <= var around if var might be instantiated by prop or set
                 later. *)
              match Universe.level l, Universe.level r with
              | Some l, Some r ->
                Constraint.add (l, Le, r) local
              | _ -> local
            else
              begin match Universe.level r with
              | None -> user_err Pp.(str "Algebraic universe on the right")
              | Some r' ->
                if Level.is_small r' then
                  if not (Universe.is_levels l)
                  then
                    raise (UniverseInconsistency (Le, l, r, None))
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
                  enforce_leq l r local
              end
          | ULub (l, r) ->
              equalize_variables true (Universe.make l) l (Universe.make r) r local
          | UWeak (l, r) ->
            if not !drop_weak_constraints then weak := UPairSet.add (l,r) !weak; local
          | UEq (l, r) -> equalize_universes l r local
  in
  let local = 
    UnivProblem.Set.fold unify_universes cstrs Constraint.empty
  in
    !vars, !weak, local

let add_constraints ctx cstrs =
  let univs, local = ctx.uctx_local in
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
    uctx_local = (univs, Constraint.union local local');
    uctx_univ_variables = vars;
    uctx_universes = UGraph.merge_constraints local' ctx.uctx_universes;
    uctx_weak_constraints = weak; }

(* let addconstrkey = CProfile.declare_profile "add_constraints_context";; *)
(* let add_constraints_context = CProfile.profile2 addconstrkey add_constraints_context;; *)

let add_universe_constraints ctx cstrs =
  let univs, local = ctx.uctx_local in
  let vars, weak, local' = process_universe_constraints ctx cstrs in
  { ctx with
    uctx_local = (univs, Constraint.union local local');
    uctx_univ_variables = vars;
    uctx_universes = UGraph.merge_constraints local' ctx.uctx_universes;
    uctx_weak_constraints = weak; }

let constrain_variables diff ctx =
  let univs, local = ctx.uctx_local in
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
      diff (univs, ctx.uctx_univ_variables, local)
  in
  { ctx with uctx_local = (univs, local); uctx_univ_variables = vars }
  
let qualid_of_level uctx =
  let map, map_rev = uctx.uctx_names in 
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
        LMap.find (LSet.choose left) (snd uctx.uctx_names) in
      info.uloc
    with Not_found -> None
  in
  user_err ?loc ~hdr:"universe_context"
    ((str(CString.plural n "Universe") ++ spc () ++
      LSet.pr (pr_uctx_level uctx) left ++
      spc () ++ str (CString.conjugate_verb_to_be n) ++
      str" unbound."))

let universe_context ~names ~extensible uctx =
  let levels = ContextSet.levels uctx.uctx_local in
  let newinst, left =
    List.fold_right
      (fun { CAst.loc; v = id } (newinst, acc) ->
         let l =
           try UNameMap.find id (fst uctx.uctx_names)
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
    let ctx = UContext.make (inst, ContextSet.constraints uctx.uctx_local) in
    ctx

let check_universe_context_set ~names ~extensible uctx =
  if extensible then ()
  else
    let left = List.fold_left (fun left { CAst.loc; v = id } ->
        let l =
          try UNameMap.find id (fst uctx.uctx_names)
          with Not_found -> assert false
        in LSet.remove l left)
        (ContextSet.levels uctx.uctx_local) names
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
      (ContextSet.constraints uctx.uctx_local);
  uctx.uctx_local

let check_univ_decl ~poly uctx decl =
  let ctx =
    let names = decl.univdecl_instance in
    let extensible = decl.univdecl_extensible_instance in
    if poly then
      let (binders, _) = uctx.uctx_names in
      let uctx = universe_context ~names ~extensible uctx in
      let nas = UnivNames.compute_instance_binders (UContext.instance uctx) binders in
      Entries.Polymorphic_entry (nas, uctx)
    else
      let () = check_universe_context_set ~names ~extensible uctx in
      Entries.Monomorphic_entry uctx.uctx_local
  in
  if not decl.univdecl_extensible_constraints then
    check_implication uctx
      decl.univdecl_constraints
      (ContextSet.constraints uctx.uctx_local);
  ctx

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
      not ((Level.equal l lbound && d == Le) || (Level.is_prop l && d == Lt && Level.is_set r))) csts in
  (LSet.inter univs keep, csts)

let restrict ctx vars =
  let vars = LSet.union vars ctx.uctx_seff_univs in
  let vars = Names.Id.Map.fold (fun na l vars -> LSet.add l vars)
      (fst ctx.uctx_names) vars
  in
  let uctx' = restrict_universe_context ~lbound:ctx.uctx_universes_lbound ctx.uctx_local vars in
  { ctx with uctx_local = uctx' }

let demote_seff_univs entry uctx =
  let open Entries in
  match entry.const_entry_universes with
  | Polymorphic_entry _ -> uctx
  | Monomorphic_entry (univs, _) ->
    let seff = LSet.union uctx.uctx_seff_univs univs in
    { uctx with uctx_seff_univs = seff }

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
let merge ?loc ~sideff ~extend rigid uctx ctx' =
  let levels = ContextSet.levels ctx' in
  let uctx =
    if not extend then uctx else
    match rigid with
    | UnivRigid -> uctx
    | UnivFlexible b ->
      let fold u accu =
        if LMap.mem u accu then accu
        else LMap.add u None accu
      in
      let uvars' = LSet.fold fold levels uctx.uctx_univ_variables in
        if b then
          { uctx with uctx_univ_variables = uvars';
          uctx_univ_algebraic = LSet.union uctx.uctx_univ_algebraic levels }
        else { uctx with uctx_univ_variables = uvars' }
  in
  let uctx_local =
    if not extend then uctx.uctx_local
    else ContextSet.append ctx' uctx.uctx_local in
  let declare g =
    LSet.fold (fun u g ->
               try UGraph.add_universe ~lbound:uctx.uctx_universes_lbound ~strict:false u g
               with UGraph.AlreadyDeclared when sideff -> g)
              levels g
  in
  let uctx_names =
    let fold u accu =
      let modify _ info = match info.uloc with
      | None -> { info with uloc = loc }
      | Some _ -> info
      in
      try LMap.modify u modify accu
      with Not_found -> LMap.add u { uname = None; uloc = loc } accu
    in
    (fst uctx.uctx_names, LSet.fold fold levels (snd uctx.uctx_names))
  in
  let initial = declare uctx.uctx_initial_universes in
  let univs = declare uctx.uctx_universes in
  let uctx_universes = UGraph.merge_constraints (ContextSet.constraints ctx') univs in
  { uctx with uctx_names; uctx_local; uctx_universes;
              uctx_initial_universes = initial }

let merge_subst uctx s =
  { uctx with uctx_univ_variables = LMap.subst_union uctx.uctx_univ_variables s }

let emit_side_effects eff u =
  let uctxs = Safe_typing.universes_of_private eff in
  List.fold_left (merge ~sideff:true ~extend:false univ_rigid) u uctxs

let new_univ_variable ?loc rigid name
  ({ uctx_local = ctx; uctx_univ_variables = uvars; uctx_univ_algebraic = avars} as uctx) =
  let u = UnivGen.fresh_level () in
  let ctx' = ContextSet.add_universe u ctx in
  let uctx', pred =
    match rigid with
    | UnivRigid -> uctx, true
    | UnivFlexible b -> 
      let uvars' = LMap.add u None uvars in
        if b then {uctx with uctx_univ_variables = uvars';
          uctx_univ_algebraic = LSet.add u avars}, false
        else {uctx with uctx_univ_variables = uvars'}, false
  in
  let names = 
    match name with
    | Some n -> add_uctx_names ?loc n u uctx.uctx_names
    | None -> add_uctx_loc u loc uctx.uctx_names
  in
  let initial =
    UGraph.add_universe ~lbound:uctx.uctx_universes_lbound ~strict:false u uctx.uctx_initial_universes
  in                                                 
  let uctx' =
    {uctx' with uctx_names = names; uctx_local = ctx';
                uctx_universes = UGraph.add_universe ~lbound:uctx.uctx_universes_lbound ~strict:false
                    u uctx.uctx_universes;
                uctx_initial_universes = initial}
  in uctx', u

let make_with_initial_binders ~lbound e us =
  let uctx = make ~lbound e in
  List.fold_left
    (fun uctx { CAst.loc; v = id } ->
       fst (new_univ_variable ?loc univ_rigid (Some id) uctx))
    uctx us

let add_global_univ uctx u =
  let initial =
    UGraph.add_universe ~lbound:Univ.Level.set ~strict:true u uctx.uctx_initial_universes
  in
  let univs = 
    UGraph.add_universe ~lbound:Univ.Level.set ~strict:true u uctx.uctx_universes
  in
  { uctx with uctx_local = ContextSet.add_universe u uctx.uctx_local;
                                     uctx_initial_universes = initial;
                                     uctx_universes = univs }

let make_flexible_variable ctx ~algebraic u =
  let {uctx_local = cstrs; uctx_univ_variables = uvars;
       uctx_univ_algebraic = avars; uctx_universes=g; } = ctx in
  assert (try LMap.find u uvars == None with Not_found -> true);
  match UGraph.choose (fun v -> not (Level.equal u v) && (algebraic || not (LSet.mem v avars))) g u with
  | Some v ->
    let uvars' = LMap.add u (Some (Universe.make v)) uvars in
    { ctx with uctx_univ_variables = uvars'; }
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
    {ctx with uctx_univ_variables = uvars';
              uctx_univ_algebraic = avars'}

let make_nonalgebraic_variable ctx u =
  { ctx with uctx_univ_algebraic = LSet.remove u ctx.uctx_univ_algebraic }

let make_flexible_nonalgebraic ctx =
  {ctx with uctx_univ_algebraic = LSet.empty}

let is_sort_variable uctx s = 
  match s with 
  | Sorts.Type u -> 
    (match universe_level u with
    | Some l as x -> 
        if LSet.mem l (ContextSet.levels uctx.uctx_local) then x
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
    UnivSubst.normalize_univ_variables uctx.uctx_univ_variables
  in
  let ctx_local = subst_univs_context_with_def def (make_subst subst) uctx.uctx_local in
  let ctx_local', univs = refresh_constraints uctx.uctx_initial_universes ctx_local in
    subst, { uctx with uctx_local = ctx_local';
      uctx_univ_variables = normalized_variables;
      uctx_universes = univs }

let abstract_undefined_variables uctx =
  let vars' = 
    LMap.fold (fun u v acc ->
      if v == None then LSet.remove u acc
      else acc)
    uctx.uctx_univ_variables uctx.uctx_univ_algebraic
  in { uctx with uctx_local = ContextSet.empty;
      uctx_univ_algebraic = vars' }

let fix_undefined_variables uctx =
  let algs', vars' = 
    LMap.fold (fun u v (algs, vars as acc) ->
      if v == None then (LSet.remove u algs, LMap.remove u vars)
      else acc)
      uctx.uctx_univ_variables 
      (uctx.uctx_univ_algebraic, uctx.uctx_univ_variables)
  in
  { uctx with uctx_univ_variables = vars';
    uctx_univ_algebraic = algs' }

let refresh_undefined_univ_variables uctx =
  let subst, ctx' = UnivGen.fresh_universe_context_set_instance uctx.uctx_local in
  let subst_fn u = subst_univs_level_level subst u in
  let alg = LSet.fold (fun u acc -> LSet.add (subst_fn u) acc)
    uctx.uctx_univ_algebraic LSet.empty
  in
  let vars = 
    LMap.fold
      (fun u v acc ->
        LMap.add (subst_fn u)
          (Option.map (subst_univs_level_universe subst) v) acc)
      uctx.uctx_univ_variables LMap.empty
  in
  let weak = UPairSet.fold (fun (u,v) acc -> UPairSet.add (subst_fn u, subst_fn v) acc) uctx.uctx_weak_constraints UPairSet.empty in
  let lbound = uctx.uctx_universes_lbound in
  let declare g = LSet.fold (fun u g -> UGraph.add_universe u ~lbound ~strict:false g)
      (ContextSet.levels ctx') g in
  let initial = declare uctx.uctx_initial_universes in
  let univs = declare UGraph.initial_universes in
  let uctx' = {uctx_names = uctx.uctx_names;
               uctx_local = ctx';
               uctx_seff_univs = uctx.uctx_seff_univs;
               uctx_univ_variables = vars; uctx_univ_algebraic = alg;
               uctx_universes = univs;
               uctx_universes_lbound = lbound;
               uctx_initial_universes = initial;
               uctx_weak_constraints = weak; } in
    uctx', subst

let minimize uctx =
  let open UnivMinim in
  let lbound = uctx.uctx_universes_lbound in
  let ((vars',algs'), us') =
    normalize_context_set ~lbound uctx.uctx_universes uctx.uctx_local uctx.uctx_univ_variables
      uctx.uctx_univ_algebraic uctx.uctx_weak_constraints
  in
  if ContextSet.equal us' uctx.uctx_local then uctx
  else
    let us', universes =
      refresh_constraints uctx.uctx_initial_universes us'
    in
      { uctx_names = uctx.uctx_names;
        uctx_local = us';
        uctx_seff_univs = uctx.uctx_seff_univs; (* not sure about this *)
        uctx_univ_variables = vars'; 
        uctx_univ_algebraic = algs';
        uctx_universes = universes;
        uctx_universes_lbound = lbound;
        uctx_initial_universes = uctx.uctx_initial_universes;
        uctx_weak_constraints = UPairSet.empty; (* weak constraints are consumed *) }

let universe_of_name uctx s = 
  UNameMap.find s (fst uctx.uctx_names)

let update_sigma_env uctx env =
  let univs = UGraph.make_sprop_cumulative (Environ.universes env) in
  let eunivs =
    { uctx with uctx_initial_universes = univs;
                         uctx_universes = univs }
  in
  merge ~sideff:true ~extend:false univ_rigid eunivs eunivs.uctx_local

let pr_weak prl {uctx_weak_constraints=weak} =
  let open Pp in
  prlist_with_sep fnl (fun (u,v) -> prl u ++ str " ~ " ++ prl v) (UPairSet.elements weak)
