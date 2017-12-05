(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open CErrors
open Util
open Names

module UNameMap = Names.Id.Map
    
type uinfo = {
  uname : Id.t option;
  uloc : Loc.t option;
}

(* 2nd part used to check consistency on the fly. *)
type t =
 { uctx_names : Universes.universe_binders * uinfo Univ.LMap.t;
   uctx_local : Univ.ContextSet.t; (** The local context of variables *)
   uctx_univ_variables : Universes.universe_opt_subst;
   (** The local universes that are unification variables *)
   uctx_univ_algebraic : Univ.LSet.t; 
   (** The subset of unification variables that can be instantiated with
        algebraic universes as they appear in inferred types only. *)
   uctx_universes : UGraph.t; (** The current graph extended with the local constraints *)
   uctx_initial_universes : UGraph.t; (** The graph at the creation of the evar_map *)
 }
  
let empty =
  { uctx_names = UNameMap.empty, Univ.LMap.empty;
    uctx_local = Univ.ContextSet.empty;
    uctx_univ_variables = Univ.LMap.empty;
    uctx_univ_algebraic = Univ.LSet.empty;
    uctx_universes = UGraph.initial_universes;
    uctx_initial_universes = UGraph.initial_universes; }

let make u =
    { empty with 
      uctx_universes = u; uctx_initial_universes = u}

let is_empty ctx =
  Univ.ContextSet.is_empty ctx.uctx_local && 
    Univ.LMap.is_empty ctx.uctx_univ_variables

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
    let local = Univ.ContextSet.union ctx.uctx_local ctx'.uctx_local in
    let names = uname_union (fst ctx.uctx_names) (fst ctx'.uctx_names) in
    let newus = Univ.LSet.diff (Univ.ContextSet.levels ctx'.uctx_local)
                               (Univ.ContextSet.levels ctx.uctx_local) in
    let newus = Univ.LSet.diff newus (Univ.LMap.domain ctx.uctx_univ_variables) in
    let declarenew g =
      Univ.LSet.fold (fun u g -> UGraph.add_universe u false g) newus g
    in
    let names_rev = Univ.LMap.union (snd ctx.uctx_names) (snd ctx'.uctx_names) in
      { uctx_names = (names, names_rev);
        uctx_local = local;
        uctx_univ_variables = 
          Univ.LMap.subst_union ctx.uctx_univ_variables ctx'.uctx_univ_variables;
        uctx_univ_algebraic = 
          Univ.LSet.union ctx.uctx_univ_algebraic ctx'.uctx_univ_algebraic;
        uctx_initial_universes = declarenew ctx.uctx_initial_universes;
        uctx_universes = 
          if local == ctx.uctx_local then ctx.uctx_universes
          else
            let cstrsr = Univ.ContextSet.constraints ctx'.uctx_local in
            UGraph.merge_constraints cstrsr (declarenew ctx.uctx_universes) }

let context_set ctx = ctx.uctx_local

let constraints ctx = snd ctx.uctx_local

let context ctx = Univ.ContextSet.to_context ctx.uctx_local

let const_univ_entry ~poly uctx =
  let open Entries in
  if poly then Polymorphic_const_entry (context uctx)
  else Monomorphic_const_entry (context_set uctx)

(* does not support cumulativity since you need more info *)
let ind_univ_entry ~poly uctx =
  let open Entries in
  if poly then Polymorphic_ind_entry (context uctx)
  else Monomorphic_ind_entry (context_set uctx)

let of_context_set ctx = { empty with uctx_local = ctx }

let subst ctx = ctx.uctx_univ_variables

let ugraph ctx = ctx.uctx_universes

let initial_graph ctx = ctx.uctx_initial_universes

let algebraics ctx = ctx.uctx_univ_algebraic

let add_uctx_names ?loc s l (names, names_rev) =
  if UNameMap.mem s names
  then user_err ?loc ~hdr:"add_uctx_names"
      Pp.(str "Universe " ++ Names.Id.print s ++ str" already bound.");
  (UNameMap.add s l names, Univ.LMap.add l { uname = Some s; uloc = loc } names_rev)

let add_uctx_loc l loc (names, names_rev) =
  match loc with
  | None -> (names, names_rev)
  | Some _ -> (names, Univ.LMap.add l { uname = None; uloc = loc } names_rev)

let of_binders b =
  let ctx = empty in
  let rmap =
    UNameMap.fold (fun id l rmap ->
        Univ.LMap.add l { uname = Some id; uloc = None } rmap)
      b Univ.LMap.empty
  in
  { ctx with uctx_names = b, rmap }

let universe_binders ctx = fst ctx.uctx_names

let instantiate_variable l b v =
  try v := Univ.LMap.update l (Some b) !v
  with Not_found -> assert false

exception UniversesDiffer

let process_universe_constraints ctx cstrs =
  let open Univ in
  let univs = ctx.uctx_universes in
  let vars = ref ctx.uctx_univ_variables in
  let normalize = Universes.normalize_universe_opt_subst vars in
  let is_local l = Univ.LMap.mem l !vars in
  let varinfo x =
    match Univ.Universe.level x with
    | None -> Inl x
    | Some l -> Inr l
  in
  let equalize_variables fo l l' r r' local =
    (** Assumes l = [l',0] and r = [r',0] *)
    let () =
      if is_local l' then
        instantiate_variable l' r vars
      else if is_local r' then
        instantiate_variable r' l vars
      else if not (UGraph.check_eq_level univs l' r') then
        (* Two rigid/global levels, none of them being local,
            one of them being Prop/Set, disallow *)
        if Univ.Level.is_small l' || Univ.Level.is_small r' then
          raise (Univ.UniverseInconsistency (Univ.Eq, l, r, None))
        else if fo then
          raise UniversesDiffer
    in
    Univ.enforce_eq_level l' r' local
  in
  let equalize_universes l r local = match varinfo l, varinfo r with
  | Inr l', Inr r' -> equalize_variables false l l' r r' local
  | Inr l, Inl r | Inl r, Inr l ->
    let alg = Univ.LSet.mem l ctx.uctx_univ_algebraic in
    let inst = Univ.univ_level_rem l r r in
      if alg then (instantiate_variable l inst vars; local)
      else
        let lu = Univ.Universe.make l in
        if Univ.univ_level_mem l r then
          Univ.enforce_leq inst lu local
        else raise (Univ.UniverseInconsistency (Univ.Eq, lu, r, None))
  | Inl _, Inl _ (* both are algebraic *) ->
    if UGraph.check_eq univs l r then local
    else raise (Univ.UniverseInconsistency (Univ.Eq, l, r, None))
  in
  let unify_universes (l, d, r) local =
    let l = normalize l and r = normalize r in
      if Univ.Universe.equal l r then local
      else 
          match d with
          | Universes.ULe ->
            if UGraph.check_leq univs l r then
              (** Keep Prop/Set <= var around if var might be instantiated by prop or set
                  later. *)
              match Univ.Universe.level l, Univ.Universe.level r with
              | Some l, Some r ->
                Univ.Constraint.add (l, Univ.Le, r) local
              | _ -> local
            else
              begin match Univ.Universe.level r with
              | None -> user_err Pp.(str "Algebraic universe on the right")
              | Some r' ->
                if Univ.Level.is_small r' then
                  let levels = Univ.Universe.levels l in
                  let fold l' local =
                    let l = Univ.Universe.make l' in
                    if Univ.Level.is_small l' || is_local l' then
                      equalize_variables false l l' r r' local
                    else raise (Univ.UniverseInconsistency (Univ.Le, l, r, None))
                  in
                  Univ.LSet.fold fold levels local
                else
                  Univ.enforce_leq l r local
              end
          | Universes.ULub ->
            begin match Universe.level l, Universe.level r with
            | Some l', Some r' ->
              equalize_variables true l l' r r' local
            | _, _ -> assert false
            end
          | Universes.UEq -> equalize_universes l r local
  in
  let local = 
    Universes.Constraints.fold unify_universes cstrs Univ.Constraint.empty
  in
    !vars, local

let add_constraints ctx cstrs =
  let univs, local = ctx.uctx_local in
  let cstrs' = Univ.Constraint.fold (fun (l,d,r) acc -> 
    let l = Univ.Universe.make l and r = Univ.Universe.make r in
    let cstr' = 
      if d == Univ.Lt then (Univ.Universe.super l, Universes.ULe, r)
      else (l, (if d == Univ.Le then Universes.ULe else Universes.UEq), r)
    in Universes.Constraints.add cstr' acc)
    cstrs Universes.Constraints.empty
  in
  let vars, local' = process_universe_constraints ctx cstrs' in
    { ctx with uctx_local = (univs, Univ.Constraint.union local local');
      uctx_univ_variables = vars;
      uctx_universes = UGraph.merge_constraints local' ctx.uctx_universes }

(* let addconstrkey = Profile.declare_profile "add_constraints_context";; *)
(* let add_constraints_context = Profile.profile2 addconstrkey add_constraints_context;; *)

let add_universe_constraints ctx cstrs =
  let univs, local = ctx.uctx_local in
  let vars, local' = process_universe_constraints ctx cstrs in
    { ctx with uctx_local = (univs, Univ.Constraint.union local local');
      uctx_univ_variables = vars;
      uctx_universes = UGraph.merge_constraints local' ctx.uctx_universes }

let constrain_variables diff ctx =
  let univs, local = ctx.uctx_local in
  let univs, vars, local =
    Univ.LSet.fold
      (fun l (univs, vars, cstrs) ->
        try
          match Univ.LMap.find l vars with
          | Some u ->
             (Univ.LSet.add l univs,
              Univ.LMap.remove l vars,
              Univ.Constraint.add (l, Univ.Eq, Option.get (Univ.Universe.level u)) cstrs)
          | None -> (univs, vars, cstrs)
        with Not_found | Option.IsNone -> (univs, vars, cstrs))
      diff (univs, ctx.uctx_univ_variables, local)
  in
  { ctx with uctx_local = (univs, local); uctx_univ_variables = vars }
  
let reference_of_level uctx =
  let map, map_rev = uctx.uctx_names in 
    fun l ->
      try Libnames.Ident (Loc.tag @@ Option.get (Univ.LMap.find l map_rev).uname)
      with Not_found | Option.IsNone ->
        Universes.reference_of_level l

let pr_uctx_level uctx l =
  Libnames.pr_reference (reference_of_level uctx l)

type universe_decl =
  (Names.Id.t Loc.located list, Univ.Constraint.t) Misctypes.gen_universe_decl

let error_unbound_universes left uctx =
  let open Univ in
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
  let open Univ in
  let levels = ContextSet.levels uctx.uctx_local in
  let newinst, left =
    List.fold_right
      (fun (loc,id) (newinst, acc) ->
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
    let open Univ in
    let left = List.fold_left (fun left (loc,id) ->
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
  let open Misctypes in
  let () =
    let names = decl.univdecl_instance in
    let extensible = decl.univdecl_extensible_instance in
    check_universe_context_set ~names ~extensible uctx
  in
  if not decl.univdecl_extensible_constraints then
    check_implication uctx
      decl.univdecl_constraints
      (Univ.ContextSet.constraints uctx.uctx_local);
  uctx.uctx_local

let check_univ_decl ~poly uctx decl =
  let open Misctypes in
  let ctx =
    let names = decl.univdecl_instance in
    let extensible = decl.univdecl_extensible_instance in
    if poly
    then Entries.Polymorphic_const_entry (universe_context ~names ~extensible uctx)
    else
      let () = check_universe_context_set ~names ~extensible uctx in
      Entries.Monomorphic_const_entry uctx.uctx_local
  in
  if not decl.univdecl_extensible_constraints then
    check_implication uctx
      decl.univdecl_constraints
      (Univ.ContextSet.constraints uctx.uctx_local);
  ctx

let restrict ctx vars =
  let vars = Names.Id.Map.fold (fun na l vars -> Univ.LSet.add l vars)
      (fst ctx.uctx_names) vars
  in
  let uctx' = Univops.restrict_universe_context ctx.uctx_local vars in
  { ctx with uctx_local = uctx' }

type rigid = 
  | UnivRigid
  | UnivFlexible of bool (** Is substitution by an algebraic ok? *)

let univ_rigid = UnivRigid
let univ_flexible = UnivFlexible false
let univ_flexible_alg = UnivFlexible true

let merge ?loc sideff rigid uctx ctx' =
  let open Univ in
  let levels = ContextSet.levels ctx' in
  let uctx = if sideff then uctx else
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
    if sideff then uctx.uctx_local
    else ContextSet.append ctx' uctx.uctx_local
  in
  let declare g =
    LSet.fold (fun u g ->
               try UGraph.add_universe u false g
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
  { uctx with uctx_univ_variables = Univ.LMap.subst_union uctx.uctx_univ_variables s }

let emit_side_effects eff u =
  let uctxs = Safe_typing.universes_of_private eff in
  List.fold_left (merge true univ_rigid) u uctxs

let new_univ_variable ?loc rigid name
  ({ uctx_local = ctx; uctx_univ_variables = uvars; uctx_univ_algebraic = avars} as uctx) =
  let u = Universes.new_univ_level () in
  let ctx' = Univ.ContextSet.add_universe u ctx in
  let uctx', pred =
    match rigid with
    | UnivRigid -> uctx, true
    | UnivFlexible b -> 
      let uvars' = Univ.LMap.add u None uvars in
        if b then {uctx with uctx_univ_variables = uvars';
          uctx_univ_algebraic = Univ.LSet.add u avars}, false
        else {uctx with uctx_univ_variables = uvars'}, false
  in
  let names = 
    match name with
    | Some n -> add_uctx_names ?loc n u uctx.uctx_names
    | None -> add_uctx_loc u loc uctx.uctx_names
  in
  let initial =
    UGraph.add_universe u false uctx.uctx_initial_universes
  in                                                 
  let uctx' =
    {uctx' with uctx_names = names; uctx_local = ctx';
                uctx_universes = UGraph.add_universe u false uctx.uctx_universes;
                uctx_initial_universes = initial}
  in uctx', u

let add_global_univ uctx u =
  let initial =
    UGraph.add_universe u true uctx.uctx_initial_universes
  in
  let univs = 
    UGraph.add_universe u true uctx.uctx_universes
  in
  { uctx with uctx_local = Univ.ContextSet.add_universe u uctx.uctx_local;
                                     uctx_initial_universes = initial;
                                     uctx_universes = univs }

let make_flexible_variable ctx ~algebraic u =
  let {uctx_local = cstrs; uctx_univ_variables = uvars; uctx_univ_algebraic = avars} = ctx in
  let uvars' = Univ.LMap.add u None uvars in
  let avars' = 
    if algebraic then
      let uu = Univ.Universe.make u in
      let substu_not_alg u' v =
        Option.cata (fun vu -> Univ.Universe.equal uu vu && not (Univ.LSet.mem u' avars)) false v
      in
      let has_upper_constraint () =
        Univ.Constraint.exists
          (fun (l,d,r) -> d == Univ.Lt && Univ.Level.equal l u)
          (Univ.ContextSet.constraints cstrs)
      in
        if not (Univ.LMap.exists substu_not_alg uvars || has_upper_constraint ())
        then Univ.LSet.add u avars else avars 
    else avars 
  in
  {ctx with uctx_univ_variables = uvars'; 
      uctx_univ_algebraic = avars'}

let make_flexible_nonalgebraic ctx =
  {ctx with uctx_univ_algebraic = Univ.LSet.empty}

let is_sort_variable uctx s = 
  match s with 
  | Sorts.Type u -> 
    (match Univ.universe_level u with
    | Some l as x -> 
        if Univ.LSet.mem l (Univ.ContextSet.levels uctx.uctx_local) then x
        else None
    | None -> None)
  | _ -> None

let subst_univs_context_with_def def usubst (ctx, cst) =
  (Univ.LSet.diff ctx def, Univ.subst_univs_constraints usubst cst)

let normalize_variables uctx =
  let normalized_variables, undef, def, subst = 
    Universes.normalize_univ_variables uctx.uctx_univ_variables 
  in
  let ctx_local = subst_univs_context_with_def def (Univ.make_subst subst) uctx.uctx_local in
  let ctx_local', univs = Universes.refresh_constraints uctx.uctx_initial_universes ctx_local in
    subst, { uctx with uctx_local = ctx_local';
      uctx_univ_variables = normalized_variables;
      uctx_universes = univs }

let abstract_undefined_variables uctx =
  let vars' = 
    Univ.LMap.fold (fun u v acc ->
      if v == None then Univ.LSet.remove u acc
      else acc)
    uctx.uctx_univ_variables uctx.uctx_univ_algebraic
  in { uctx with uctx_local = Univ.ContextSet.empty;
      uctx_univ_algebraic = vars' }

let fix_undefined_variables uctx =
  let algs', vars' = 
    Univ.LMap.fold (fun u v (algs, vars as acc) ->
      if v == None then (Univ.LSet.remove u algs, Univ.LMap.remove u vars)
      else acc)
      uctx.uctx_univ_variables 
      (uctx.uctx_univ_algebraic, uctx.uctx_univ_variables)
  in
  { uctx with uctx_univ_variables = vars';
    uctx_univ_algebraic = algs' }

let refresh_undefined_univ_variables uctx =
  let subst, ctx' = Universes.fresh_universe_context_set_instance uctx.uctx_local in
  let alg = Univ.LSet.fold (fun u acc -> Univ.LSet.add (Univ.subst_univs_level_level subst u) acc) 
    uctx.uctx_univ_algebraic Univ.LSet.empty 
  in
  let vars = 
    Univ.LMap.fold
      (fun u v acc ->
        Univ.LMap.add (Univ.subst_univs_level_level subst u) 
          (Option.map (Univ.subst_univs_level_universe subst) v) acc)
      uctx.uctx_univ_variables Univ.LMap.empty
  in
  let declare g = Univ.LSet.fold (fun u g -> UGraph.add_universe u false g)
                                   (Univ.ContextSet.levels ctx') g in
  let initial = declare uctx.uctx_initial_universes in
  let univs = declare UGraph.initial_universes in
  let uctx' = {uctx_names = uctx.uctx_names;
               uctx_local = ctx'; 
               uctx_univ_variables = vars; uctx_univ_algebraic = alg;
               uctx_universes = univs;
               uctx_initial_universes = initial } in
    uctx', subst

let normalize uctx = 
  let ((vars',algs'), us') = 
    Universes.normalize_context_set uctx.uctx_local uctx.uctx_univ_variables
				    uctx.uctx_univ_algebraic
  in
  if Univ.ContextSet.equal us' uctx.uctx_local then uctx
  else
    let us', universes =
      Universes.refresh_constraints uctx.uctx_initial_universes us'
    in
      { uctx_names = uctx.uctx_names;
        uctx_local = us'; 
        uctx_univ_variables = vars'; 
        uctx_univ_algebraic = algs';
        uctx_universes = universes;
        uctx_initial_universes = uctx.uctx_initial_universes }

let universe_of_name uctx s = 
  UNameMap.find s (fst uctx.uctx_names)

let update_sigma_env uctx env =
  let univs = Environ.universes env in
  let eunivs =
    { uctx with uctx_initial_universes = univs;
                         uctx_universes = univs }
  in
  merge true univ_rigid eunivs eunivs.uctx_local
