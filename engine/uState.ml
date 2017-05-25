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

module StringOrd = struct type t = string let compare = String.compare end
module UNameMap = struct
    
  include Map.Make(StringOrd)
    
  let union s t = 
    if s == t then s
    else
      merge (fun k l r -> 
        match l, r with
        | Some _, _ -> l
        | _, _ -> r) s t
end

type uinfo = {
  uname : string option;
  uloc : Loc.t option;
}

(* 2nd part used to check consistency on the fly. *)
type t =
 { uctx_names : Univ.Level.t UNameMap.t * uinfo Univ.LMap.t;
   uctx_local : Univ.universe_context_set; (** The local context of variables *)
   uctx_univ_variables : Universes.universe_opt_subst;
   (** The local universes that are unification variables *)
   uctx_univ_algebraic : Univ.universe_set; 
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

let union ctx ctx' =
  if ctx == ctx' then ctx
  else if is_empty ctx' then ctx
  else
    let local = Univ.ContextSet.union ctx.uctx_local ctx'.uctx_local in
    let names = UNameMap.union (fst ctx.uctx_names) (fst ctx'.uctx_names) in
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

let of_context_set ctx = { empty with uctx_local = ctx }

let subst ctx = ctx.uctx_univ_variables

let ugraph ctx = ctx.uctx_universes

let algebraics ctx = ctx.uctx_univ_algebraic

let constrain_variables diff ctx =
  Univ.LSet.fold
    (fun l cstrs ->
      try
        match Univ.LMap.find l ctx.uctx_univ_variables with
        | Some u -> Univ.Constraint.add (l, Univ.Eq, Option.get (Univ.Universe.level u)) cstrs
        | None -> cstrs
      with Not_found | Option.IsNone -> cstrs)
    diff Univ.Constraint.empty

let add_uctx_names ?loc s l (names, names_rev) =
  (UNameMap.add s l names, Univ.LMap.add l { uname = Some s; uloc = loc } names_rev)

let add_uctx_loc l loc (names, names_rev) =
  match loc with
  | None -> (names, names_rev)
  | Some _ -> (names, Univ.LMap.add l { uname = None; uloc = loc } names_rev)

let of_binders b =
  let ctx = empty in
  let names =
    List.fold_left (fun acc (id, l) -> add_uctx_names (Id.to_string id) l acc)
                   ctx.uctx_names b
  in { ctx with uctx_names = names }

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
              | None -> error ("Algebraic universe on the right")
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

let pr_uctx_level uctx = 
  let map, map_rev = uctx.uctx_names in 
    fun l ->
      try str (Option.get (Univ.LMap.find l map_rev).uname)
      with Not_found | Option.IsNone ->
        Universes.pr_with_global_universes l

let universe_context ?names ctx =
  match names with
  | None -> [], Univ.ContextSet.to_context ctx.uctx_local
  | Some pl ->
     let levels = Univ.ContextSet.levels ctx.uctx_local in
     let newinst, map, left =
       List.fold_right
         (fun (loc,id) (newinst, map, acc) ->
          let l =
            try UNameMap.find (Id.to_string id) (fst ctx.uctx_names)
            with Not_found ->
              user_err ?loc ~hdr:"universe_context"
                            (str"Universe " ++ Nameops.pr_id id ++ str" is not bound anymore.")
          in (l :: newinst, (id, l) :: map, Univ.LSet.remove l acc))
         pl ([], [], levels)
     in
       if not (Univ.LSet.is_empty left) then
         let n = Univ.LSet.cardinal left in
         let loc =
           try
             let info =
               Univ.LMap.find (Univ.LSet.choose left) (snd ctx.uctx_names) in
             info.uloc
           with Not_found -> None
         in
           user_err ?loc ~hdr:"universe_context"
                        ((str(CString.plural n "Universe") ++ spc () ++
			     Univ.LSet.pr (pr_uctx_level ctx) left ++
			   spc () ++ str (CString.conjugate_verb_to_be n) ++
                           str" unbound."))
      else
        let inst = Univ.Instance.of_array (Array.of_list newinst) in
        let ctx = Univ.UContext.make (inst,
          Univ.ContextSet.constraints ctx.uctx_local)
        in map, ctx

let restrict ctx vars =
  let uctx' = Universes.restrict_universe_context ctx.uctx_local vars in
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
  let u = Universes.new_univ_level (Global.current_dirpath ()) in
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

let make_flexible_variable ctx b u =
  let {uctx_univ_variables = uvars; uctx_univ_algebraic = avars} = ctx in
  let uvars' = Univ.LMap.add u None uvars in
  let avars' = 
    if b then
      let uu = Univ.Universe.make u in
      let substu_not_alg u' v =
        Option.cata (fun vu -> Univ.Universe.equal uu vu && not (Univ.LSet.mem u' avars)) false v
      in
        if not (Univ.LMap.exists substu_not_alg uvars)
        then Univ.LSet.add u avars else avars 
    else avars 
  in
  {ctx with uctx_univ_variables = uvars'; 
      uctx_univ_algebraic = avars'}

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

let add_universe_name uctx s l =
  let names' = add_uctx_names s l uctx.uctx_names in
  { uctx with uctx_names = names' }

let update_sigma_env uctx env =
  let univs = Environ.universes env in
  let eunivs =
    { uctx with uctx_initial_universes = univs;
                         uctx_universes = univs }
  in
  merge true univ_rigid eunivs eunivs.uctx_local
