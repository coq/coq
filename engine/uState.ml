(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open CErrors
open Util
open Names
open Univ
open UVars

module UnivFlex = UnivFlex

type universes_entry =
| Monomorphic_entry of Univ.ContextSet.t
| Polymorphic_entry of UVars.UContext.t

module UNameMap = Names.Id.Map

type uinfo = {
  uname : Id.t option;
  uloc : Loc.t option;
}

type quality = QVar of Sorts.QVar.t | QProp | QSProp | QType

let sort_inconsistency ?explain cst l r =
  let explain = Option.map (fun p -> UGraph.Other p) explain in
  raise (UGraph.UniverseInconsistency (cst, l, r, explain))

let pr_quality = function
  | QVar v -> Sorts.QVar.pr v
  | QProp -> Pp.str "Prop"
  | QSProp -> Pp.str "SProp"
  | QType -> Pp.str "Type"

module QState : sig
  type t
  type elt = Sorts.QVar.t
  val empty : t
  val union : fail:(t -> quality -> quality -> t) -> t -> t -> t
  val add : elt -> t -> t
  val repr : elt -> t -> quality
  val unify_quality : fail:(unit -> t) -> Conversion.conv_pb -> quality -> quality -> t -> t
  val is_above_prop : elt -> t -> bool
  val collapse : t -> t
  val pr : t -> Pp.t
end =
struct

module QSet = Set.Make(Sorts.QVar)
module QMap = Map.Make(Sorts.QVar)

type t = {
  qmap : quality option QMap.t;
  (* TODO: use a persistent union-find structure *)
  above : QSet.t;
  (** Set of quality variables known to be either in Prop or Type.
      If q ∈ above then it must map to None in qmap. *)
}

type elt = Sorts.QVar.t

let empty = { qmap = QMap.empty; above = QSet.empty }

let quality_eq a b = match a, b with
  | QProp, QProp | QSProp, QSProp | QType, QType -> true
  | QVar q1, QVar q2 -> Sorts.QVar.equal q1 q2
  | (QVar _ | QProp | QSProp | QType), _ -> false

let rec repr q m = match QMap.find q m.qmap with
| None -> QVar q
| Some (QVar q) -> repr q m
| Some (QProp | QSProp | QType as q) -> q
| exception Not_found ->
(*   let () = assert !Flags.in_debugger in *) (* FIXME *)
  QVar q

let is_above_prop q m = QSet.mem q m.above

let set q qv m =
  let q = repr q m in
  let q = match q with QVar q -> q | QProp | QSProp | QType -> assert false in
  let qv = match qv with QVar qv -> repr qv m | (QSProp | QProp | QType as qv) -> qv in
  match q, qv with
  | q, QVar qv ->
    if Sorts.QVar.equal q qv then Some m
    else
      let above =
        if QSet.mem q m.above then QSet.add qv (QSet.remove q m.above)
        else m.above
      in
      Some { qmap = QMap.add q (Some (QVar qv)) m.qmap; above }
  | q, (QProp | QSProp | QType as qv) ->
    if qv == QSProp && QSet.mem q m.above then None
    else Some { qmap = QMap.add q (Some qv) m.qmap; above = QSet.remove q m.above }

let set_above_prop q m =
  let q = repr q m in
  let q = match q with QVar q -> q | QProp | QSProp | QType -> assert false in
  { qmap = m.qmap; above = QSet.add q m.above }

let unify_quality ~fail c q1 q2 local = match q1, q2 with
| QType, QType | QProp, QProp | QSProp, QSProp -> local
| QProp, QVar q when c == Conversion.CUMUL ->
  set_above_prop q local
| QVar q, (QType | QProp | QSProp | QVar _ as qv)
| (QType | QProp | QSProp as qv), QVar q ->
  begin match set q qv local with
  | Some local -> local
  | None -> fail ()
  end
| (QType, (QProp | QSProp)) -> fail ()
| (QProp, QType) ->
  begin match c with
  | CONV -> fail ()
  | CUMUL -> local
  end
| (QSProp, (QType | QProp)) -> fail ()
| (QProp, QSProp) -> fail ()

let nf_quality m = function
  | QSProp | QProp | QType as q -> q
  | QVar q -> repr q m

let union ~fail s1 s2 =
  let extra = ref [] in
  let qmap = QMap.union (fun qk q1 q2 ->
      match q1, q2 with
      | Some q, None | None, Some q -> Some (Some q)
      | None, None -> Some None
      | Some q1, Some q2 ->
        let () = if not (quality_eq q1 q2) then extra := (q1,q2) :: !extra in
        Some (Some q1))
      s1.qmap s2.qmap
  in
  let extra = !extra in
  let filter q = match QMap.find q qmap with
  | None -> true
  | Some _ -> false
  | exception Not_found -> false
  in
  let above = QSet.filter filter @@ QSet.union s1.above s2.above in
  let s = { qmap; above } in
  List.fold_left (fun s (q1,q2) ->
      let q1 = nf_quality s q1 and q2 = nf_quality s q2 in
      unify_quality ~fail:(fun () -> fail s q1 q2) CONV q1 q2 s)
    s
    extra

let add q m = { qmap = QMap.add q None m.qmap; above = m.above }

let collapse m =
  let map q v = match v with
  | None -> Some QType
  | Some _ -> v
  in
  { qmap = QMap.mapi map m.qmap; above = QSet.empty }

let pr { qmap; above } =
  let open Pp in
  let prbody u = function
  | None ->
    if QSet.mem u above then str " >= Prop"
    else mt ()
  | Some q ->
    let q = pr_quality q in
    str " := " ++ q
  in
  h (prlist_with_sep fnl (fun (u, v) -> Sorts.QVar.pr u ++ prbody u v) (QMap.bindings qmap))

end

module UPairSet = UnivMinim.UPairSet

type univ_names = UnivNames.universe_binders * uinfo Level.Map.t

(* 2nd part used to check consistency on the fly. *)
type t =
 { names : univ_names; (** Printing/location information *)
   local : ContextSet.t; (** The local graph of universes (variables and constraints) *)
   seff_univs : Level.Set.t; (** Local universes used through private constants *)
   univ_variables : UnivFlex.t;
   (** The local universes that are unification variables *)
   sort_variables : QState.t;
   (** Local quality variables. *)
   universes : UGraph.t; (** The current graph extended with the local constraints *)
   universes_lbound : UGraph.Bound.t; (** The lower bound on universes (e.g. Set or Prop) *)
   initial_universes : UGraph.t; (** The graph at the creation of the evar_map *)
   minim_extra : UnivMinim.extra;
 }

let empty =
  { names = UNameMap.empty, Level.Map.empty;
    local = ContextSet.empty;
    seff_univs = Level.Set.empty;
    univ_variables = UnivFlex.empty;
    sort_variables = QState.empty;
    universes = UGraph.initial_universes;
    universes_lbound = UGraph.Bound.Set;
    initial_universes = UGraph.initial_universes;
    minim_extra = UnivMinim.empty_extra; }

let make ~lbound univs =
  { empty with
    universes = univs;
    universes_lbound = lbound;
    initial_universes = univs }

let is_empty uctx =
  ContextSet.is_empty uctx.local &&
  UnivFlex.is_empty uctx.univ_variables

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
    let seff = Level.Set.union uctx.seff_univs uctx'.seff_univs in
    let names = uname_union (fst uctx.names) (fst uctx'.names) in
    let names_rev = Level.Map.lunion (snd uctx.names) (snd uctx'.names) in
    let newus = Level.Set.diff (ContextSet.levels uctx'.local)
                               (ContextSet.levels uctx.local) in
    let newus = Level.Set.diff newus (UnivFlex.domain uctx.univ_variables) in
    let extra = UnivMinim.extra_union uctx.minim_extra uctx'.minim_extra in
    let declarenew g =
      Level.Set.fold (fun u g -> UGraph.add_universe u ~lbound:uctx.universes_lbound ~strict:false g) newus g
    in
    let fail_union s q1 q2 =
      if UGraph.type_in_type uctx.universes then s
      else CErrors.user_err
          Pp.(str "Could not merge universe contexts: could not unify" ++ spc() ++
             pr_quality q1 ++ strbrk " and " ++ pr_quality q2 ++ str ".")
    in
      { names = (names, names_rev);
        local = local;
        seff_univs = seff;
        univ_variables =
          UnivFlex.biased_union uctx.univ_variables uctx'.univ_variables;
        sort_variables = QState.union ~fail:fail_union uctx.sort_variables uctx'.sort_variables;
        initial_universes = declarenew uctx.initial_universes;
        universes =
          (if local == uctx.local then uctx.universes
           else
             let cstrsr = ContextSet.constraints uctx'.local in
             UGraph.merge_constraints cstrsr (declarenew uctx.universes));
        universes_lbound = uctx.universes_lbound;
        minim_extra = extra}

let context_set uctx = uctx.local

let constraints uctx = snd uctx.local

let compute_instance_binders rbinders inst =
  let map lvl =
    try Name (Option.get (Level.Map.find lvl rbinders).uname)
    with Option.IsNone | Not_found -> Anonymous
  in
  Array.map map (Instance.to_array inst)

let context uctx =
  let (_, rbinders) = uctx.names in
  UContext.of_context_set (compute_instance_binders rbinders) uctx.local

type named_universes_entry = universes_entry * UnivNames.universe_binders

let univ_entry ~poly uctx =
  let (binders, _) = uctx.names in
  let entry =
    if poly then Polymorphic_entry (context uctx)
    else Monomorphic_entry (context_set uctx) in
  entry, binders

let of_context_set local = { empty with local }

type universe_opt_subst = UnivFlex.t

let subst uctx = uctx.univ_variables

let ugraph uctx = uctx.universes

let initial_graph uctx = uctx.initial_universes

let is_algebraic l uctx = UnivFlex.is_algebraic l uctx.univ_variables

let add_names ?loc s l (names, names_rev) =
  if UNameMap.mem s names
  then user_err ?loc
      Pp.(str "Universe " ++ Names.Id.print s ++ str" already bound.");
  (UNameMap.add s l names, Level.Map.add l { uname = Some s; uloc = loc } names_rev)

let add_loc l loc (names, names_rev) =
  match loc with
  | None -> (names, names_rev)
  | Some _ -> (names, Level.Map.add l { uname = None; uloc = loc } names_rev)

let of_names (ubind,revubind) =
  let revubind = Level.Map.map (fun id -> { uname = Some id; uloc = None }) revubind in
  {empty with names = (ubind,revubind)}

let universe_of_name uctx s =
  UNameMap.find s (fst uctx.names)

let name_level level id uctx =
  assert(not(Names.Id.Map.mem id (fst uctx.names)));
  { uctx with names = (Names.Id.Map.add id level (fst uctx.names), Univ.Level.Map.add level { uname = Some id; uloc = None } (snd uctx.names)) }


let universe_binders uctx =
  let named, _ = uctx.names in
  named

let nf_qvar uctx q = QState.repr q uctx.sort_variables

let instantiate_variable l (b : Universe.t) v =
  v := UnivFlex.define l b !v

exception UniversesDiffer

let { Goptions.get = drop_weak_constraints } =
  Goptions.declare_bool_option_and_ref
    ~key:["Cumulativity";"Weak";"Constraints"]
    ~value:false
    ()

let level_inconsistency cst l r =
  let mk u = Sorts.sort_of_univ @@ Universe.make u in
  raise (UGraph.UniverseInconsistency (cst, mk l, mk r, None))

let subst_univs_sort normalize qnormalize s = match s with
| Sorts.Set | Sorts.Prop | Sorts.SProp -> s
| Sorts.Type u -> Sorts.sort_of_univ (UnivSubst.subst_univs_universe normalize u)
| Sorts.QSort (q, u) ->
  match qnormalize q with
  | QSProp -> Sorts.sprop
  | QProp -> Sorts.prop
  | QType -> Sorts.sort_of_univ (UnivSubst.subst_univs_universe normalize u)
  | QVar q -> Sorts.qsort q (UnivSubst.subst_univs_universe normalize u)

let nf_sort uctx s =
  let normalize u = UnivFlex.normalize_univ_variable uctx.univ_variables u in
  let qnormalize q = QState.repr q uctx.sort_variables in
  subst_univs_sort normalize qnormalize s

let nf_relevance uctx r = match r with
| Sorts.Relevant | Sorts.Irrelevant -> r
| Sorts.RelevanceVar q ->
  match nf_qvar uctx q with
  | QSProp -> Sorts.Irrelevant
  | QProp | QType -> Sorts.Relevant
  | QVar q' ->
    if QState.is_above_prop q' uctx.sort_variables then Relevant
    else if Sorts.QVar.equal q q' then r
    else Sorts.RelevanceVar q'

let nf_universes uctx c =
  let lsubst = uctx.univ_variables in
  let level_value l =
    UnivSubst.level_subst_of (fun l -> UnivFlex.normalize_univ_variable lsubst l) l
  in
  let sort_value s = nf_sort uctx s in
  let rel_value r = nf_relevance uctx r in
  UnivSubst.nf_evars_and_universes_opt_subst (fun _ -> None) level_value sort_value rel_value c

type small_universe = USet | UProp | USProp

let is_uset = function USet -> true | UProp | USProp -> false

type sort_classification =
| USmall of small_universe (* Set, Prop or SProp *)
| ULevel of Level.t (* Var or Global *)
| UMax of Universe.t * Level.Set.t (* Max of Set, Var, Global without increments *)
| UAlgebraic of Universe.t (* Arbitrary algebraic expression *)

let classify s = match s with
| Sorts.Prop -> USmall UProp
| Sorts.SProp -> USmall USProp
| Sorts.Set -> USmall USet
| Sorts.Type u | Sorts.QSort (_, u) ->
  if Universe.is_levels u then match Universe.level u with
  | None -> UMax (u, Universe.levels u)
  | Some u -> ULevel u
  else UAlgebraic u

type local = {
  local_cst : Constraints.t;
  local_above_prop : Level.Set.t;
  local_weak : UPairSet.t;
  local_sorts : QState.t;
}

let add_local cst local =
  { local with local_cst = Constraints.add cst local.local_cst }

(* Constraint with algebraic on the left and a single level on the right *)
let enforce_leq_up u v local =
  { local with local_cst = UnivSubst.enforce_leq u (Universe.make v) local.local_cst }

let quality_of_sort = function
| Sorts.Set | Sorts.Type _ -> QType
| Sorts.Prop -> QProp
| Sorts.SProp -> QSProp
| Sorts.QSort (q, _) -> QVar q

let get_constraint = function
| Conversion.CONV -> Eq
| Conversion.CUMUL -> Le

let unify_quality univs c s1 s2 l =
  let fail () = if UGraph.type_in_type univs then l.local_sorts
    else sort_inconsistency (get_constraint c) s1 s2
  in
  { l with
    local_sorts  = QState.unify_quality ~fail
        c (quality_of_sort s1) (quality_of_sort s2) l.local_sorts;
  }

let process_universe_constraints uctx cstrs =
  let open UnivSubst in
  let open UnivProblem in
  let univs = uctx.universes in
  let vars = ref uctx.univ_variables in
  let normalize u = UnivFlex.normalize_univ_variable !vars u in
  let normalize_sort sorts s =
    let qnormalize q = QState.repr q sorts in
    subst_univs_sort normalize qnormalize s
  in
  let nf_constraint sorts = function
    | ULub (u, v) -> ULub (level_subst_of normalize u, level_subst_of normalize v)
    | UWeak (u, v) -> UWeak (level_subst_of normalize u, level_subst_of normalize v)
    | UEq (u, v) -> UEq (normalize_sort sorts u, normalize_sort sorts v)
    | ULe (u, v) -> ULe (normalize_sort sorts u, normalize_sort sorts v)
  in
  let is_local l = UnivFlex.mem l !vars in
  let equalize_small l s local =
    let ls = match l with
    | USProp -> Sorts.sprop
    | UProp -> Sorts.prop
    | USet -> Sorts.set
    in
    if UGraph.check_eq_sort univs ls s then local
    else if is_uset l then match classify s with
    | USmall _ -> sort_inconsistency Eq Sorts.set s
    | ULevel r ->
      if is_local r then
        let () = instantiate_variable r Universe.type0 vars in
        add_local (Level.set, Eq, r) local
      else
        sort_inconsistency Eq Sorts.set s
    | UMax (u, _)| UAlgebraic u ->
      if univ_level_mem Level.set u then
        let inst = univ_level_rem Level.set u u in
        enforce_leq_up inst Level.set local
      else
        sort_inconsistency Eq ls s
    else sort_inconsistency Eq ls s
  in
  let equalize_variables fo l' r' local =
    if Level.equal l' r' then local
    else
      let () =
        if is_local l' then
          instantiate_variable l' (Universe.make r') vars
        else if is_local r' then
          instantiate_variable r' (Universe.make l') vars
        else if not (UnivProblem.check_eq_level univs l' r') then
          (* Two rigid/global levels, none of them being local,
              one of them being Prop/Set, disallow *)
          if Level.is_set l' || Level.is_set r' then
            level_inconsistency Eq l' r'
          else if fo then
            raise UniversesDiffer
      in
      add_local (l', Eq, r') local
  in
  let equalize_algebraic l ru local =
    let alg = UnivFlex.is_algebraic l uctx.univ_variables in
    let inst = univ_level_rem l ru ru in
    if alg && not (Level.Set.mem l (Universe.levels inst)) then
      let () = instantiate_variable l inst vars in
      local
    else
      if univ_level_mem l ru then
        enforce_leq_up inst l local
      else sort_inconsistency Eq (Sorts.sort_of_univ (Universe.make l)) (Sorts.sort_of_univ ru)
  in
  let equalize_universes l r local = match classify l, classify r with
  | USmall l', (USmall _ | ULevel _ | UMax _ | UAlgebraic _) ->
    equalize_small l' r local
  | (ULevel _ | UMax _ | UAlgebraic _), USmall r' ->
    equalize_small r' l local
  | ULevel l', ULevel r' ->
    equalize_variables false l' r' local
  | ULevel l', (UAlgebraic r | UMax (r, _)) | (UAlgebraic r | UMax (r, _)), ULevel l' ->
    equalize_algebraic l' r local
  | (UAlgebraic _ | UMax _), (UAlgebraic _ | UMax _) ->
    (* both are algebraic *)
    if UGraph.check_eq_sort univs l r then local
    else sort_inconsistency Eq l r
  in
  let unify_universes cst local =
    let cst = nf_constraint local.local_sorts cst in
    if UnivProblem.is_trivial cst then local
    else match cst with
    | ULe (l, r) ->
      let local = unify_quality univs CUMUL l r local in
      let l = normalize_sort local.local_sorts l in
      let r = normalize_sort local.local_sorts r in
      begin match classify r with
      | UAlgebraic _ | UMax _ ->
        if UGraph.check_leq_sort univs l r then local
        else
          sort_inconsistency Le l r
            ~explain:(Pp.str "(cannot handle algebraic on the right)")
      | USmall r' ->
        (* Invariant: there are no universes u <= Set in the graph. Except for
           template levels, Set <= u anyways. Otherwise, for template
           levels, any constraint u <= Set is turned into u := Set. *)
        if UGraph.type_in_type univs then local
        else begin match classify l with
        | UAlgebraic _ ->
          (* l contains a +1 and r=r' small so l <= r impossible *)
          sort_inconsistency Le l r
        | USmall l' ->
          if UGraph.check_leq_sort univs l r then local
          else sort_inconsistency Le l r
        | ULevel l' ->
          if is_uset r' && is_local l' then
            (* Unbounded universe constrained from above, we equalize it *)
            let () = instantiate_variable l' Universe.type0 vars in
            add_local (l', Eq, Level.set) local
          else
            sort_inconsistency Le l r
        | UMax (_, levels) ->
          if is_uset r' then
            let fold l' local =
              let l = Sorts.sort_of_univ @@ Universe.make l' in
              if Level.is_set l' || is_local l' then
                equalize_variables false l' Level.set local
              else sort_inconsistency Le l r
            in
            Level.Set.fold fold levels local
          else
            sort_inconsistency Le l r
        end
      | ULevel r' ->
        (* We insert the constraint in the graph even if the graph
            already contains it.  Indeed, checking the existence of the
            constraint is costly when the constraint does not already
            exist directly as a single edge in the graph, but adding an
            edge in the graph which is implied by others is cheap.
            Hence, by doing this, we avoid a costly check here, and
            make further checks of this constraint easier since it will
            exist directly in the graph. *)
        match classify l with
        | USmall UProp ->
          { local with local_above_prop = Level.Set.add r' local.local_above_prop }
        | USmall USProp ->
          if UGraph.type_in_type univs then local
          else sort_inconsistency Le l r
        | USmall USet ->
          add_local (Level.set, Le, r') local
        | ULevel l' ->
          add_local (l', Le, r') local
        | UAlgebraic l ->
          enforce_leq_up l r' local
        | UMax (_, l) ->
          Univ.Level.Set.fold (fun l' accu -> add_local (l', Le, r') accu) l local
      end
    | ULub (l, r) ->
      equalize_variables true l r local
    | UWeak (l, r) ->
      if not (drop_weak_constraints ())
      then { local with local_weak = UPairSet.add (l, r) local.local_weak }
      else local
    | UEq (l, r) ->
      let local = unify_quality univs CONV l r local in
      let l = normalize_sort local.local_sorts l in
      let r = normalize_sort local.local_sorts r in
      equalize_universes l r local
  in
  let unify_universes cst local =
    if not (UGraph.type_in_type univs) then unify_universes cst local
    else try unify_universes cst local with UGraph.UniverseInconsistency _ -> local
  in
  let local = {
    local_cst = Constraints.empty;
    local_weak = uctx.minim_extra.UnivMinim.weak_constraints;
    local_above_prop = uctx.minim_extra.UnivMinim.above_prop;
    local_sorts = uctx.sort_variables;
  } in
  let local = UnivProblem.Set.fold unify_universes cstrs local in
  let extra = { UnivMinim.above_prop = local.local_above_prop; UnivMinim.weak_constraints = local.local_weak } in
  !vars, extra, local.local_cst, local.local_sorts

let add_constraints uctx cstrs =
  let univs, old_cstrs = uctx.local in
  let cstrs' = Constraints.fold (fun (l,d,r) acc ->
    let l = Universe.make l and r = Sorts.sort_of_univ @@ Universe.make r in
    let cstr' = let open UnivProblem in
      match d with
      | Lt ->
        ULe (Sorts.sort_of_univ @@ Universe.super l, r)
      | Le -> ULe (Sorts.sort_of_univ l, r)
      | Eq -> UEq (Sorts.sort_of_univ l, r)
    in UnivProblem.Set.add cstr' acc)
    cstrs UnivProblem.Set.empty
  in
  let vars, extra, cstrs', sorts = process_universe_constraints uctx cstrs' in
  { uctx with
    local = (univs, Constraints.union old_cstrs cstrs');
    univ_variables = vars;
    universes = UGraph.merge_constraints cstrs' uctx.universes;
    sort_variables = sorts;
    minim_extra = extra; }

let add_universe_constraints uctx cstrs =
  let univs, local = uctx.local in
  let vars, extra, local', sorts = process_universe_constraints uctx cstrs in
  { uctx with
    local = (univs, Constraints.union local local');
    univ_variables = vars;
    universes = UGraph.merge_constraints local' uctx.universes;
    sort_variables = sorts;
    minim_extra = extra; }

let constrain_variables diff uctx =
  let local, vars = UnivFlex.constrain_variables diff uctx.univ_variables uctx.local in
  { uctx with local; univ_variables = vars }

let id_of_level uctx l =
  try Some (Option.get (Level.Map.find l (snd uctx.names)).uname)
  with Not_found | Option.IsNone ->
    None

let qualid_of_level_names (map, map_rev) l =
  try Some (Libnames.qualid_of_ident (Option.get (Level.Map.find l map_rev).uname))
  with Not_found | Option.IsNone ->
    UnivNames.qualid_of_level map l

let qualid_of_level uctx l = qualid_of_level_names uctx.names l

let pr_uctx_level_names names l =
  match qualid_of_level_names names l with
  | Some qid -> Libnames.pr_qualid qid
  | None -> Level.raw_pr l

let pr_uctx_level uctx l = pr_uctx_level_names uctx.names l

type ('a, 'b) gen_universe_decl = {
  univdecl_instance : 'a; (* Declared universes *)
  univdecl_extensible_instance : bool; (* Can new universes be added *)
  univdecl_constraints : 'b; (* Declared constraints *)
  univdecl_extensible_constraints : bool (* Can new constraints be added *) }

type universe_decl =
  (Level.t list, Constraints.t) gen_universe_decl

let default_univ_decl =
  { univdecl_instance = [];
    univdecl_extensible_instance = true;
    univdecl_constraints = Constraints.empty;
    univdecl_extensible_constraints = true }

let pr_error_unbound_universes left names =
  let open Pp in
  let n = Level.Set.cardinal left in
  let prlev u =
    let info = Level.Map.find_opt u (snd names) in
    h (pr_uctx_level_names names u ++ (match info with
        | None | Some {uloc=None} -> mt ()
        | Some {uloc=Some loc} -> spc() ++ str"(" ++ Loc.pr loc ++ str")"))
  in
  (hv 0
     (str (CString.plural n "Universe") ++ spc () ++
      (prlist_with_sep spc prlev (Level.Set.elements left)) ++
      spc () ++ str (CString.conjugate_verb_to_be n) ++ str" unbound."))

exception UnboundUnivs of Level.Set.t * univ_names

(* Deliberately using no location as the location of the univs
   doesn't correspond to the failing command. *)
let error_unbound_universes left uctx = raise (UnboundUnivs (left,uctx))

let _ = CErrors.register_handler (function
    | UnboundUnivs (left,uctx) -> Some (pr_error_unbound_universes left uctx)
    | _ -> None)

let universe_context_inst ~prefix ~extensible levels names =
  let left = List.fold_left (fun acc l -> Level.Set.remove l acc) levels prefix in
  if not extensible && not (Level.Set.is_empty left)
  then error_unbound_universes left names
  else
    let left = UContext.sort_levels (Array.of_list (Level.Set.elements left)) in
    let inst = Array.append (Array.of_list prefix) left in
    let inst = Instance.of_array inst in
    inst

let check_universe_context_set ~prefix levels names =
  let left =
    List.fold_left (fun left l -> Level.Set.remove l left)
      levels prefix
  in
  if not (Level.Set.is_empty left)
  then error_unbound_universes left names

let check_implication uctx cstrs cstrs' =
  let gr = initial_graph uctx in
  let grext = UGraph.merge_constraints cstrs gr in
  let cstrs' = Constraints.filter (fun c -> not (UGraph.check_constraint grext c)) cstrs' in
  if Constraints.is_empty cstrs' then ()
  else CErrors.user_err
      Pp.(str "Universe constraints are not implied by the ones declared: " ++
          Constraints.pr (pr_uctx_level uctx) cstrs')

let check_mono_univ_decl uctx decl =
  let levels, csts = uctx.local in
  let () =
    let prefix = decl.univdecl_instance in
    if not decl.univdecl_extensible_instance
    then check_universe_context_set ~prefix levels uctx.names
  in
  if decl.univdecl_extensible_constraints then uctx.local
  else begin
    check_implication uctx
      decl.univdecl_constraints
      csts;
    levels, decl.univdecl_constraints
  end

let check_poly_univ_decl uctx decl =
  let prefix = decl.univdecl_instance in
  let extensible = decl.univdecl_extensible_instance in
  let levels, csts = uctx.local in
  let inst = universe_context_inst ~prefix ~extensible levels uctx.names in
  let nas = compute_instance_binders (snd uctx.names) inst in
  let csts = if decl.univdecl_extensible_constraints then csts
    else begin
      check_implication uctx
        decl.univdecl_constraints
        csts;
      decl.univdecl_constraints
    end
  in
  let uctx = UContext.make nas (inst, csts) in
  uctx

let check_univ_decl ~poly uctx decl =
  let entry =
    if not poly then
      let ctx = check_mono_univ_decl uctx decl in
      Monomorphic_entry ctx
    else
      let ctx = check_poly_univ_decl uctx decl in
      Polymorphic_entry ctx
  in
  entry, fst uctx.names

let is_bound l lbound = match lbound with
  | UGraph.Bound.Prop -> false
  | UGraph.Bound.Set -> Level.is_set l

let restrict_universe_context ~lbound (univs, csts) keep =
  let removed = Level.Set.diff univs keep in
  if Level.Set.is_empty removed then univs, csts
  else
  let allunivs = Constraints.fold (fun (u,_,v) all -> Level.Set.add u (Level.Set.add v all)) csts univs in
  let g = UGraph.initial_universes in
  let g = Level.Set.fold (fun v g -> if Level.is_set v then g else
                        UGraph.add_universe v ~lbound ~strict:false g) allunivs g in
  let g = UGraph.merge_constraints csts g in
  let allkept = Level.Set.union (UGraph.domain UGraph.initial_universes) (Level.Set.diff allunivs removed) in
  let csts = UGraph.constraints_for ~kept:allkept g in
  let csts = Constraints.filter (fun (l,d,r) -> not (is_bound l lbound && d == Le)) csts in
  (Level.Set.inter univs keep, csts)

let restrict uctx vars =
  let vars = Level.Set.union vars uctx.seff_univs in
  let vars = Names.Id.Map.fold (fun na l vars -> Level.Set.add l vars)
      (fst uctx.names) vars
  in
  let uctx' = restrict_universe_context ~lbound:uctx.universes_lbound uctx.local vars in
  { uctx with local = uctx' }

let restrict_even_binders uctx vars =
  let vars = Level.Set.union vars uctx.seff_univs in
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
  let local = ContextSet.append uctx' uctx.local in
  let declare g =
    Level.Set.fold (fun u g ->
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
      try Level.Map.modify u modify accu
      with Not_found -> Level.Map.add u { uname = None; uloc = loc } accu
    in
    (fst uctx.names, Level.Set.fold fold levels (snd uctx.names))
  in
  let initial = declare uctx.initial_universes in
  let univs = declare uctx.universes in
  let universes = UGraph.merge_constraints (ContextSet.constraints uctx') univs in
  let uctx =
    match rigid with
    | UnivRigid -> uctx
    | UnivFlexible b ->
      assert (not sideff);
      let uvars' = UnivFlex.add_levels levels ~algebraic:b uctx.univ_variables in
      { uctx with univ_variables = uvars' }
  in
  { uctx with names; local; universes;
              initial_universes = initial }

(* Check bug_4363 and bug_6323 when changing this code *)
let demote_seff_univs univs uctx =
  let seff = Level.Set.union uctx.seff_univs univs in
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
    Level.Set.fold (fun u g ->
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

let update_sigma_univs uctx univs =
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

let new_sort_variable uctx =
  let q = UnivGen.new_sort_global () in
  let sort_variables = QState.add q uctx.sort_variables in
  { uctx with sort_variables }, q

let new_univ_variable ?loc rigid name uctx =
  let u = UnivGen.fresh_level () in
  let uctx =
    match rigid with
    | UnivRigid -> uctx
    | UnivFlexible algebraic ->
      let univ_variables = UnivFlex.add u ~algebraic uctx.univ_variables in
      { uctx with univ_variables }
  in
  let uctx = add_universe ?loc name false uctx.universes_lbound uctx u in
  uctx, u

let add_global_univ uctx u = add_universe None true UGraph.Bound.Set uctx u

let make_with_initial_binders ~lbound univs binders =
  let uctx = make ~lbound univs in
  List.fold_left
    (fun uctx { CAst.loc; v = id } ->
       fst (new_univ_variable ?loc univ_rigid (Some id) uctx))
    uctx binders

let from_env ?(binders=[]) env =
  make_with_initial_binders ~lbound:(Environ.universes_lbound env) (Environ.universes env) binders

let make_nonalgebraic_variable uctx u =
  { uctx with univ_variables = UnivFlex.make_nonalgebraic_variable uctx.univ_variables u }

let make_flexible_nonalgebraic uctx =
  { uctx with univ_variables = UnivFlex.make_all_undefined_nonalgebraic uctx.univ_variables }

let subst_univs_context_with_def def usubst (uctx, cst) =
  (Level.Set.diff uctx def, UnivSubst.subst_univs_constraints usubst cst)

let normalize_variables uctx =
  let normalized_variables, def, subst =
    UnivFlex.normalize_univ_variables uctx.univ_variables
  in
  let uctx_local = subst_univs_context_with_def def subst uctx.local in
  let univs = UGraph.merge_constraints (snd uctx_local) uctx.initial_universes in
  { uctx with
    local = uctx_local;
    univ_variables = normalized_variables;
    universes = univs }

let fix_undefined_variables uctx =
  { uctx with univ_variables = UnivFlex.fix_undefined_variables uctx.univ_variables }

let collapse_sort_variables uctx =
  { uctx with sort_variables = QState.collapse uctx.sort_variables }

let minimize uctx =
  let open UnivMinim in
  let lbound = uctx.universes_lbound in
  let (vars', us') =
    normalize_context_set ~lbound uctx.universes uctx.local uctx.univ_variables
      uctx.minim_extra
  in
  if ContextSet.equal us' uctx.local then uctx
  else
    let universes = UGraph.merge_constraints (snd us') uctx.initial_universes in
      { names = uctx.names;
        local = us';
        seff_univs = uctx.seff_univs; (* not sure about this *)
        univ_variables = vars';
        sort_variables = uctx.sort_variables;
        universes = universes;
        universes_lbound = lbound;
        initial_universes = uctx.initial_universes;
        minim_extra = UnivMinim.empty_extra; (* weak constraints are consumed *) }

(* XXX print above_prop too *)
let pr_weak prl {minim_extra={UnivMinim.weak_constraints=weak}} =
  let open Pp in
  prlist_with_sep fnl (fun (u,v) -> prl u ++ str " ~ " ++ prl v) (UPairSet.elements weak)

let pr_sort_opt_subst uctx = QState.pr uctx.sort_variables

module Internal =
struct

let reboot env uctx =
  let uctx_global = from_env env in
  { uctx_global with univ_variables = uctx.univ_variables; sort_variables = uctx.sort_variables }

end
