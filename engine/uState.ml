(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
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
open Sorts
open UVars

module UnivFlex = UnivFlex

type universes_entry =
| Monomorphic_entry of Univ.ContextSet.t
| Polymorphic_entry of UVars.UContext.t

module UNameMap = Id.Map

type uinfo = {
  uname : Id.t option;
  uloc : Loc.t option;
}

open Quality

let sort_inconsistency ?explain cst l r =
  let explain = Option.map (fun p -> UGraph.Other p) explain in
  raise (UGraph.UniverseInconsistency (None, (cst, l, r, explain)))

module QState : sig
  type t
  type elt = QVar.t
  val empty : t
  val union : fail:(t -> Quality.t -> Quality.t -> t) -> t -> t -> t
  val add : check_fresh:bool -> rigid:bool -> elt -> t -> t
  val repr : elt -> t -> Quality.t
  val is_rigid : t -> QVar.t -> bool
  val unify_quality : fail:(unit -> t) -> Conversion.conv_pb -> Quality.t -> Quality.t -> t -> t
  val is_above_prop : elt -> t -> bool
  val undefined : t -> QVar.Set.t
  val collapse_above_prop : to_prop:bool -> t -> t
  val collapse : ?except:QVar.Set.t -> t -> t
  val pr : (QVar.t -> Libnames.qualid option) -> t -> Pp.t
  val of_set : QVar.Set.t -> t
end =
struct

module QSet = QVar.Set
module QMap = QVar.Map

type t = {
  rigid : QSet.t;
  (** Rigid variables, may not be set to another *)
  qmap : Quality.t option QMap.t;
  (* TODO: use a persistent union-find structure *)
  above : QSet.t;
  (** Set of quality variables known to be either in Prop or Type.
      If q ∈ above then it must map to None in qmap. *)
}

type elt = QVar.t

let empty = { rigid = QSet.empty; qmap = QMap.empty; above = QSet.empty }

let rec repr q m = match QMap.find q m.qmap with
| None -> QVar q
| Some (QVar q) -> repr q m
| Some (QConstant _ as q) -> q
| exception Not_found ->
(*   let () = assert !Flags.in_debugger in *) (* FIXME *)
  QVar q

let is_above_prop q m = QSet.mem q m.above

let is_rigid m q = QSet.mem q m.rigid

let set q qv m =
  let q = repr q m in
  let q = match q with QVar q -> q | QConstant _ -> assert false in
  let qv = match qv with QVar qv -> repr qv m | (QConstant _ as qv) -> qv in
  match q, qv with
  | q, QVar qv ->
    if QVar.equal q qv then Some m
    else
    if QSet.mem q m.rigid then None
    else
      let above =
        if QSet.mem q m.above then QSet.add qv (QSet.remove q m.above)
        else m.above
      in
      Some { rigid = m.rigid; qmap = QMap.add q (Some (QVar qv)) m.qmap; above }
  | q, (QConstant qc as qv) ->
    if qc == QSProp && QSet.mem q m.above then None
    else if QSet.mem q m.rigid then None
    else
      Some { rigid = m.rigid; qmap = QMap.add q (Some qv) m.qmap; above = QSet.remove q m.above }

let set_above_prop q m =
  let q = repr q m in
  let q = match q with QVar q -> q | QConstant _ -> assert false in
  if QSet.mem q m.rigid then None
  else Some { rigid = m.rigid; qmap = m.qmap; above = QSet.add q m.above }

let unify_quality ~fail c q1 q2 local = match q1, q2 with
| QConstant QType, QConstant QType
| QConstant QProp, QConstant QProp
| QConstant QSProp, QConstant QSProp -> local
| QConstant QProp, QVar q when c == Conversion.CUMUL ->
  begin match set_above_prop q local with
  | Some local -> local
  | None -> fail ()
  end
| QVar qv1, QVar qv2 -> begin match set qv1 q2 local with
    | Some local -> local
    | None -> match set qv2 q1 local with
      | Some local -> local
      | None -> fail ()
  end
| QVar q, (QConstant (QType | QProp | QSProp) as qv)
| (QConstant (QType | QProp | QSProp) as qv), QVar q ->
  begin match set q qv local with
  | Some local -> local
  | None -> fail ()
  end
| (QConstant QType, QConstant (QProp | QSProp)) -> fail ()
| (QConstant QProp, QConstant QType) ->
  begin match c with
  | CONV -> fail ()
  | CUMUL -> local
  end
| (QConstant QSProp, QConstant (QType | QProp)) -> fail ()
| (QConstant QProp, QConstant QSProp) -> fail ()

let nf_quality m = function
  | QConstant _ as q -> q
  | QVar q -> repr q m

let union ~fail s1 s2 =
  let extra = ref [] in
  let qmap = QMap.union (fun qk q1 q2 ->
      match q1, q2 with
      | Some q, None | None, Some q -> Some (Some q)
      | None, None -> Some None
      | Some q1, Some q2 ->
        let () = if not (Quality.equal q1 q2) then extra := (q1,q2) :: !extra in
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
  let s = { rigid = QSet.union s1.rigid s2.rigid; qmap; above } in
  List.fold_left (fun s (q1,q2) ->
      let q1 = nf_quality s q1 and q2 = nf_quality s q2 in
      unify_quality ~fail:(fun () -> fail s q1 q2) CONV q1 q2 s)
    s
    extra

let add ~check_fresh ~rigid q m =
  if check_fresh then assert (not (QMap.mem q m.qmap));
  { rigid = if rigid then QSet.add q m.rigid else m.rigid;
    qmap = QMap.add q None m.qmap;
    above = m.above }

let of_set qs =
  { rigid = QSet.empty; qmap = QMap.bind (fun _ -> None) qs; above = QSet.empty }

(* XXX what about [above]? *)
let undefined m =
  let m = QMap.filter (fun _ v -> Option.is_empty v) m.qmap in
  QMap.domain m

let collapse_above_prop ~to_prop m =
  let map q v = match v with
    | None ->
      if not @@ QSet.mem q m.above then None else
      if to_prop then Some (QConstant QProp)
      else Some (QConstant QType)
  | Some _ -> v
  in
  { rigid = m.rigid; qmap = QMap.mapi map m.qmap; above = QSet.empty }

let collapse ?(except=QSet.empty) m =
  let map q v = match v with
  | None -> if QSet.mem q m.rigid || QSet.mem q except then None else Some (QConstant QType)
  | Some _ -> v
  in
  { rigid = m.rigid; qmap = QMap.mapi map m.qmap; above = QSet.empty }

let pr prqvar_opt { qmap; above; rigid } =
  let open Pp in
  let prqvar q = match prqvar_opt q with
    | None -> QVar.raw_pr q
    | Some qid -> Libnames.pr_qualid qid
  in
  let prbody u = function
  | None ->
    if QSet.mem u above then str " >= Prop"
    else if QSet.mem u rigid then
      str " (rigid)"
    else mt ()
  | Some q ->
    let q = Quality.pr prqvar q in
    str " := " ++ q
  in
  let prqvar_name q =
    match prqvar_opt q with
    | None -> mt()
    | Some qid -> str " (named " ++ Libnames.pr_qualid qid ++ str ")"
  in
  h (prlist_with_sep fnl (fun (u, v) -> QVar.raw_pr u ++ prbody u v ++ prqvar_name u) (QMap.bindings qmap))

end

module UPairSet = UnivMinim.UPairSet

type univ_names = UnivNames.universe_binders * (uinfo QVar.Map.t * uinfo Level.Map.t)

(* 2nd part used to check consistency on the fly. *)
type t =
 { names : univ_names; (** Printing/location information *)
   local : ContextSet.t; (** The local graph of universes (variables and constraints) *)
   univ_variables : UnivFlex.t;
   (** The local universes that are unification variables *)
   sort_variables : QState.t;
   (** Local quality variables. *)
   universes : UGraph.t; (** The current graph extended with the local constraints *)
   initial_universes : UGraph.t; (** The graph at the creation of the evar_map + local universes
                                     (but not local constraints) *)
   minim_extra : UnivMinim.extra;
 }

let empty =
  { names = UnivNames.empty_binders, (QVar.Map.empty, Level.Map.empty);
    local = ContextSet.empty;
    univ_variables = UnivFlex.empty;
    sort_variables = QState.empty;
    universes = UGraph.initial_universes;
    initial_universes = UGraph.initial_universes;
    minim_extra = UnivMinim.empty_extra; }

let make univs =
  { empty with
    universes = univs;
    initial_universes = univs }

let is_empty uctx =
  ContextSet.is_empty uctx.local &&
  UnivFlex.is_empty uctx.univ_variables

let id_of_level uctx l =
  try (Level.Map.find l (snd (snd uctx.names))).uname
  with Not_found -> None

let id_of_qvar uctx l =
  try (QVar.Map.find l (fst (snd uctx.names))).uname
  with Not_found -> None

let is_rigid_qvar uctx q = QState.is_rigid uctx.sort_variables q

let qualid_of_qvar_names (bind, (qrev,_)) l =
  try Some (Libnames.qualid_of_ident (Option.get (QVar.Map.find l qrev).uname))
  with Not_found | Option.IsNone ->
    None (* no global qvars *)

let qualid_of_level_names (bind, (_,urev)) l =
  try Some (Libnames.qualid_of_ident (Option.get (Level.Map.find l urev).uname))
  with Not_found | Option.IsNone ->
    UnivNames.qualid_of_level bind l

let qualid_of_level uctx l = qualid_of_level_names uctx.names l

let pr_uctx_qvar_names names l =
  match qualid_of_qvar_names names l with
  | Some qid -> Libnames.pr_qualid qid
  | None -> QVar.raw_pr l

let pr_uctx_level_names names l =
  match qualid_of_level_names names l with
  | Some qid -> Libnames.pr_qualid qid
  | None -> Level.raw_pr l

let pr_uctx_level uctx l = pr_uctx_level_names uctx.names l

let pr_uctx_qvar uctx l = pr_uctx_qvar_names uctx.names l

let merge_constraints uctx cstrs g =
  try UGraph.merge_constraints cstrs g
  with UGraph.UniverseInconsistency (_, i) ->
    let printers = (pr_uctx_qvar uctx, pr_uctx_level uctx) in
    raise (UGraph.UniverseInconsistency (Some printers, i))

let uname_union s t =
  if s == t then s
  else
    UNameMap.merge (fun k l r ->
        match l, r with
        | Some _, _ -> l
        | _, _ -> r) s t

let names_union ((qbind,ubind),(qrev,urev)) ((qbind',ubind'),(qrev',urev')) =
  let qbind = uname_union qbind qbind'
  and ubind = uname_union ubind ubind'
  and qrev = QVar.Map.union (fun _ l _ -> Some l) qrev qrev'
  and urev = Level.Map.lunion urev urev' in
  ((qbind,ubind),(qrev,urev))

let union uctx uctx' =
  if uctx == uctx' then uctx
  else if is_empty uctx' then uctx
  else
    let local = ContextSet.union uctx.local uctx'.local in
    let names = names_union uctx.names uctx'.names in
    let newus = Level.Set.diff (ContextSet.levels uctx'.local)
                               (ContextSet.levels uctx.local) in
    let newus = Level.Set.diff newus (UnivFlex.domain uctx.univ_variables) in
    let extra = UnivMinim.extra_union uctx.minim_extra uctx'.minim_extra in
    let declarenew g =
      Level.Set.fold (fun u g -> UGraph.add_universe u ~strict:false g) newus g
    in
    let fail_union s q1 q2 =
      if UGraph.type_in_type uctx.universes then s
      else CErrors.user_err
          Pp.(str "Could not merge universe contexts: could not unify" ++ spc() ++
             Quality.raw_pr q1 ++ strbrk " and " ++ Quality.raw_pr q2 ++ str ".")
    in
      { names;
        local = local;
        univ_variables =
          UnivFlex.biased_union uctx.univ_variables uctx'.univ_variables;
        sort_variables = QState.union ~fail:fail_union uctx.sort_variables uctx'.sort_variables;
        initial_universes = declarenew uctx.initial_universes;
        universes =
          (if local == uctx.local then uctx.universes
           else
             let cstrsr = ContextSet.constraints uctx'.local in
             merge_constraints uctx cstrsr (declarenew uctx.universes));
        minim_extra = extra}

let context_set uctx = uctx.local

let sort_context_set uctx =
  let us, csts = uctx.local in
  (QState.undefined uctx.sort_variables, us), csts

let constraints uctx = snd uctx.local

let compute_instance_binders uctx inst =
  let (qrev,urev) = snd uctx.names in
  let qinst, uinst = Instance.to_array inst in
  let qmap = function
    | QVar q ->
      begin try Name (Option.get (QVar.Map.find q qrev).uname)
      with Option.IsNone | Not_found -> Anonymous
      end
    | QConstant _ -> assert false
  in
  let umap lvl =
    try Name (Option.get (Level.Map.find lvl urev).uname)
    with Option.IsNone | Not_found -> Anonymous
  in
  Array.map qmap qinst, Array.map umap uinst

let context uctx =
  let qvars = QState.undefined uctx.sort_variables in
  UContext.of_context_set (compute_instance_binders uctx) qvars uctx.local

type named_universes_entry = universes_entry * UnivNames.universe_binders

let univ_entry ~poly uctx =
  let (binders, _) = uctx.names in
  let entry =
    if poly then Polymorphic_entry (context uctx)
    else Monomorphic_entry (context_set uctx) in
  entry, binders

let of_context_set ((qs,us),csts) =
  let sort_variables = QState.of_set qs in
  { empty with
    local = (us,csts);
    sort_variables;}

type universe_opt_subst = UnivFlex.t

let subst uctx = uctx.univ_variables

let ugraph uctx = uctx.universes

let is_algebraic l uctx = UnivFlex.is_algebraic l uctx.univ_variables

let of_names (ubind,(revqbind,revubind)) =
  let revqbind = QVar.Map.map (fun id -> { uname = Some id; uloc = None }) revqbind in
  let revubind = Level.Map.map (fun id -> { uname = Some id; uloc = None }) revubind in
  {empty with names = (ubind,(revqbind,revubind))}

let universe_of_name uctx s =
  UNameMap.find s (snd (fst uctx.names))

let quality_of_name uctx s =
  Id.Map.find s (fst (fst uctx.names))

let name_level level id uctx =
  let ((qbind,ubind),(qrev,urev)) = uctx.names in
  assert(not(Id.Map.mem id ubind));
  let ubind = Id.Map.add id level ubind in
  let urev = Level.Map.add level { uname = Some id; uloc = None } urev in
  { uctx with names = ((qbind,ubind),(qrev,urev)) }


let universe_binders uctx =
  let named, _ = uctx.names in
  named

let nf_qvar uctx q = QState.repr q uctx.sort_variables

let instantiate_variable l (b : Universe.t) v =
  v := UnivFlex.define l b !v

exception UniversesDiffer

let { Goptions.get = weak_constraints } =
  Goptions.declare_bool_option_and_ref
    ~key:["Cumulativity";"Weak";"Constraints"]
    ~value:true
    ()

let level_inconsistency cst l r =
  let mk u = Sorts.sort_of_univ @@ Universe.make u in
  raise (UGraph.UniverseInconsistency (None, (cst, mk l, mk r, None)))

let nf_universe uctx u =
  UnivSubst.(subst_univs_universe (UnivFlex.normalize_univ_variable uctx.univ_variables)) u

let nf_level uctx u =
  UnivSubst.(level_subst_of (UnivFlex.normalize_univ_variable uctx.univ_variables)) u

let nf_instance uctx u = Instance.subst_fn (nf_qvar uctx, nf_level uctx) u

let nf_quality uctx q = Quality.subst (nf_qvar uctx) q

let nf_sort uctx s =
  let normalize u = nf_universe uctx u in
  let qnormalize q = QState.repr q uctx.sort_variables in
  Sorts.subst_fn (qnormalize, normalize) s

let nf_relevance uctx r = match r with
| Relevant | Irrelevant -> r
| RelevanceVar q ->
  match nf_qvar uctx q with
  | QConstant QSProp -> Sorts.Irrelevant
  | QConstant QProp | QConstant QType -> Sorts.Relevant
  | QVar q' ->
    (* XXX currently not used in nf_evars_and_universes_opt_subst
       does it matter? *)
    if QState.is_above_prop q' uctx.sort_variables then Relevant
    else if QVar.equal q q' then r
    else Sorts.RelevanceVar q'

let nf_universes uctx c =
  let lsubst = uctx.univ_variables in
  let nf_univ u = UnivFlex.normalize_univ_variable lsubst u in
  let rec self () c = match Constr.kind c with
  | Evar (evk, args) ->
    let args' = SList.Smart.map (self ()) args in
    if args == args' then c else Constr.mkEvar (evk, args')
  | _ -> UnivSubst.map_universes_opt_subst_with_binders ignore self (nf_relevance uctx) (nf_qvar uctx) nf_univ () c
  in
  self ()  c

type small_universe = USet | UProp | USProp

let is_uset = function USet -> true | UProp | USProp -> false

type sort_classification =
| USmall of small_universe (* Set, Prop or SProp *)
| ULevel of Level.t (* Var or Global *)
| UMax of Universe.t * Level.Set.t (* Max of Set, Var, Global without increments *)
| UAlgebraic of Universe.t (* Arbitrary algebraic expression *)

let classify s = match s with
| Prop -> USmall UProp
| SProp -> USmall USProp
| Set -> USmall USet
| Type u | QSort (_, u) ->
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

let get_constraint = function
| Conversion.CONV -> Eq
| Conversion.CUMUL -> Le

let unify_quality univs c s1 s2 l =
  let fail () = if UGraph.type_in_type univs then l.local_sorts
    else sort_inconsistency (get_constraint c) s1 s2
  in
  { l with
    local_sorts  = QState.unify_quality ~fail
        c (Sorts.quality s1) (Sorts.quality s2) l.local_sorts;
  }

let process_universe_constraints uctx cstrs =
  let open UnivSubst in
  let open UnivProblem in
  let univs = uctx.universes in
  let vars = ref uctx.univ_variables in
  let normalize u = UnivFlex.normalize_univ_variable !vars u in
  let qnormalize sorts q = QState.repr q sorts in
  let normalize_sort sorts s =
    Sorts.subst_fn ((qnormalize sorts), subst_univs_universe normalize) s
  in
  let nf_constraint sorts = function
    | QLeq (a, b) -> QLeq (Quality.subst (qnormalize sorts) a, Quality.subst (qnormalize sorts) b)
    | QEq (a, b) -> QEq (Quality.subst (qnormalize sorts) a, Quality.subst (qnormalize sorts) b)
    | ULub (u, v) -> ULub (level_subst_of normalize u, level_subst_of normalize v)
    | UWeak (u, v) -> UWeak (level_subst_of normalize u, level_subst_of normalize v)
    | UEq (u, v) -> UEq (normalize_sort sorts u, normalize_sort sorts v)
    | ULe (u, v) -> ULe (normalize_sort sorts u, normalize_sort sorts v)
  in
  let is_local l = UnivFlex.mem l !vars in
  let equalize_small l s local =
    let ls = match l with
    | USProp -> sprop
    | UProp -> prop
    | USet -> set
    in
    if UGraph.check_eq_sort univs ls s then local
    else if is_uset l then match classify s with
    | USmall _ -> sort_inconsistency Eq set s
    | ULevel r ->
      if is_local r then
        let () = instantiate_variable r Universe.type0 vars in
        add_local (Level.set, Eq, r) local
      else
        sort_inconsistency Eq set s
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
      else sort_inconsistency Eq (sort_of_univ (Universe.make l)) (sort_of_univ ru)
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
    | QEq (a, b) ->
      (* TODO sort_inconsistency should be able to handle raw
         qualities instead of having to make a dummy sort *)
      let mk q = Sorts.make q Universe.type0 in
      unify_quality univs CONV (mk a) (mk b) local
    | QLeq (a, b) ->
      (* TODO sort_inconsistency should be able to handle raw
         qualities instead of having to make a dummy sort *)
      let mk q = Sorts.make q Universe.type0 in
      unify_quality univs CUMUL (mk a) (mk b) local
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
              let l = sort_of_univ @@ Universe.make l' in
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
      if weak_constraints ()
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

let add_universe_constraints uctx cstrs =
  let univs, local = uctx.local in
  let vars, extra, local', sorts = process_universe_constraints uctx cstrs in
  { uctx with
    local = (univs, Constraints.union local local');
    univ_variables = vars;
    universes = merge_constraints uctx local' uctx.universes;
    sort_variables = sorts;
    minim_extra = extra; }

let problem_of_constraints cstrs =
  Constraints.fold (fun (l,d,r) acc ->
      let l = Universe.make l and r = sort_of_univ @@ Universe.make r in
      let cstr' = let open UnivProblem in
        match d with
        | Lt ->
          ULe (sort_of_univ @@ Universe.super l, r)
        | Le -> ULe (sort_of_univ l, r)
        | Eq -> UEq (sort_of_univ l, r)
      in UnivProblem.Set.add cstr' acc)
    cstrs UnivProblem.Set.empty

let add_constraints uctx cstrs =
  let cstrs = problem_of_constraints cstrs in
  add_universe_constraints uctx cstrs

let add_quconstraints uctx (qcstrs,ucstrs) =
  let cstrs = problem_of_constraints ucstrs in
  let cstrs = QConstraints.fold (fun (l,d,r) cstrs ->
      match d with
      | Equal -> UnivProblem.Set.add (QEq (l,r)) cstrs
      | Leq -> UnivProblem.Set.add (QLeq (l,r)) cstrs)
      qcstrs cstrs
  in
  add_universe_constraints uctx cstrs

let check_qconstraints uctx csts =
  Sorts.QConstraints.for_all (fun (l,k,r) ->
      let l = nf_quality uctx l in
      let r = nf_quality uctx r in
      if Quality.equal l r then true
      else match l,k,r with
        | _, Equal, _ -> false
        | QConstant QProp, Leq, QConstant QType -> true
        | QConstant QProp, Leq, QVar q -> QState.is_above_prop q uctx.sort_variables
        | _, Leq, _ -> false)
    csts

let check_universe_constraint uctx (c:UnivProblem.t) =
  match c with
  | QEq (a,b) ->
    let a = nf_quality uctx a in
    let b = nf_quality uctx b in
    Quality.equal a b
  | QLeq (a,b) ->
    let a = nf_quality uctx a in
    let b = nf_quality uctx b in
    if Quality.equal a b then true
    else begin match a, b with
      | QConstant QProp, QConstant QType -> true
      | QConstant QProp, QVar q -> QState.is_above_prop q uctx.sort_variables
      | _ -> false
    end
  | ULe (u,v) -> UGraph.check_leq_sort uctx.universes u v
  | UEq (u,v) -> UGraph.check_eq_sort uctx.universes u v
  | ULub (u,v) -> UGraph.check_eq_level uctx.universes u v
  | UWeak _ -> true

let check_universe_constraints uctx csts =
  UnivProblem.Set.for_all (check_universe_constraint uctx) csts

let constrain_variables diff uctx =
  let local, vars = UnivFlex.constrain_variables diff uctx.univ_variables uctx.local in
  { uctx with local; univ_variables = vars }

type ('a, 'b, 'c) gen_universe_decl = {
  univdecl_qualities : 'a;
  univdecl_extensible_qualities : bool;
  univdecl_instance : 'b; (* Declared universes *)
  univdecl_extensible_instance : bool; (* Can new universes be added *)
  univdecl_constraints : 'c; (* Declared constraints *)
  univdecl_extensible_constraints : bool (* Can new constraints be added *) }

type universe_decl =
  (QVar.t list, Level.t list, Constraints.t) gen_universe_decl

let default_univ_decl =
  { univdecl_qualities = [];
    (* in practice non named qualities will get collapsed for toplevel definitions,
       but side effects see named qualities from the surrounding definitions
       while using default_univ_decl *)
    univdecl_extensible_qualities = true;
    univdecl_instance = [];
    univdecl_extensible_instance = true;
    univdecl_constraints = Constraints.empty;
    univdecl_extensible_constraints = true }

let pr_error_unbound_universes quals univs names =
  let open Pp in
  let nqs = QVar.Set.cardinal quals in
  let prqvar q =
    let info = QVar.Map.find_opt q (fst (snd names)) in
    h (pr_uctx_qvar_names names q ++ (match info with
        | None | Some {uloc=None} -> mt ()
        | Some {uloc=Some loc} -> spc() ++ str"(" ++ Loc.pr loc ++ str")"))
  in
  let nus = Level.Set.cardinal univs in
  let prlev u =
    let info = Level.Map.find_opt u (snd (snd names)) in
    h (pr_uctx_level_names names u ++ (match info with
        | None | Some {uloc=None} -> mt ()
        | Some {uloc=Some loc} -> spc() ++ str"(" ++ Loc.pr loc ++ str")"))
  in
  let ppqs = if nqs > 0 then
      str (if nqs = 1 then "Quality" else "Qualities") ++ spc () ++
      prlist_with_sep spc prqvar (QVar.Set.elements quals)
    else mt()
  in
  let ppus = if nus > 0 then
      let universe_s = CString.plural nus "universe" in
      let universe_s = if nqs = 0 then CString.capitalize_ascii universe_s else universe_s in
      str universe_s ++ spc () ++
      prlist_with_sep spc prlev (Level.Set.elements univs)
    else mt()
  in
  (hv 0
     (ppqs ++
      (if nqs > 0 && nus > 0 then strbrk " and " else mt()) ++
      ppus ++
      spc () ++ str (CString.conjugate_verb_to_be (nus + nqs)) ++ str" unbound."))

exception UnboundUnivs of QVar.Set.t * Level.Set.t * univ_names

(* XXX when we have multi location errors we won't have to pick an arbitrary error *)
let error_unbound_universes qs us uctx =
  let exception Found of Loc.t in
  let loc =
    try
      Level.Set.iter (fun u ->
          match Level.Map.find_opt u (snd (snd uctx)) with
          | None -> ()
          | Some info -> match info.uloc with
            | None -> ()
            | Some loc -> raise_notrace (Found loc))
        us;
      QVar.Set.iter (fun s ->
          match QVar.Map.find_opt s (fst (snd uctx)) with
          | None -> ()
          | Some info -> match info.uloc with
            | None -> ()
            | Some loc -> raise_notrace (Found loc))
        qs;
      None
    with Found loc -> Some loc
  in
  Loc.raise ?loc (UnboundUnivs (qs,us,uctx))

let () = CErrors.register_handler (function
    | UnboundUnivs (qs,us,uctx) -> Some (pr_error_unbound_universes qs us uctx)
    | _ -> None)

let universe_context_inst decl qvars levels names =
  let leftqs = List.fold_left (fun acc l -> QVar.Set.remove l acc) qvars decl.univdecl_qualities in
  let leftus = List.fold_left (fun acc l -> Level.Set.remove l acc) levels decl.univdecl_instance in
  let () =
    let unboundqs = if decl.univdecl_extensible_qualities then QVar.Set.empty else leftqs in
    let unboundus = if decl.univdecl_extensible_instance then Level.Set.empty else leftus in
    if not (QVar.Set.is_empty unboundqs && Level.Set.is_empty unboundus)
    then error_unbound_universes unboundqs unboundus names
  in
  let leftqs = UContext.sort_qualities
      (Array.map_of_list (fun q -> Quality.QVar q) (QVar.Set.elements leftqs))
  in
  let leftus = UContext.sort_levels (Array.of_list (Level.Set.elements leftus)) in
  let instq = Array.append
      (Array.map_of_list (fun q -> Quality.QVar q) decl.univdecl_qualities)
      leftqs
  in
  let instu = Array.append (Array.of_list decl.univdecl_instance) leftus in
  let inst = Instance.of_array (instq,instu) in
  inst

let check_universe_context_set ~prefix levels names =
  let left =
    List.fold_left (fun left l -> Level.Set.remove l left)
      levels prefix
  in
  if not (Level.Set.is_empty left)
  then error_unbound_universes QVar.Set.empty left names

let check_implication uctx cstrs cstrs' =
  let gr = uctx.initial_universes in
  let grext = merge_constraints uctx cstrs gr in
  let cstrs' = Constraints.filter (fun c -> not (UGraph.check_constraint grext c)) cstrs' in
  if Constraints.is_empty cstrs' then ()
  else CErrors.user_err
      Pp.(str "Universe constraints are not implied by the ones declared: " ++
          Constraints.pr (pr_uctx_level uctx) cstrs')

let check_template_univ_decl uctx ~template_qvars decl =
  let () =
    match List.filter (fun q -> not @@ QVar.Set.mem q template_qvars) decl.univdecl_qualities with
    | (_ :: _) as qvars ->
      CErrors.user_err
        Pp.(str "Qualities " ++ prlist_with_sep spc (pr_uctx_qvar uctx) qvars ++
            str " cannot be template.")
    | [] ->
      if not (QVar.Set.equal template_qvars (QState.undefined uctx.sort_variables))
      then CErrors.anomaly Pp.(str "Bugged template univ declaration.")
  in
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

let check_mono_univ_decl uctx decl =
  (* Note: if [decl] is [default_univ_decl], behave like [uctx.local] *)
  let () =
    if not (List.is_empty decl.univdecl_qualities)
    || not (QVar.Set.is_empty (QState.undefined uctx.sort_variables))
    then CErrors.user_err Pp.(str "Monomorphic declarations may not have sort variables.")
  in
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
  (* Note: if [decl] is [default_univ_decl], behave like [context uctx] *)
  let levels, csts = uctx.local in
  let qvars = QState.undefined uctx.sort_variables in
  let inst = universe_context_inst decl qvars levels uctx.names in
  let nas = compute_instance_binders uctx inst in
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
  let (binders, _) = uctx.names in
  let entry =
    if poly then Polymorphic_entry (check_poly_univ_decl uctx decl)
    else Monomorphic_entry (check_mono_univ_decl uctx decl) in
  entry, binders

let restrict_universe_context (univs, csts) keep =
  let removed = Level.Set.diff univs keep in
  if Level.Set.is_empty removed then univs, csts
  else
  let allunivs = Constraints.fold (fun (u,_,v) all -> Level.Set.add u (Level.Set.add v all)) csts univs in
  let g = UGraph.initial_universes in
  let g = Level.Set.fold (fun v g ->
      if Level.is_set v then g else
        UGraph.add_universe v ~strict:false g) allunivs g in
  let g = UGraph.merge_constraints csts g in
  let allkept = Level.Set.union (UGraph.domain UGraph.initial_universes) (Level.Set.diff allunivs removed) in
  let csts = UGraph.constraints_for ~kept:allkept g in
  let csts = Constraints.filter (fun (l,d,r) -> not (Level.is_set l && d == Le)) csts in
  (Level.Set.inter univs keep, csts)

let restrict uctx vars =
  let vars = Id.Map.fold (fun na l vars -> Level.Set.add l vars)
      (snd (fst uctx.names)) vars
  in
  let uctx' = restrict_universe_context uctx.local vars in
  { uctx with local = uctx' }

let restrict_even_binders uctx vars =
  let uctx' = restrict_universe_context uctx.local vars in
  { uctx with local = uctx' }

let restrict_constraints uctx csts =
  let levels, _ = uctx.local in
  let uctx' = { uctx with local = ContextSet.of_set levels; universes = uctx.initial_universes } in
  add_constraints uctx' csts

type rigid =
  | UnivRigid
  | UnivFlexible of bool (** Is substitution by an algebraic ok? *)

let univ_rigid = UnivRigid
let univ_flexible = UnivFlexible false
let univ_flexible_alg = UnivFlexible true

(** ~sideff indicates that it is ok to redeclare a universe.
    Also merges the universe context in the local constraint structures
    and not only in the graph. *)
let merge ?loc ~sideff rigid uctx uctx' =
  let levels = ContextSet.levels uctx' in
  let local = ContextSet.append uctx' uctx.local in
  let declare g =
    Level.Set.fold (fun u g ->
        try UGraph.add_universe ~strict:false u g
        with UGraph.AlreadyDeclared when sideff -> g)
      levels g
  in
  let names =
    let fold u accu =
      let update = function
        | None -> Some { uname = None; uloc = loc }
        | Some info -> match info.uloc with
          | None -> Some { info with uloc = loc }
          | Some _ -> Some info
      in
      Level.Map.update u update accu
    in
    (fst uctx.names, (fst (snd uctx.names), Level.Set.fold fold levels (snd (snd uctx.names))))
  in
  let initial = declare uctx.initial_universes in
  let univs = declare uctx.universes in
  let universes = merge_constraints uctx (ContextSet.constraints uctx') univs in
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

let merge_sort_variables ?loc ~sideff uctx qvars =
  let sort_variables =
    QVar.Set.fold (fun qv qstate -> QState.add ~check_fresh:(not sideff) ~rigid:false qv qstate)
      qvars
      uctx.sort_variables
  in
  let names =
    let fold u accu =
      let update = function
        | None -> Some { uname = None; uloc = loc }
        | Some info -> match info.uloc with
          | None -> Some { info with uloc = loc }
          | Some _ -> Some info
      in
      QVar.Map.update u update accu
    in
    let qrev = QVar.Set.fold fold qvars (fst (snd uctx.names)) in
    (fst uctx.names, (qrev, snd (snd uctx.names)))
  in
  { uctx with sort_variables; names }

let merge_sort_context ?loc ~sideff rigid uctx ((qvars,levels),csts) =
  let uctx = merge_sort_variables ?loc ~sideff uctx qvars in
  merge ?loc ~sideff rigid uctx (levels,csts)

let demote_global_univs (lvl_set,csts_set) uctx =
  let (local_univs, local_constraints) = uctx.local in
  let local_univs = Level.Set.diff local_univs lvl_set in
  let univ_variables = Level.Set.fold UnivFlex.remove lvl_set uctx.univ_variables in
  let update_ugraph g =
    let g = Level.Set.fold (fun u g ->
        try UGraph.add_universe u ~strict:true g
        with UGraph.AlreadyDeclared -> g)
        lvl_set
        g
    in
    UGraph.merge_constraints csts_set g
  in
  let initial_universes = update_ugraph uctx.initial_universes in
  let universes = update_ugraph uctx.universes in
  { uctx with local = (local_univs, local_constraints); univ_variables; universes; initial_universes }

let demote_global_univ_entry entry uctx = match entry with
  | Monomorphic_entry entry -> demote_global_univs entry uctx
  | Polymorphic_entry _ -> uctx

(* Check bug_4363 bug_6323 bug_3539 and success/rewrite lemma l1
   for quick feedback when changing this code *)
let emit_side_effects eff u =
  let uctx = Safe_typing.universes_of_private eff in
  demote_global_univs uctx u

let merge_seff uctx uctx' =
  let levels = ContextSet.levels uctx' in
  let declare g =
    Level.Set.fold (fun u g ->
        try UGraph.add_universe ~strict:false u g
        with UGraph.AlreadyDeclared -> g)
      levels g
  in
  let initial_universes = declare uctx.initial_universes in
  let univs = declare uctx.universes in
  let universes = merge_constraints uctx (ContextSet.constraints uctx') univs in
  { uctx with universes; initial_universes }

let update_sigma_univs uctx univs =
  let eunivs =
    { uctx with
      initial_universes = univs;
      universes = univs }
  in
  merge_seff eunivs eunivs.local

let add_qnames ?loc s l ((qnames,unames), (qnames_rev,unames_rev)) =
  if Id.Map.mem s qnames
  then user_err ?loc
      Pp.(str "Quality " ++ Id.print s ++ str" already bound.");
  ((Id.Map.add s l qnames, unames),
   (QVar.Map.add l { uname = Some s; uloc = loc } qnames_rev, unames_rev))

let add_names ?loc s l ((qnames,unames), (qnames_rev,unames_rev)) =
  if UNameMap.mem s unames
  then user_err ?loc
      Pp.(str "Universe " ++ Id.print s ++ str" already bound.");
  ((qnames,UNameMap.add s l unames),
   (qnames_rev, Level.Map.add l { uname = Some s; uloc = loc } unames_rev))

let add_qloc l loc (names, (qnames_rev,unames_rev) as orig) =
  match loc with
  | None -> orig
  | Some _ -> (names, (QVar.Map.add l { uname = None; uloc = loc } qnames_rev, unames_rev))

let add_loc l loc (names, (qnames_rev,unames_rev) as orig) =
  match loc with
  | None -> orig
  | Some _ -> (names, (qnames_rev, Level.Map.add l { uname = None; uloc = loc } unames_rev))

let add_universe ?loc name strict uctx u =
  let initial_universes = UGraph.add_universe ~strict u uctx.initial_universes in
  let universes = UGraph.add_universe ~strict u uctx.universes in
  let local = ContextSet.add_universe u uctx.local in
  let names =
    match name with
    | Some n -> add_names ?loc n u uctx.names
    | None -> add_loc u loc uctx.names
  in
  { uctx with names; local; initial_universes; universes }

let new_sort_variable ?loc ?name uctx =
  let q = UnivGen.new_sort_global () in
  (* don't need to check_fresh as it's guaranteed new *)
  let sort_variables = QState.add ~check_fresh:false ~rigid:(Option.has_some name)
      q uctx.sort_variables
  in
  let names = match name with
    | Some n -> add_qnames ?loc n q uctx.names
    | None -> add_qloc q loc uctx.names
  in
  { uctx with sort_variables; names }, q

let new_univ_variable ?loc rigid name uctx =
  let u = UnivGen.fresh_level () in
  let uctx =
    match rigid with
    | UnivRigid -> uctx
    | UnivFlexible algebraic ->
      let univ_variables = UnivFlex.add u ~algebraic uctx.univ_variables in
      { uctx with univ_variables }
  in
  let uctx = add_universe ?loc name false uctx u in
  uctx, u

let add_forgotten_univ uctx u = add_universe None true uctx u

let make_with_initial_binders univs binders =
  let uctx = make univs in
  List.fold_left
    (fun uctx { CAst.loc; v = id } ->
       fst (new_univ_variable ?loc univ_rigid (Some id) uctx))
    uctx binders

let from_env ?(binders=[]) env =
  make_with_initial_binders (Environ.universes env) binders

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

let collapse_above_prop_sort_variables ~to_prop uctx =
  { uctx with sort_variables = QState.collapse_above_prop ~to_prop uctx.sort_variables }

let collapse_sort_variables ?except uctx =
  { uctx with sort_variables = QState.collapse ?except uctx.sort_variables }

let minimize uctx =
  let open UnivMinim in
  let (vars', us') =
    normalize_context_set uctx.universes uctx.local uctx.univ_variables
      uctx.minim_extra
  in
  if ContextSet.equal us' uctx.local then uctx
  else
    let universes = UGraph.merge_constraints (snd us') uctx.initial_universes in
      { names = uctx.names;
        local = us';
        univ_variables = vars';
        sort_variables = uctx.sort_variables;
        universes = universes;
        initial_universes = uctx.initial_universes;
        minim_extra = UnivMinim.empty_extra; (* weak constraints are consumed *) }

let universe_context_inst_decl decl qvars levels names =
  let leftqs = List.fold_left (fun acc l -> QVar.Set.remove l acc) qvars decl.univdecl_qualities in
  let leftus = List.fold_left (fun acc l -> Level.Set.remove l acc) levels decl.univdecl_instance in
  let () =
    let unboundqs = if decl.univdecl_extensible_qualities then QVar.Set.empty else leftqs in
    let unboundus = if decl.univdecl_extensible_instance then Level.Set.empty else leftus in
    if not (QVar.Set.is_empty unboundqs && Level.Set.is_empty unboundus)
    then error_unbound_universes unboundqs unboundus names
  in
  let instq = Array.map_of_list (fun q -> Quality.QVar q) decl.univdecl_qualities in
  let instu = Array.of_list decl.univdecl_instance in
  let inst = Instance.of_array (instq,instu) in
  inst

let check_univ_decl_rev uctx decl =
  let levels, csts = uctx.local in
  let qvars = QState.undefined uctx.sort_variables in
  let inst = universe_context_inst_decl decl qvars levels uctx.names in
  let nas = compute_instance_binders uctx inst in
  let () =
    check_implication uctx
    csts
    decl.univdecl_constraints
  in
  let uctx = fix_undefined_variables uctx in
  let uctx, csts =
    if decl.univdecl_extensible_constraints
    then uctx, csts else restrict_constraints uctx decl.univdecl_constraints, decl.univdecl_constraints
  in
  let uctx' = UContext.make nas (inst, csts) in
  uctx, uctx'

let check_uctx_impl ~fail uctx uctx' =
  let levels, csts = uctx'.local in
  let qvars_diff =
    QVar.Set.diff
      (QState.undefined uctx'.sort_variables)
      (QState.undefined uctx.sort_variables)
  in
  let levels_diff = Level.Set.diff levels (fst uctx.local) in
  let () = if not @@ (QVar.Set.is_empty qvars_diff && Level.Set.is_empty levels_diff) then
    error_unbound_universes qvars_diff levels_diff uctx'.names
  in
  let () =
    let grext = ugraph uctx in
    let cstrs' = Constraints.filter (fun c -> not (UGraph.check_constraint grext c)) csts in
    if Constraints.is_empty cstrs' then ()
    else fail (Constraints.pr (pr_uctx_level uctx) cstrs')
  in
  ()


(* XXX print above_prop too *)
let pr_weak prl {minim_extra={UnivMinim.weak_constraints=weak; above_prop}} =
  let open Pp in
  v 0 (
    prlist_with_sep cut (fun (u,v) -> h (prl u ++ str " ~ " ++ prl v)) (UPairSet.elements weak)
    ++ if UPairSet.is_empty weak || Level.Set.is_empty above_prop then mt() else cut () ++
    prlist_with_sep cut (fun u -> h (str "Prop <= " ++ prl u)) (Level.Set.elements above_prop))

let pr_sort_opt_subst uctx = QState.pr (qualid_of_qvar_names uctx.names) uctx.sort_variables

let pr ctx =
  let open Pp in
  let prl = pr_uctx_level ctx in
  if is_empty ctx then mt ()
  else
    v 0
      (str"UNIVERSES:"++brk(0,1)++
       h (Univ.pr_universe_context_set prl (context_set ctx)) ++ fnl () ++
       UnivFlex.pr prl (subst ctx) ++ fnl() ++
       str"SORTS:"++brk(0,1)++
       h (pr_sort_opt_subst ctx) ++ fnl() ++
       str "WEAK CONSTRAINTS:"++brk(0,1)++
       h (pr_weak prl ctx) ++ fnl ())

module Internal =
struct

let reboot env uctx =
  let uctx_global = from_env env in
  { uctx_global with univ_variables = uctx.univ_variables; sort_variables = uctx.sort_variables }

end
