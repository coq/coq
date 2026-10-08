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

let template_default_univs = Summary.ref ~name:"template default univs" Univ.Level.Set.empty

let cache_template_default_univs us =
  let open Summary.Ref in
  template_default_univs := Univ.Level.Set.union !template_default_univs us

let template_default_univs_obj =
  Libobject.declare_object {
    (Libobject.default_object "template default univs") with
    cache_function = cache_template_default_univs;
    load_function = (fun _ us -> cache_template_default_univs us);
    discharge_function = (fun x -> Some x);
    classify_function = (fun _ -> Escape);
  }

let add_template_default_univs env kn =
  match Declareops.inductive_template (Environ.lookup_mind kn env) with
  | None -> ()
  | Some template ->
    let _, us = UVars.LevelInstance.levels template.template_defaults in
    Lib.add_leaf (template_default_univs_obj us)

let template_default_univs () =
  let open Summary.Ref in
  !template_default_univs

let _debug_ustate_flag, debug = CDebug.create_full ~name:"ustate" ()
let _debug_ustate_model_flag, debug_model = CDebug.create_full ~name:"ustate_model" ()

type universes_entry =
| Monomorphic_entry of Univ.ContextSet.t
| Polymorphic_entry of UVars.UContext.t * Entries.variance_entry

module UNameMap = Id.Map

type uinfo = {
  uname : Id.t option;
  uloc : Loc.t option;
}

open Quality

exception SortInconsistency of UGraph.univ_inconsistency

let sort_inconsistency ?explain cst l r =
  let explain = Option.map (fun p -> UGraph.Other p) explain in
  raise (SortInconsistency (None, (cst, l, r, explain)))

let univ_inconsistency ?explain cst l r =
  let explain = Option.map (fun p -> UGraph.Other p) explain in
  raise (UGraph.UniverseInconsistency (None, (cst, l, r, explain)))

module QSet = QVar.Set
module QMap = QVar.Map

type above_prop = AboveProp | BelowType

module QState : sig
  type t
  type elt = QVar.t
  val empty : t
  val is_empty : t -> bool
  val union : fail:(t -> Quality.t -> Quality.t -> t) -> t -> t -> t
  val add : check_fresh:bool -> rigid:bool -> elt -> t -> t
  val repr : elt -> t -> Quality.t
  val is_rigid : t -> QVar.t -> bool
  val is_above_prop : t -> QVar.t -> bool
  val set_above_prop : QVar.t -> above_prop -> t -> t option
  val unify_quality : fail:(unit -> t) -> Conversion.conv_pb -> Quality.t -> Quality.t -> t -> t
  val undefined : t -> QVar.Set.t
  val collapse : ?except:QVar.Set.t -> only_above_prop:bool -> t -> t
  val pr : Sorts.Quality.printer -> (QVar.t -> Id.t option) -> t -> Pp.t
  val of_elims : QGraph.t -> t
  val elims : t -> QGraph.t
  val set_elims : QGraph.t -> t -> t
  val initial_elims : t -> QGraph.t
  val merge_constraints : (QGraph.t -> QGraph.t) -> t -> t
  val normalize_elim_constraints : t -> ElimConstraints.t -> ElimConstraints.t
end =
struct

type node =
| Equiv of Quality.t
| Canonical of { rigid : bool }
(** Rigid variables may not be set to another *)

type t = {
  qmap : node QMap.t;
  (* TODO: use a persistent union-find structure *)
  above_prop : above_prop QMap.t;
  (** Set for quality variables known to be either in Prop or Type.
      If q ∈ above_prop then it must map to None in qmap. *)
  elims : QGraph.t;
  (** Elimination graph for quality variables. *)
  initial_elims : QGraph.t;
  (** Keep the qvar domain without any constraints to optimize computation. *)
}

type elt = QVar.t

let empty = { qmap = QMap.empty; above_prop = QMap.empty;
              elims = QGraph.initial_graph; initial_elims = QGraph.initial_graph }

let is_empty m = QMap.is_empty m.qmap && QSet.is_empty m.above_prop

let rec repr q m = match QMap.find q m.qmap with
| Canonical _ -> QVar q
| Equiv (QVar q) -> repr q m
| Equiv (QConstant _ | QGlobal _ as q) -> q
| exception Not_found -> QVar q

type repr =
| ReprConstant of Quality.constant
| ReprGlobal of QGlobal.t
| ReprVar of QVar.t * bool

let rec repr_node_qvar q m = match QMap.find q m.qmap with
| Canonical { rigid } -> ReprVar (q, rigid)
| Equiv q -> repr_node q m
| exception Not_found -> ReprVar (q, true) (* a bit dubious but missing variables are considered rigid *)

and repr_node q m = match q with
| QVar q -> repr_node_qvar q m
| (QConstant qc) -> ReprConstant qc
| (QGlobal q) -> ReprGlobal q

let is_above_prop m q = QMap.mem q m.above_prop

let above_prop m q = QMap.find_opt q m.above_prop

let eliminates_to_prop m q =
  QGraph.eliminates_to_prop m.elims (QVar q)

let is_rigid m q = match repr_node_qvar q m with
| ReprVar (_, rigid) -> rigid
| ReprConstant _ | ReprGlobal _ -> true

let set q qv m =
  let q = repr_node_qvar q m in
  let q, rigid = match q with
    | ReprVar (q, rigid) -> q, rigid
    | ReprConstant _ | ReprGlobal _ -> assert false
  in
  let qv = repr_node qv m in
  let enforce_eq q1 q2 g =
    let ans = QGraph.enforce_eliminates_to q1 q2 (QGraph.enforce_eliminates_to q2 q1 g) in
    let () = QGraph.check_rigid_paths ans in
    ans
  in
  match qv with
  | ReprVar (qv, _qvrigd) ->
    if QVar.equal q qv then Some m
    else if rigid then None
    else
      let above_prop =
        match above_prop m q with
        | None -> m.above_prop
        | Some above -> QMap.add qv above (QMap.remove q m.above_prop)
      in
      Some { m with
             qmap = QMap.add q (Equiv (QVar qv)) m.qmap; above_prop;
             elims = enforce_eq (QVar qv) (QVar q) m.elims; }
  | ReprConstant qc ->
    if qc == QSProp && (is_above_prop m q || eliminates_to_prop m q) then None
    else if rigid then None
    else
      let qv = QConstant qc in
      Some { m with qmap = QMap.add q (Equiv qv) m.qmap;
                    above_prop = QMap.remove q m.above_prop;
                    elims = enforce_eq qv (QVar q) m.elims }
  | ReprGlobal qg ->
    if is_above_prop m q then None
    else if rigid then None
    else
      let qv = QGlobal qg in
      Some { m with qmap = QMap.add q (Equiv qv) m.qmap;
                    above_prop = m.above_prop;
                    elims = enforce_eq qv (QVar q) m.elims }

let set_above_prop q above m =
  let q = repr_node_qvar q m in
  let q, rigid = match q with ReprVar (q, rigid) -> q, rigid | ReprConstant _ | ReprGlobal _ -> assert false in
  if rigid then None
  else
    let above_prop =
      QMap.update q (fun prev ->
          match above, prev with
          | _, Some BelowType -> Some BelowType
          | (AboveProp|BelowType), _ -> Some above)
        m.above_prop
    in
    Some { m with above_prop }

let unify_quality ~fail c q1 q2 local = match q1, q2 with
| QConstant QType, QConstant QType
| QConstant QProp, QConstant QProp
| QConstant QSProp, QConstant QSProp -> local
| QGlobal q1, QGlobal q2 -> if QGlobal.equal q1 q2 then local else fail ()
| QConstant QProp, QVar q when c == Conversion.CUMUL ->
  begin match set_above_prop q AboveProp local with
  | Some local -> local
  | None -> fail ()
  end
| QVar qv1, QVar qv2 -> begin match set qv1 q2 local with
    | Some local -> local
    | None -> match set qv2 q1 local with
      | Some local -> local
      | None -> fail ()
  end
(* TODO BelowType *)
| QVar q, (QConstant (QType | QProp | QSProp) | QGlobal _ as qv)
| (QConstant (QType | QProp | QSProp) | QGlobal _ as qv), QVar q ->
  begin match set q qv local with
  | Some local -> local
  | None -> fail ()
  end
| QGlobal _, QConstant _| QConstant _, QGlobal _ -> fail ()
| (QConstant QType, QConstant (QProp | QSProp)) -> fail ()
| (QConstant QProp, QConstant QType) ->
  begin match c with
  | CONV -> fail ()
  | CUMUL -> local
  end
| (QConstant QSProp, QConstant (QType | QProp)) -> fail ()
| (QConstant QProp, QConstant QSProp) -> fail ()

let nf_quality m = function
  | QConstant _ | QGlobal _ as q -> q
  | QVar q -> repr q m

let add_qvars m qmap qs =
  let g = m.initial_elims in
  let filter v = match QMap.find_opt v qmap with
  | None | Some (Canonical _) -> true
  | Some (Equiv _) -> false
  in
  (* Here, we filter instead of enforcing equality due to the collapse:
     simply enforcing equality may lead to inconsistencies after it *)
  let qs = QVar.Set.filter filter qs in
  let fold v g = try QGraph.add_quality (QVar v) g with QGraph.AlreadyDeclared -> g in
  QVar.Set.fold fold qs g

let union ~fail s1 s2 =
  let extra = ref [] in
  let qmap = QMap.union (fun qk q1 q2 ->
      match q1, q2 with
      | Equiv q, (Canonical {rigid}) | (Canonical {rigid}), Equiv q ->
        assert (not rigid);
        Some (Equiv q)
      | Canonical { rigid = r1 }, Canonical { rigid = r2 } ->
        assert (Bool.equal r1 r2);
        Some (Canonical { rigid = r1 })
      | Equiv q1, Equiv q2 ->
        let () = if not (Quality.equal q1 q2) then extra := (q1,q2) :: !extra in
        Some (Equiv q1))
      s1.qmap s2.qmap
  in
  let extra = !extra in
  let qs = QVar.Set.union (QGraph.qvar_domain s1.elims) (QGraph.qvar_domain s2.elims) in
  let filter_above v _ = match QMap.find_opt v qmap with
  | None | Some (Canonical _) -> true
  | Some (Equiv _) -> false
  in
  let above_union _ a b = match a, b with
    | AboveProp, AboveProp -> Some AboveProp
    | BelowType, _ | _, BelowType -> Some BelowType
  in
  let above_prop = QMap.filter filter_above @@ QMap.union above_union s1.above_prop s2.above_prop in
  let elims = add_qvars s2 qmap qs in
  let s = { qmap; above_prop;
            elims; initial_elims = elims } in
  List.fold_left (fun s (q1,q2) ->
      let q1 = nf_quality s q1 and q2 = nf_quality s q2 in
      unify_quality ~fail:(fun () -> fail s q1 q2) CONV q1 q2 s)
    s
    extra

let add ~check_fresh ~rigid q m =
  if check_fresh then assert (not (QMap.mem q m.qmap));
  let add_quality g =
    try QGraph.add_quality (QVar q) g
    with QGraph.AlreadyDeclared as e -> if check_fresh then raise e else g
  in
  { qmap = QMap.add q (Canonical { rigid }) m.qmap;
    above_prop = m.above_prop;
    elims = add_quality m.elims;
    initial_elims = add_quality m.initial_elims }

let of_elims elims =
  { empty with elims; initial_elims = elims }

(* XXX what about qvars in the elimination graph? *)
let undefined m =
  let filter _ v = match v with
  | Canonical _ -> true
  | Equiv _ -> false
  in
  let mq = QMap.filter filter m.qmap in
  QMap.domain mq

let collapse ?(except=QSet.empty) ~only_above_prop m =
  let free_qualities = QMap.fold (fun q v fqs ->
      match v with
      | Equiv _ -> fqs
      | Canonical _ -> QSet.add q fqs)
      m.qmap QSet.empty
  in
  let dominates_above_prop q q' =
    not (QVar.equal q q') && QGraph.eliminates_to m.elims (QVar q) (QVar q') && not (QMap.mem q m.above_prop)
  in
  QMap.fold (fun q v m ->
      match v with
      | Equiv _ -> m
      | Canonical { rigid } ->
        if rigid || QSet.mem q except then m
        (* This check is necessary because there is a particular scenario where we could end up
           with an unsatisfied elimination constraint or an unnecessary elaborated elimination constraint to Type
           (or some inexistent sort variable); if we simply defaulted sort variables to Type, as before.
           This comes from a weird interaction with "above Prop". The scenario is:
           - An unbound sort variable β might be set to be above Prop during unification, which in practice
             should be equal to Prop.
           - A rigid sort s eliminates to Prop explicitly (and β, since they are supposed to be equal)
           - Collapsing β to Type means that now sort s eliminates to Type, but this is an undeclared constraint,
             and therefore the declaration fails.

           This check is therefore simply finding if the sort variable above Prop is dominated by another one.
           If so, the sort variable collapses to Prop, otherwise to Type (if collapsing is enabled), or we keep it.
           TODO not sure if still needed with BelowType
        *)
        else match QMap.find_opt q m.above_prop with
          | Some BelowType ->
            if QSet.exists (fun q' -> dominates_above_prop q' q) free_qualities then
              Option.get (set q qprop m)
            else Option.get (set q qtype m)
          | Some AboveProp -> Option.get (set q qprop m)
          | None -> if not only_above_prop then Option.get (set q qtype m) else m)
    m.qmap m

let pr prqvar local_name ({ qmap; elims } as m) =
  let open Pp in
  (* Print the "body" of the QVar, e.g. "α1 := Type", "α2 >= Prop" *)
  let prbody u = function
  | Canonical { rigid } ->
    begin match above_prop m u with
    | Some AboveProp -> str " >= Prop"
    | Some BelowType -> str " <= Type"
    | None ->
      if rigid then
        str " (rigid)"
      else mt ()
    end
  | Equiv q ->
    let q = Quality.pr prqvar q in
    str " := " ++ q
  in
  (* Print the "name" (given by the user) of the Qvar, e.g. "(named s)" *)
  let prqvar_name q = match local_name q with
  | None -> mt ()
  | Some qid -> str " (named " ++ Id.print qid ++ str ")"
  in
  let prqvar_full (q1, q2) = QVar.raw_pr q1 ++ prbody q1 q2 ++ prqvar_name q1 in
  hov 0 (prlist_with_sep fnl prqvar_full (QMap.bindings qmap) ++
    str " |=" ++ brk (1, 2) ++ hov 0 (QGraph.pr_qualities prqvar elims))

let elims m = m.elims

let set_elims elims m = { m with elims }

let initial_elims m = m.initial_elims

let merge_constraints f m =
  { m with elims = f m.elims }

let normalize_elim_constraints m cstrs =
  let subst q = match q with
    | QConstant _ | QGlobal _ -> q
    | QVar qv -> repr qv m
  in
  let is_instantiated q = is_qconst q || is_qglobal q in
  let can_drop (q1,_,q2) = not (is_instantiated q1 && is_instantiated q2) in
  let subst_cst (q1,c,q2) = (subst q1,c,subst q2) in
  let cstrs = ElimConstraints.map subst_cst cstrs in
  let cstrs = ElimConstraints.filter can_drop cstrs in
  ElimConstraints.filter (fun (q1, _, q2) -> not @@ Quality.equal q1 q2) cstrs
end

module UPairSet = UnivMinim.UPairSet

type univ_names = UnivNames.universe_binders * (uinfo QVar.Map.t * uinfo Level.Map.t)

(* Checks consistency on the fly using the graph. The graph carries a substitution
  from levels to universes, but informs us of equivalences found between universes. *)
type t =
 { names : univ_names;
   (** Printing/location information *)

   local : Sorts.ElimConstraints.t; (** The local graph of universes (variables and constraints) *)

   local_variables : Level.Set.t;
   (** The rigid variables: those that must stay in the universe context. *)

   demoted_local_context : Univ.ContextSet.t;
   (** Variables and constraints that appear local in the graph but are actually already declared globally
      (due to a side effect). *)

   flexible_variables : Level.Set.t;
   (** The remaining flexible variables: local universes that are unification variables *)

   fixed_rigid_universes : bool;
   (** Are the rigid universes fixed. In this case, all the flexible variables will be instantiated during minimization *)

   fixed_rigid_constraints : bool;
  (** Are the (rigid) constraints fixed. In this case, at each constraint addition, we check that no new constraint on rigid universes
    are implied. *)

   sort_variables : QState.t;
   (** Local quality variables. *)

   universes : UGraph.t;
   (** The current graph extended with the local constraints *)

   initial_universes : UGraph.t;
   (** The graph at the creation of the evar_map + local universes
                                     (but not local constraints) *)

   variances : InferCumulativity.variances option;
   minim_extra : UnivMinim.extra;
 }

(** 3 Projections *)

let subst uctx = UGraph.subst ~local:true uctx.universes

let subst_fn uctx = UGraph.normalize uctx.universes

let ugraph uctx = uctx.universes

let is_flexible l uctx = Level.Set.mem l uctx.flexible_variables

let is_declared uctx l = UGraph.is_declared uctx.universes l
let empty =
  { names = UnivNames.empty_binders, (QVar.Map.empty, Level.Map.empty);
    local = Sorts.ElimConstraints.empty ;
    local_variables = Level.Set.empty;
    demoted_local_context = Univ.ContextSet.empty;
    flexible_variables = Level.Set.empty;
    fixed_rigid_universes = false;
    fixed_rigid_constraints = false;
    sort_variables = QState.empty;
    universes = UGraph.initial_universes;
    initial_universes = UGraph.initial_universes;
    variances = None;
    minim_extra = UnivMinim.empty_extra; }

let id_of_level uctx l =
  try (Level.Map.find l (snd (snd uctx.names))).uname
  with Not_found -> None

let id_of_qvar uctx l =
  try (QVar.Map.find l (fst (snd uctx.names))).uname
  with Not_found -> None

let is_rigid_qvar uctx q = QState.is_rigid uctx.sort_variables q

let get_uname info = match info.uname with
| None -> raise Not_found
| Some id -> id

let qualid_of_qvar_names (bind, (qrev,_)) l =
  try Some (Libnames.qualid_of_ident (get_uname (QVar.Map.find l qrev)))
  with Not_found ->
    UnivNames.qualid_of_quality bind (QVar l)

let qualid_of_level_names (bind, (_,urev)) l =
  try Some (Libnames.qualid_of_ident (get_uname (Level.Map.find l urev)))
  with Not_found ->
    UnivNames.qualid_of_level bind l

let qualid_of_level uctx l = qualid_of_level_names uctx.names l

let pr_uctx_qvar_names names l =
  match qualid_of_qvar_names names l with
  | Some qid -> Libnames.pr_qualid qid
  | None -> QVar.raw_pr l

let quality_printer_names names = {
  Sorts.Quality.prvar = pr_uctx_qvar_names names;
  prglobal = (UnivNames.quality_printer (fst names)).prglobal;
}

let quality_printer uctx = quality_printer_names uctx.names

let pr_uctx_level_names names l =
  match qualid_of_level_names names l with
  | Some qid -> Libnames.pr_qualid qid
  | None -> Level.raw_pr l

let sort_printer_names names = {
  Sorts.prq = quality_printer_names names;
  pru = pr_uctx_level_names names;
}

let sort_printer uctx = sort_printer_names uctx.names

let pr_uctx_level uctx l = pr_uctx_level_names uctx.names l

let pr_uctx_qglobal uctx q =
  UnivNames.pr_quality_with_global_universes ~binders:(fst uctx.names) (QGlobal q)

let pr_uctx_qvar uctx l = pr_uctx_qvar_names uctx.names l

let pr_weak prl {minim_extra={UnivMinim.weak_constraints=weak; above_prop; above_zero}} =
  let open Pp in
  v 0 (
    prlist_with_sep cut (fun (u,v) -> h (Universe.pr prl u ++ str " ~ " ++ Universe.pr prl v)) (UPairSet.elements weak)
    ++ if UPairSet.is_empty weak || Level.Set.is_empty above_prop then mt() else cut () ++
    prlist_with_sep cut (fun u -> h (str "Prop <= " ++ prl u)) (Level.Set.elements above_prop) ++
    if Level.Set.is_empty above_prop || Level.Set.is_empty above_zero then mt() else cut () ++
    prlist_with_sep cut (fun u -> h (str "Prop <= " ++ prl u)) (Level.Set.elements above_zero))

let pr_sort_opt_subst uctx =
  let local_name q = try Some (get_uname (QVar.Map.find q (fst @@ snd uctx.names)))
    with Not_found -> None
  in
  QState.pr (quality_printer uctx)
    local_name
    uctx.sort_variables

let is_empty uctx =
  Level.Set.is_empty uctx.local_variables &&
  Level.Set.is_empty uctx.flexible_variables &&
  QState.is_empty uctx.sort_variables &&
  Option.is_empty uctx.variances &&
  UPairSet.is_empty uctx.minim_extra.weak_constraints &&
  Level.Set.is_empty uctx.minim_extra.above_prop &&
  Level.Set.is_empty uctx.minim_extra.above_zero &&
  (let levels, cstrs, eqs = UGraph.constraints_of_universes ~only_local:true uctx.universes in
   Level.Set.is_empty levels && UnivConstraints.is_empty cstrs && Level.Map.is_empty eqs)

let pr ?(local=false) ctx =
  let open Pp in
  let prl = pr_uctx_level ctx in
  if is_empty ctx then mt ()
  else
    let levelsr, cstrs, eqs = UGraph.constraints_of_universes ~only_local:local ctx.universes in
    let preq (localeq, univ) =
      str " = " ++ Univ.Universe.pr prl univ ++
      (match localeq with Loop_checking.Local -> str "(local)" | _ -> str "(global)") ++ spc ()
    in
    let levelsr = Level.Set.diff levelsr ctx.local_variables in
    v 0
      (str"UNIVERSE VARIABLES:" ++ brk(0,1) ++
       h (Level.Set.pr prl ctx.local_variables) ++ fnl () ++
       str"RIGID UNIVERSE VARIABLES:" ++ brk(0,1) ++
       h (Level.Set.pr prl levelsr) ++ fnl () ++
       str"DEMOTED (GLOBAL) UNIVERSE VARIABLES:" ++ brk(0,1) ++
       h (Univ.ContextSet.pr prl ctx.demoted_local_context) ++ fnl () ++
       str"FLEXIBLE UNIVERSE VARIABLES:" ++ brk(0,1) ++
       h (Level.Set.pr prl ctx.flexible_variables) ++ fnl () ++
       str"DEFINED LOCAL VARIABLES:" ++ brk(0,1) ++
       h (Level.Map.pr prl preq eqs) ++ fnl () ++
       str"UNIVERSES:"++brk(0,1)++
       h (Univ.UnivConstraints.pr prl cstrs) ++ fnl() ++
       str"SORTS:"++brk(0,1)++
       h (pr_sort_opt_subst ctx) ++ fnl() ++
       (pr_opt (fun variances -> str"VARIANCES:"++brk(0,1)++
       h (InferCumulativity.pr_variances Univ.Level.raw_pr variances) ++ fnl ()) ctx.variances) ++
       str "WEAK CONSTRAINTS:"++brk(0,1)++
       h (pr_weak prl ctx) ++ fnl ())

let filter_set_constraints cstrs =
  UnivConstraints.filter (fun (l, d, r) -> not (Universe.is_type0 l && d == Le)) cstrs

let rigid_levels_constraints_of_substitution variables gvariables substitution (levels, cstrs) =
   Level.Map.fold (fun l (locality, u) (levels, cstrs) ->
     if Level.Set.mem l variables then
       Level.Set.add l levels, UnivConstraints.add (Universe.make l, Eq, u) cstrs
     else if locality == UGraph.Global || Level.Set.mem l gvariables then
       levels, UnivConstraints.add (Universe.make l, Eq, u) cstrs
     else levels, cstrs) substitution (levels, cstrs)

let univ_context_set uctx : Univ.ContextSet.t =
  let levels, cstrs, eqs =
    UGraph.constraints_of_universes ~only_local:true uctx.universes in
  let cstrs = filter_set_constraints cstrs in
  let levels = Level.Set.union uctx.local_variables levels in
  let dlevels, dcstrs = uctx.demoted_local_context in
  let lvls, univ_cstrs = rigid_levels_constraints_of_substitution uctx.local_variables dlevels eqs
    (Level.Set.diff levels dlevels, UnivConstraints.diff cstrs dcstrs)
  in
  lvls, univ_cstrs

let univ_context_set uctx =
  let ctx = univ_context_set uctx in
  debug Pp.(fun () -> str"Rigid context set of " ++ pr ~local:true uctx ++ fnl () ++ str" = " ++ Univ.ContextSet.pr Level.raw_pr ctx);
  ctx

let context_set uctx =
  let levels, univ_csts = univ_context_set uctx in
  levels, (uctx.local, univ_csts)

let merge_univ_constraints uctx cstrs g =
  try UGraph.merge_constraints cstrs g
  with UGraph.UniverseInconsistency (_, i) ->
    raise (UGraph.UniverseInconsistency (Some (sort_printer uctx), i))

type constraint_source =
| Internal
| Rigid
| Static

let merge_elim_constraints ?(src = Internal) uctx cstrs g =
  try
    let g = QGraph.merge_constraints cstrs g in
    match src with
    | Static -> g
    | Internal ->
      let () = if not (ElimConstraints.is_empty cstrs) then QGraph.check_rigid_paths g in
      g
    | Rigid ->
      let fold (q1, _, q2) accu = QGraph.add_rigid_path q1 q2 accu in
      Sorts.ElimConstraints.fold fold cstrs g
  with QGraph.(EliminationError (QualityInconsistency (_, i))) ->
    raise (QGraph.(EliminationError (QualityInconsistency (Some (quality_printer uctx), i))))

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

let update_univ_subst_gen f vars flex variances subst =
  let flex, vars = List.fold_left (fun (flex, vars) (l, u) ->
    if Level.Set.mem l flex then (Level.Set.remove l flex, Level.Set.remove l vars)
    else flex, vars (* A rigid universe was unified with u *)) (flex, vars) subst in
  (* let flex = List.fold_left (fun ls (l, u) -> Level.Set.remove l ls) flex subst in *)
  let variances = Option.map (fun variances -> List.fold_right (fun (l, u) variances ->
    Level.Map.remove l (UnivMinim.update_variances variances l (Univ.Universe.levels (f u)))) subst variances) variances in
  vars, flex, variances

let update_univ_subst = update_univ_subst_gen identity
let update_univ_expr_subst = update_univ_subst_gen Universe.of_expr

let push_subst eqs graph =
  let fold l (local, u) (graph, equivs) =
    try let graph, equivs' = UGraph.set l u graph in
      graph, (l, u) :: List.map (fun (l, u) -> l, Universe.of_expr u) equivs' @ equivs
    with Loop_checking.NotCanonical
       | Loop_checking.OccurCheck
       | Loop_checking.InconsistentEquality ->
        let graph, equivs' = UGraph.enforce_constraint (Universe.make l, Eq, u) graph in
        graph, List.map (fun (l, u) -> l, Universe.of_expr u) equivs' @ equivs
  in
  Level.Map.fold fold eqs (graph, [])

let union uctx uctx' =
  if uctx == uctx' then uctx
  else if is_empty uctx' then uctx
  else
    let () = debug Pp.(fun () -> str"Union of " ++ pr ~local:true uctx ++ str " and " ++ spc () ++ pr ~local:true uctx') in
    (* Note: levelsr does not contain the domain of eqs *)
    let levelsr, cstrsr, eqs = UGraph.constraints_of_universes ~only_local:true uctx'.universes in
    (* Declare all levels: we are going to [set] the defined ones *)
    let levelsr = Level.Set.union levelsr (Level.Map.domain eqs) in
    let () = debug Pp.(fun () -> str"Levelsr = " ++ Level.Set.pr Level.raw_pr levelsr) in
    let uctx_subst = subst uctx in
    let levelsr = Level.Set.diff levelsr uctx.local_variables in
    let levelsr = Level.Set.diff levelsr (Level.Map.domain uctx_subst) in
    let () = debug Pp.(fun () -> str"Levelsr = " ++ Level.Set.pr Level.raw_pr levelsr) in
    let local = ElimConstraints.union uctx.local uctx'.local in
    let names = names_union uctx.names uctx'.names in
    let variances = Option.union InferCumulativity.union_variances uctx.variances uctx'.variances in
    let extra = UnivMinim.extra_union uctx.minim_extra uctx'.minim_extra in
    let declarenew levels g =
      Level.Set.fold (fun u g ->
        if UGraph.is_declared g u then g
        else UGraph.add_universe u ~strict:false
        ~rigid:(not (Level.Set.mem u uctx'.flexible_variables)) g) levels g
    in
    let local_variables = Level.Set.union uctx.local_variables uctx'.local_variables in
    let flexible_variables = Level.Set.union uctx.flexible_variables uctx'.flexible_variables in
    let fail_union s q1 q2 =
      if QGraph.ignore_constraints (QState.elims uctx.sort_variables) then s else
      CErrors.user_err
        Pp.(str "Could not merge universe contexts: could not unify" ++ spc() ++
           Quality.raw_pr q1 ++ strbrk " and " ++ Quality.raw_pr q2 ++ str ".")
    in
    let universes = declarenew levelsr uctx.universes in
    let universes, equivs = push_subst eqs universes in
    let local_variables, flexible_variables, variances =
      update_univ_subst local_variables flexible_variables variances equivs
    in
    debug Pp.(fun () -> str"Union of substitutions = " ++ UGraph.pr ~local:true Level.raw_pr universes);
    let universes, equivs = merge_univ_constraints uctx cstrsr universes in
    let local_variables, flexible_variables, variances =
      update_univ_expr_subst local_variables flexible_variables variances equivs
    in
    let uctx = { names;
        local;
        local_variables;
        demoted_local_context = Univ.ContextSet.union uctx.demoted_local_context uctx'.demoted_local_context;
        flexible_variables;
        fixed_rigid_universes = uctx.fixed_rigid_universes;
        fixed_rigid_constraints = uctx.fixed_rigid_constraints;
        sort_variables = QState.union ~fail:fail_union uctx.sort_variables uctx'.sort_variables;
        initial_universes = declarenew levelsr uctx.initial_universes;
        universes;
        variances;
        minim_extra = extra} in
    debug Pp.(fun () -> str"Union = " ++ pr ~local:true uctx);
    uctx

let universe_context_set uctx = univ_context_set uctx

let sort_context_set uctx =
  let us, csts = context_set uctx in
  (QState.undefined uctx.sort_variables, us), csts

let constraints uctx = snd (context_set uctx)

let compute_instance_binders uctx inst =
  let (qrev, urev) = snd uctx.names in
  let qinst, uinst = LevelInstance.to_array inst in
  let qmap = function
    | QVar q ->
      begin try Name (get_uname (QVar.Map.find q qrev))
      with Not_found -> Anonymous
      end
    | QConstant _ | QGlobal _ -> assert false
  in
  let umap lvl =
    try Name (get_uname (Level.Map.find lvl urev))
    with Not_found -> Anonymous
  in
  {quals = Array.map qmap qinst; univs =  Array.map umap uinst}

let context uctx =
  let qvars = QState.undefined uctx.sort_variables in
  UContext.of_context_set (compute_instance_binders uctx) ((qvars, uctx.local), univ_context_set uctx)

type named_universes_entry =
  { universes_entry_universes : universes_entry;
    universes_entry_binders : UnivNames.universe_binders }

let check_mono_sort_constraints uctx =
  (* This looks very stringent but it passes nonetheless all the tests? *)
  let () = assert (Sorts.ElimConstraints.is_empty uctx.local) in
  univ_context_set uctx

let univ_entry ~poly ?variances uctx =
  let (binders, _) = uctx.names in
  let entry =
    if PolyFlags.univ_poly poly then Polymorphic_entry (context uctx, variances)
    else
      (assert (Option.is_empty variances);
       let uctx = check_mono_sort_constraints uctx in
       Monomorphic_entry uctx) in
  { universes_entry_universes = entry;
    universes_entry_binders = binders }

(** Merge the given constraint set in the universe context. Assumes the universes
  from the constraints are already declared. *)
let merge_constraints uctx cstrs =
  let universes, equivs = merge_univ_constraints uctx cstrs uctx.universes in
  let local_variables, flexible_variables, variances =
    update_univ_expr_subst uctx.local_variables uctx.flexible_variables uctx.variances equivs
  in
    { uctx with
      local_variables;
      flexible_variables;
      universes;
      variances; }

(** Merge the given context set in the universe context.
  Does not assume the universes from the context are already declared. *)
let merge_context_universes ~strict uctx (us, csts)  =
  debug Pp.(fun () -> str"merge_context_universes : " ++ Univ.ContextSet.pr Level.raw_pr (us, csts));
  let declarenew g = Level.Set.fold (fun v g -> if Level.is_set v then g else
    try UGraph.add_universe v ~strict ~rigid:true g with UGraph.AlreadyDeclared -> g) us g in
  let uctx = merge_constraints { uctx with universes = declarenew uctx.universes;
    initial_universes = declarenew uctx.initial_universes } csts in
  debug Pp.(fun () -> str"After merge of context set: " ++ pr uctx);
  uctx

let elim_graph uctx = QState.elims uctx.sort_variables
let initial_elim_graph uctx = QState.initial_elims uctx.sort_variables

let is_above_prop uctx qv = QState.is_above_prop uctx.sort_variables qv

let of_names (ubind,(revqbind,revubind)) =
  let revqbind = QVar.Map.map (fun id -> { uname = Some id; uloc = None }) revqbind in
  let revubind = Level.Map.map (fun id -> { uname = Some id; uloc = None }) revubind in
  let qgraph = QVar.Map.fold (fun v _ -> QGraph.add_quality (QVar v)) revqbind QGraph.initial_graph in
  { empty with names = (ubind,(revqbind,revubind));
               sort_variables = QState.of_elims qgraph; }

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
  UnivSubst.(subst_univs_universe (UGraph.normalize uctx.universes)) u

let nf_level uctx u =
  UnivSubst.(level_subst_of (UGraph.normalize uctx.universes)) u

let nf_instance uctx u = Instance.subst_fn (nf_qvar uctx, nf_level uctx) u

let nf_quality uctx q = Quality.subst (nf_qvar uctx) q

let nf_sort uctx s =
  let normalize u = nf_level uctx u in
  let qnormalize q = QState.repr q uctx.sort_variables in
  Sorts.subst_fn (qnormalize, normalize) s

let nf_relevance uctx r = match r with
| Relevant | Irrelevant -> r
| RelevanceVar q ->
  match nf_qvar uctx q with
  | QConstant QSProp -> Sorts.Irrelevant
  | QConstant QProp | QConstant QType | QGlobal _ -> Sorts.Relevant
  | QVar q' ->
    (* XXX currently not used in nf_evars_and_universes_opt_subst
       does it matter? *)
    if QState.is_above_prop uctx.sort_variables q' then Relevant
    else if QVar.equal q q' then r
    else Sorts.RelevanceVar q'

let nf_universes uctx c =
  let nf_univ u = UGraph.normalize uctx.universes u in
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
| ULevel of Level.t * Universe.t (* Var or Global *)
| UAlgebraic of Universe.t (* Arbitrary algebraic expression *)

let classify s = match s with
| Prop -> USmall UProp
| SProp -> USmall USProp
| Set -> USmall USet
| Type u | GSort (_, u) | VSort (_, u) ->
  match Universe.level u with
  | None -> UAlgebraic u
  | Some l -> ULevel (l, u)

let update_local_expr_equivalences local equivs =
  let local_variables, flexible_variables, variances =
    update_univ_expr_subst local.local_variables local.flexible_variables local.variances equivs
  in
  { local with local_variables; flexible_variables; variances }

let update_local_equivalences local equivs =
  let local_variables, flexible_variables, variances =
    update_univ_subst local.local_variables local.flexible_variables local.variances equivs
  in
  { local with local_variables; flexible_variables; variances }

let add_local_univ cstr local =
  let universes, equivs = UGraph.enforce_constraint cstr local.universes in
  let local = update_local_expr_equivalences local equivs in
  { local with universes }

(* Constraint with algebraic on the left and a single level on the right *)
let enforce_leq_up u v local =
  add_local_univ (u, Le, Universe.make v) local

let pr_level_equiv =
  let open Pp in
  let pr_subst (l, u) = Level.raw_pr l ++ str " := " ++ Universe.pr Level.raw_pr u in
  prlist_with_sep spc pr_subst

let pr_graph g =
  let repr = UGraph.repr ~local:true g in
  UGraph.pr_universes Level.raw_pr repr

let instantiate_variable l (b : Universe.t) local =
  debug Pp.(fun () -> str"Instantiating " ++ Level.raw_pr l ++ str " with " ++ Universe.pr Level.raw_pr b ++ str" variances? " ++ bool (not (Option.is_empty local.variances)));
  debug Pp.(fun () -> str"Context: " ++ Level.Set.pr Level.raw_pr local.local_variables ++ fnl () ++
     str"Constraints: :" ++ pr_graph local.universes);
  let universes, equivs =
    try UGraph.set l b local.universes
    with Loop_checking.NotCanonical
       | Loop_checking.OccurCheck -> UGraph.enforce_constraint (Universe.make l, Eq, b) local.universes
       | UGraph.InconsistentEquality ->
      debug Pp.(fun () -> str"Inconsistent equality!");
      univ_inconsistency Eq (Sorts.sort_of_univ (Universe.make l)) (Sorts.sort_of_univ b)
  in
  let equivs = (l, b) :: List.map (fun (l, u) -> l, Universe.of_expr u) equivs in
  debug Pp.(fun () -> str"Equivalences from set: " ++ pr_level_equiv equivs);
  debug_model Pp.(fun () -> str"Model after set: " ++ pr_graph universes);
  let local = update_local_equivalences { local with universes } equivs in
  debug Pp.(fun () -> str"Substitution after set: " ++ Level.Set.pr Level.raw_pr local.flexible_variables);
  local

let get_constraint = function
| Conversion.CONV -> UnivConstraint.Eq
| Conversion.CUMUL -> UnivConstraint.Le

let warn_template =
  CWarnings.create_warning ~from:[CWarnings.CoreCategories.fragile] ~default:Disabled ~name:"bad-template-constraint" ()

let do_warn_template = CWarnings.create_in warn_template
    Pp.(fun (uctx,csts) ->
        str "Adding constraints involving global template univs:" ++ spc() ++
        UnivConstraints.pr (pr_uctx_level uctx) csts )

(*FIXME: MS reenable warning *)
let _warn_template uctx csts =
  match CWarnings.warning_status warn_template with
  | Disabled -> ()
  | Enabled | AsError ->
  let is_template u = Level.Set.subset (Universe.levels u) (template_default_univs()) in
  let csts = UnivConstraints.filter (fun (u,_,v as cst) ->
      not (Universe.is_type0 u) && not (Universe.is_type0 v) &&
      (is_template u || is_template v) &&
      not (UGraph.check_constraint uctx.universes cst)) csts in
  if not @@ UnivConstraints.is_empty csts then
    do_warn_template (uctx,csts)

let unify_quality c s1 s2 l =
  let fail () =
    if QGraph.ignore_constraints (QState.elims l.sort_variables) then l.sort_variables else
    sort_inconsistency (get_constraint c) s1 s2
  in
  { l with
    sort_variables = QState.unify_quality ~fail
        c (Sorts.quality s1) (Sorts.quality s2) l.sort_variables;
  }

let normalize_universe graph u = UnivSubst.(subst_univs_universe (UGraph.normalize graph)) u

let add_local_univ fo c local =
  if fo then
    if UGraph.check_constraint local.universes c then local
    else raise UniversesDiffer
  else if local.fixed_rigid_constraints then
    (* Check that we don't add a constraint that is too strict w.r.t. rigid universes *)
    if UGraph.check_constraint local.universes c then local
    else
    let local' = add_local_univ c local in
    let newcstrs = UGraph.constraints_for ~kept:(Level.Set.diff local.local_variables local.flexible_variables) local'.universes in
    if UnivConstraints.for_all (fun c -> UGraph.check_constraint local.universes c) newcstrs then
      local'
    else
      (* The constraint is too strict *)
      let (l, cst, r) = c in
      raise (UGraph.UniverseInconsistency (None, (cst, Sorts.sort_of_univ l, Sorts.sort_of_univ r, None)))
  else add_local_univ c local

let process_constraints ?src uctx cstrs =
  let open UnivProblem in
  (* let quals = elim_graph uctx in *)
  let normalize local u = UGraph.normalize local.universes u in
  let qnormalize local q = QState.repr q local.sort_variables in
  let normalize_univ local u = normalize_universe local.universes u in
  let normalize_sort local s =
    Sorts.subst_fn ((qnormalize local), UnivSubst.subst_univs_level (normalize local)) s
  in
  let nf_constraint local = function
    | QElimTo (a, b) -> QElimTo (Quality.subst (qnormalize local) a, Quality.subst (qnormalize local) b)
    | QLeq (a, b) -> QLeq (Quality.subst (qnormalize local) a, Quality.subst (qnormalize local) b)
    | QEq (a, b) -> QEq (Quality.subst (qnormalize local) a, Quality.subst (qnormalize local) b)
    | ULub (c, u, v) -> ULub (c, normalize_univ local u, normalize_univ local v)
    | UWeak (u, v) -> UWeak (normalize_univ local u, normalize_univ local v)
    | UEq (u, v) -> UEq (normalize_sort local u, normalize_sort local v)
    | ULe (u, v) -> ULe (normalize_sort local u, normalize_sort local v)
  in
  let is_flexible local l = Level.Set.mem l local.flexible_variables in
  let all_flexible local = Universe.for_all (fun (l,k) -> is_flexible local l) in
  let equalize_small fo l s local =
    let ls = match l with
    | USProp -> sprop
    | UProp -> prop
    | USet -> set
    in
    if UGraph.check_eq_sort Sorts.Quality.equal local.universes ls s then local
    else if is_uset l then match classify s with
    | USmall _ -> univ_inconsistency Eq set s
    | ULevel (r, ru) ->
      if is_flexible local r then
        try instantiate_variable r Universe.type0 local
        with UGraph.OccurCheck -> assert false
      else
        (* Warn? Setting a rigid universe to 0 *)
        add_local_univ fo (ru, Eq, Universe.type0) local
    | UAlgebraic u ->
      let inst = univ_level_rem Level.set u u in
      let repr = Univ.Universe.repr inst in
      if List.for_all (fun (l, k) -> Int.equal k 0 && is_flexible local l) repr then (* No n+k expression, we can just unify set with each expression *)
        let rec instantiate_univ local repr =
          List.fold_left (fun local (l, _) ->
            try
              match normalize local l with
              | None ->
                if is_flexible local l then instantiate_variable l Universe.type0 local
                else add_local_univ fo (Universe.make l, Eq, Universe.type0) local
              | Some u -> instantiate_univ local (Univ.Universe.repr u)
            with UGraph.OccurCheck -> assert false) local repr
        in instantiate_univ local repr
      else univ_inconsistency Eq ls s
    else univ_inconsistency Eq ls s
  in
  let equalize_variables fo l' r' local =
    if Level.equal l' r' then local
    else
      if is_flexible local l' then
        instantiate_variable l' (Universe.make r') local
      else if is_flexible local r' then
        instantiate_variable r' (Universe.make l') local
      else
        if (Level.is_set l') || (Level.is_set r') then
          level_inconsistency Eq l' r'
        else
          add_local_univ fo (Universe.make l', Eq, Universe.make r') local
  in
  let equalize_variables fo l r local =
    try equalize_variables fo l r local
    with UGraph.OccurCheck -> add_local_univ fo (Universe.make l, Eq, Universe.make r) local
  in
  let equalize_algebraic fo l ru local =
    let inst = univ_level_rem l ru ru in
    if not (Level.Set.mem l (Universe.levels inst)) then
      if is_flexible local l then
        (try instantiate_variable l inst local
         with UGraph.OccurCheck -> assert false)
      else
        add_local_univ fo (Universe.make l, Eq, ru) local
    else
      if univ_level_mem l ru then
        enforce_leq_up inst l local
      else univ_inconsistency Eq (sort_of_univ (Universe.make l)) (sort_of_univ ru)
  in
  let equalize_universes fo l r local = match classify l, classify r with
  | USmall l', (USmall _ | ULevel _ | UAlgebraic _) ->
    equalize_small fo l' r local
  | (ULevel _ | UAlgebraic _), USmall r' ->
    equalize_small fo r' l local
  | ULevel (l', _), ULevel (r', _) ->
    equalize_variables fo l' r' local
  | ULevel (l', _), UAlgebraic r | UAlgebraic r, ULevel (l', _) ->
    equalize_algebraic fo l' r local
  | UAlgebraic l', UAlgebraic r' ->
    let fo = fo && (not (all_flexible local l') && not (all_flexible local r')) in
    add_local_univ fo (l', Eq, r') local
  in
  let enforce_le fo local l r =
    let local = unify_quality CUMUL l r local in
    let l = normalize_sort local l in
    let r = normalize_sort local r in
    begin match classify r with
    | USmall r' ->
      (* Invariant: there are no universes u <= Set in the graph. Except for
          template levels, Set <= u anyways. Otherwise, for template
          levels, any constraint u <= Set is turned into u := Set. *)
      if UGraph.type_in_type local.universes then local
      else begin match classify l with
      | UAlgebraic ul ->
        if Universe.is_levels ul then
          if is_uset r' then
            let fold l' local =
              if Level.is_set l' || is_flexible local l' then
                equalize_variables false l' Level.set local
              else
                let l = Sorts.sort_of_univ @@ Universe.make l' in
                univ_inconsistency Le l r
            in
            Level.Set.fold fold (Universe.levels ul) local
          else
            univ_inconsistency Le l r
        else
          (* l contains a +1 and r=r' small so l <= r impossible *)
          univ_inconsistency Le l r
      | USmall l' ->
        if UGraph.check_leq_sort Sorts.Quality.equal local.universes l r then local
        else univ_inconsistency Le l r
      | ULevel (l', _) ->
        if is_uset r' && is_flexible local l' then
          (* Unbounded universe constrained from above, we equalize it *)
          (try instantiate_variable l' Universe.type0 local
            with UGraph.OccurCheck -> assert false)
        else
          univ_inconsistency Le l r
      end
    | ULevel (_, r') | UAlgebraic r' ->
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
        let minim_extra = UnivMinim.{ local.minim_extra with above_prop = Level.Set.union (Universe.levels r') local.minim_extra.above_prop } in
        { local with minim_extra }
      | USmall USProp ->
        if UGraph.type_in_type local.universes then local
        else univ_inconsistency Le l r
      | USmall USet ->
        let minim_extra = UnivMinim.{ local.minim_extra with above_zero = Level.Set.union (Universe.levels r') local.minim_extra.above_zero } in
        let local = { local with minim_extra } in
        add_local_univ fo (Universe.type0, Le, r') local
      | ULevel (_, l') | UAlgebraic l' ->
        add_local_univ fo (l', Le, r') local
    end
  in
  let unify_universes cst local =
    let cst = nf_constraint local cst in
    (* TODO univ_inconsistency should be able to handle raw
       qualities instead of having to make a dummy sort *)
    let mk q = Sorts.make q Universe.type0 in
    if UnivProblem.is_trivial cst then local
    else match cst with
    | QEq (a, b) -> unify_quality CONV (mk a) (mk b) local
    | QLeq (a, b) -> unify_quality CUMUL (mk a) (mk b) local
    | QElimTo (a, b) ->
       let local' = ElimConstraints.add (a, ElimConstraint.ElimTo, b) local.local in
       { local with local = local' }
    | ULe (l, r) -> enforce_le false local l r
    | ULub (c, l, r) ->
      if all_flexible local l || all_flexible local r then
        match c with
        | Eq -> equalize_universes false (Sorts.sort_of_univ l) (Sorts.sort_of_univ r) local
        | Le -> enforce_le false local (Sorts.sort_of_univ l) (Sorts.sort_of_univ r)
      else
      (match Universe.level l, c, Universe.level r with
      | Some l, Eq, Some r -> equalize_variables true l r local
      | _, _, _ ->
        match c with
        | Eq -> equalize_universes true (Sorts.sort_of_univ l) (Sorts.sort_of_univ r) local
        | Le -> enforce_le true local (Sorts.sort_of_univ l) (Sorts.sort_of_univ r))
    | UWeak (l, r) ->
      if weak_constraints ()
      then
        let minim_extra = UnivMinim.{ local.minim_extra with
           weak_constraints = UPairSet.add (l, r) local.minim_extra.weak_constraints } in
        { local with minim_extra }
      else local
    | UEq (l, r) ->
      let local = unify_quality CONV l r local in
      let l = normalize_sort local l in
      let r = normalize_sort local r in
      equalize_universes false l r local
  in
  let unify_universes cst local =
    try unify_universes cst local
    with
      | SortInconsistency e
        when QGraph.ignore_constraints (QState.elims local.sort_variables) -> local
      | SortInconsistency e as exn ->
        let info = Exninfo.info exn in
        Exninfo.iraise (UGraph.UniverseInconsistency e, info)
      | UGraph.UniverseInconsistency _ when UGraph.type_in_type local.universes -> local
  in
  let uctx' = UnivProblem.Set.fold unify_universes cstrs uctx in
  (* FIXME: MS: reinstant warn template on the clauses that are added *)
  (* let () = warn_template uctx' ( PConstraints.univs local.local_cst) in *)
  uctx'

let process_constraints ?src (uctx : t) cstrs =
  if UnivProblem.Set.is_empty cstrs then uctx
  else begin
    debug Pp.(fun () -> str"Calling process_universe_constraints with: " ++ UnivProblem.Set.pr cstrs ++
    spc () ++ str"Context: " ++ Level.Set.pr Level.raw_pr uctx.local_variables);
    try let res = process_constraints ?src uctx cstrs in
      debug Pp.(fun () -> str"process_constraints terminated with: " ++ pr ~local:true res);
      res
    with Stack_overflow -> CErrors.anomaly (Pp.str "process_constraint raised a stack overflow")
    | UGraph.UniverseInconsistency incon as e ->
      debug Pp.(fun () -> str"process_constraint failed with inconsistency: "
      ++ UGraph.explain_universe_inconsistency (sort_printer uctx) incon); raise e
  end

(* FIXME: MS: enforce quality constraints as part of process_constraints *)

let add_constraints ?src uctx cstrs =
  let uctx' = process_constraints uctx cstrs in
  let sorts = uctx'.sort_variables in
  let sort_variables =
    QState.merge_constraints (merge_elim_constraints ?src uctx uctx'.local) sorts
  in
  { uctx' with
    local = ElimConstraints.union uctx.local uctx'.local;
    sort_variables;
    }

let set_above_prop q above uctx =
  match above with
  | AboveProp ->
    add_constraints uctx (UnivProblem.Set.singleton (QLeq (QConstant QProp, QVar q)))
  | BelowType ->
    match QState.set_above_prop q BelowType uctx.sort_variables with
    | Some sort_variables -> { uctx with sort_variables }
    | None ->
      (* TODO handle BelowType in unify_quality and use
         add_constraints here for more uniform erroring? *)
      CErrors.user_err Pp.(str "Could not enforce " ++ pr_uctx_qvar uctx q ++ str " <= Type.")

let problem_of_univ_constraints cstrs =
  UnivConstraints.fold (fun (l,d,r) acc ->
      let l = sort_of_univ l and r = sort_of_univ r in
      let cstr' = let open UnivProblem in
        match d with
        | Le -> ULe (l, r)
        | Eq -> UEq (l, r)
      in UnivProblem.Set.add cstr' acc)
    cstrs UnivProblem.Set.empty

let problem_of_elim_constraints cstrs =
  ElimConstraints.fold (fun (l, k, r) pbs ->
      let open ElimConstraint in
      match k with
      | ElimTo -> UnivProblem.Set.add (QElimTo (l, r)) pbs)
    cstrs UnivProblem.Set.empty

let add_univ_constraints uctx cstrs =
  let cstrs = problem_of_univ_constraints cstrs in
  add_constraints ~src:Static uctx cstrs

let add_poly_constraints ?src uctx (qcstrs, ucstrs) =
  let lvl_pbs = problem_of_univ_constraints ucstrs in
  let elim_pbs = problem_of_elim_constraints qcstrs in
  let uctx = add_constraints ?src uctx (UnivProblem.Set.union lvl_pbs elim_pbs) in
  let sort_variables = QState.merge_constraints (fun cst -> merge_elim_constraints ?src uctx qcstrs cst) uctx.sort_variables in
  { uctx with sort_variables }

let check_elim_constraints uctx csts =
  Sorts.ElimConstraints.for_all (fun (l,k,r) ->
      let l = nf_quality uctx l in
      let r = nf_quality uctx r in
      match l,k,r with
        | _, ElimTo, _ -> Inductive.eliminates_to (QState.elims uctx.sort_variables) l r)
    csts

let check_eq_quality uctx q1 q2 =
  Sorts.Quality.equal q1 q2 || Sorts.Quality.equal (nf_quality uctx q1) (nf_quality uctx q2)

let check_constraint uctx (c:UnivProblem.t) =
  match c with
  | QEq (a,b) ->
    let a = nf_quality uctx a in
    let b = nf_quality uctx b in
    Quality.equal a b
  | QLeq (a,b) ->
    let a = nf_quality uctx a in
    let b = nf_quality uctx b in
    Quality.equal a b ||
      begin
        match a, b with
        | QConstant QProp, QConstant QType -> true
        | QConstant QProp, QVar q -> QState.is_above_prop uctx.sort_variables q
        | (QConstant _ | QVar _ | QGlobal _), _ -> false
      end
  | QElimTo (a, b) ->
    let a = nf_quality uctx a in
    let b = nf_quality uctx b in
    Inductive.eliminates_to (QState.elims uctx.sort_variables) a b
  | ULe (u,v) -> UGraph.check_leq_sort (fun q1 q2 -> check_eq_quality uctx q1 q2) uctx.universes u v
  | UEq (u,v) -> UGraph.check_eq_sort (fun q1 q2 -> check_eq_quality uctx q1 q2) uctx.universes u v
  | ULub (Eq,u,v) -> UGraph.check_eq uctx.universes u v
  | ULub (Le,u,v) -> UGraph.check_leq uctx.universes u v
  | UWeak _ -> true

let check_constraints uctx csts =
  debug Pp.(fun () -> str"Calling check_constraints with: " ++ UnivProblem.Set.pr csts);
  UnivProblem.Set.for_all (check_constraint uctx) csts

let constrain_variables diff (uctx : t) =
  { uctx with flexible_variables = Level.Set.diff uctx.flexible_variables diff;
    local_variables = Level.Set.union diff uctx.local_variables }

type ('a, 'b, 'c, 'd, 'e) gen_universe_decl = {
  univdecl_qualities : 'a;
  univdecl_extensible_qualities : bool;
  univdecl_elim_constraints : 'b;
  univdecl_instance : 'c; (* Declared universes *)
  univdecl_extensible_instance : bool; (* Can new universes be added *)
  univdecl_variances : 'd; (* Universe variance information *)
  univdecl_univ_constraints : 'e; (* Declared univ constraints *)
  univdecl_extensible_constraints : bool; (* Can new constraints (elim or univ) be added *) }

type pre_variances = UVars.Variance.t option list option

type universe_decl =
  (QVar.t list, Sorts.ElimConstraints.t, Level.t list, pre_variances, Univ.UnivConstraints.t) gen_universe_decl

let default_univ_decl =
  { univdecl_qualities = [];
    (* in practice non named qualities will get collapsed for toplevel definitions,
       but side effects see named qualities from the surrounding definitions
       while using default_univ_decl *)
    univdecl_extensible_qualities = true;
    univdecl_elim_constraints = ElimConstraints.empty;
    univdecl_instance = [];
    univdecl_extensible_instance = true;
    univdecl_variances = None;
    univdecl_univ_constraints = UnivConstraints.empty;
    univdecl_extensible_constraints = true }

let univ_decl_csts decl =
  PConstraints.make decl.univdecl_elim_constraints decl.univdecl_univ_constraints

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
  let leftqs = List.fold_left (fun acc l -> QSet.remove l acc) qvars decl.univdecl_qualities in
  let leftus = List.fold_left (fun acc l -> Level.Set.remove l acc) levels decl.univdecl_instance in
  let () =
    let unboundqs = if decl.univdecl_extensible_qualities then QSet.empty else leftqs in
    let unboundus = if decl.univdecl_extensible_instance then Level.Set.empty else leftus in
    if not (QSet.is_empty unboundqs && Level.Set.is_empty unboundus)
    then error_unbound_universes unboundqs unboundus names
  in
  let leftqs = UContext.sort_qualities
      (Array.map_of_list (fun q -> Quality.QVar q) (QVar.Set.elements leftqs))
  in
  let leftus = UContext.sort_levels (Array.of_list (Level.Set.elements leftus)) in
  let instq = Array.append
      (Array.map_of_list (fun q -> QVar q) decl.univdecl_qualities)
      leftqs
  in
  let instu = Array.append (Array.of_list decl.univdecl_instance) leftus in
  let inst = LevelInstance.of_array (instq,instu) in
  inst

let check_universe_context_set ~prefix levels names =
  let left =
    List.fold_left (fun left l -> Level.Set.remove l left)
      levels prefix
  in
  if not (Level.Set.is_empty left)
  then error_unbound_universes QVar.Set.empty left names

let check_univ_implication uctx cstrs cstrs' =
  let gr = uctx.initial_universes in
  let grext, _ = merge_univ_constraints uctx cstrs gr in
  let cstrs' = UnivConstraints.filter (fun c -> not (UGraph.check_constraint grext c)) cstrs' in
  if UnivConstraints.is_empty cstrs' then ()
  else CErrors.user_err
      Pp.(str "Universe constraints are not implied by the ones declared: " ++
          UnivConstraints.pr (pr_uctx_level uctx) cstrs')

let check_elim_implication uctx cstrs cstrs' =
  let g = initial_elim_graph uctx in
  let grext = merge_elim_constraints ~src:Rigid uctx cstrs g in
  let cstrs' = ElimConstraints.filter (fun c -> not (QGraph.check_constraint grext c)) cstrs' in
  if ElimConstraints.is_empty cstrs' then ()
  else CErrors.user_err
      Pp.(str "Elimination constraints are not implied by the ones declared: " ++
          ElimConstraints.pr (quality_printer uctx) cstrs')

let check_implication uctx (elim_csts,univ_csts) (elim_csts',univ_csts') =
  check_univ_implication uctx univ_csts univ_csts';
  check_elim_implication uctx elim_csts elim_csts'

let check_template_univ_decl uctx ~template_qvars decl =
  let () =
    match List.filter (fun q -> not @@ QSet.mem q template_qvars) decl.univdecl_qualities with
    | (_ :: _) as qvars ->
      CErrors.user_err
        Pp.(str "Qualities " ++ prlist_with_sep spc (pr_uctx_qvar uctx) qvars ++
            str " cannot be template.")
    | [] ->
      if not (QVar.Set.equal template_qvars (QState.undefined uctx.sort_variables))
      then CErrors.anomaly Pp.(str "Bugged template univ declaration.")
  in
  (* XXX: when the kernel takes template entries closer to the polymorphic ones,
     we should perform some additional checks here. *)
  let () = assert (Sorts.ElimConstraints.is_empty decl.univdecl_elim_constraints) in
  let levels, csts = univ_context_set uctx in
  let () =
    let prefix = decl.univdecl_instance in
    if not decl.univdecl_extensible_instance
    then check_universe_context_set ~prefix levels uctx.names
  in
  if decl.univdecl_extensible_constraints then (levels, csts)
  else begin
    check_implication uctx (univ_decl_csts decl) (uctx.local, csts);
    levels, decl.univdecl_univ_constraints
  end

let check_mono_univ_decl uctx decl =
  (* Note: if [decl] is [default_univ_decl], behave like [uctx.local] *)
  let () =
    if not (List.is_empty decl.univdecl_qualities)
    || not (QSet.is_empty (QState.undefined uctx.sort_variables))
    then CErrors.user_err Pp.(str "Monomorphic declarations may not have sort variables.")
  in
  let levels, csts as ctx = univ_context_set uctx in
  let () =
    let prefix = decl.univdecl_instance in
    if not decl.univdecl_extensible_instance
    then check_universe_context_set ~prefix levels uctx.names
  in
  if decl.univdecl_extensible_constraints then check_mono_sort_constraints uctx
  else
    let () = assert (Sorts.ElimConstraints.is_empty uctx.local) in
    let () = check_implication uctx (univ_decl_csts decl) (uctx.local, csts) in
    levels, decl.univdecl_univ_constraints

let extend_variances inst variances =
  let open UVars in
  let _, ulen = LevelInstance.length inst in
  let variances = Array.of_list variances in
  let vlen = Array.length variances in
  if Int.equal vlen ulen then variances
  else if vlen > ulen then CErrors.user_err Pp.(str"More variance annotations than bound universes")
  else Array.append variances (Array.make (ulen - vlen) None)

let force_variance ~force_in_term ?(kind=PolyFlags.Definition) fv (VarianceOccurrence.{ in_binders = (binder_mode, occs); in_term; in_type; _ } as vocc) =
  let open VariancePair in
  let bindersv = Option.map (fun var -> { var with cumul_variance = Variance.sup var.cumul_variance fv }) binder_mode in
  let in_term =
    if force_in_term then Some { cumul_variance = Invariant;
      typing_variance = if kind == PolyFlags.Assumption then fv else Option.default Variance.Irrelevant (Option.map typing_variance in_term) }
    else Option.map (fun var -> { cumul_variance = Variance.sup var.cumul_variance fv; typing_variance = fv }) in_term
  in
  { vocc with in_binders = bindersv, occs; in_term; in_type = in_type }

let computed_variances cumulative kind ivariances inst =
  let inferred_variance level =
    match Level.Map.find_opt level ivariances with
    | None -> None
    | Some o ->
      let occ = InferCumulativity.forget_infer_variance_occurrence o in
      if cumulative then Some occ
      else Some (force_variance ~force_in_term:true ~kind Invariant occ)
  in
  let arr = Array.map inferred_variance (snd (LevelInstance.to_array inst)) in
  if not cumulative && Array.for_all Option.is_empty arr then None
  else
    let arr =
      Array.map (function None -> VarianceOccurrence.default_occ | Some v -> v) arr
    in Some (UVars.Variances.make arr)

let pr_pre_variances =
  let open Pp in
  let pr = pr_opt Variance.pr in
  prlist_with_sep spc pr

let check_variances ~cumulative ~kind names ivariances inst variances =
  debug Pp.(fun () -> str"Checking variance annotation with cumulative = " ++ bool cumulative);
  debug Pp.(fun () -> str"Checking variance annotation: " ++ Option.cata pr_pre_variances (str" no annotation") variances);
  debug Pp.(fun () -> str"Inferred variances: " ++ Option.cata (InferCumulativity.pr_variances Level.raw_pr) (str" no inferred variances") ivariances);
  let variances = Option.map (extend_variances inst) variances in
  match variances with
  | None -> (match ivariances with
    | None -> if cumulative then CErrors.anomaly Pp.(str"Variance was not inferred when checking universe declaration of cumulative definition") else None
    | Some ivariances -> computed_variances cumulative kind ivariances inst)
  | Some variances ->
    if not cumulative then
      CErrors.user_err
        Pp.(strbrk "Universe variance was specified but this definition will not be cumulative.")
    else
      match ivariances with
      | None -> CErrors.anomaly Pp.(str"Variance was not inferred when checking universe declaration of cumulative definition")
      | Some ivariances ->
        let check_var level variance =
          match Univ.Level.Map.find_opt level ivariances with
          | None -> CErrors.user_err Pp.(str"Variance annotation " ++ pr_opt UVars.Variance.pr variance ++ str" for unused universe binder " ++
            (pr_uctx_level_names names level))
          | Some iv ->
            debug Pp.(fun () -> str"Checking variance annotation: " ++ pr_opt UVars.Variance.pr variance ++ str " vs inferred variances " ++
              InferCumulativity.pr_variance_occurrence iv);
            let iv = InferCumulativity.forget_infer_variance_occurrence iv in
            match variance with
            | None -> iv
            | Some variance ->
              let ivariance = UVars.VarianceOccurrence.typing_variances iv in
              (* FIXME should we force only the cumulativity variance ? *)
              if UVars.Variance.le ivariance variance then force_variance ~force_in_term:false variance iv
              else CErrors.user_err Pp.(str"Variance annotation " ++ Variance.pr variance ++ str" for universe binder " ++
                (pr_uctx_level_names names level) ++ str" is incorrect, inferred variances are " ++
                  VarianceOccurrence.pr iv ++ str" and typing variance is hence " ++ Variance.pr ivariance)
        in
        Some (UVars.Variances.make (Array.map2 check_var (snd (LevelInstance.to_array inst)) variances))

let check_poly_univ_decl ~cumulative ~kind uctx decl =
  (* Note: if [decl] is [default_univ_decl], behave like [context uctx] *)
  let levels, (elim_csts, univ_csts) = context_set uctx in
  debug Pp.(fun () -> str"Checking universe declaration: cumulative = " ++ bool cumulative ++
    str", extensible instance? " ++ bool decl.univdecl_extensible_instance ++
    str", extensible constraints? " ++ bool decl.univdecl_extensible_constraints);
  let qvars = QState.undefined uctx.sort_variables in
  let inst = universe_context_inst decl qvars levels uctx.names in
  let nas = compute_instance_binders uctx inst in
  let univ_csts = if decl.univdecl_extensible_constraints then univ_csts
    else begin
      check_univ_implication uctx
        decl.univdecl_univ_constraints
        univ_csts;
      decl.univdecl_univ_constraints
    end
  in
  let elim_csts = if decl.univdecl_extensible_constraints then elim_csts
    else begin
      check_elim_implication uctx
        decl.univdecl_elim_constraints
        elim_csts;
      decl.univdecl_elim_constraints
    end
  in
  let variances = check_variances ~cumulative ~kind uctx.names uctx.variances inst decl.univdecl_variances in
  let uctx = UContext.make nas (inst, (elim_csts,univ_csts)) in
  uctx, variances

let check_univ_decl ~poly ~kind uctx decl =
  let (binders, _) = uctx.names in
  let entry =
    if PolyFlags.univ_poly poly then
      let uctx, variances = check_poly_univ_decl ~cumulative:(PolyFlags.cumulative poly) ~kind uctx decl in
      Polymorphic_entry (uctx, Option.map (fun v -> Entries.Check_variances v) variances)
    else
      if not (Option.is_empty decl.univdecl_variances) then
        CErrors.user_err
          Pp.(strbrk "Universe variance was specified but this definition will not be cumulative.")
      else Monomorphic_entry (check_mono_univ_decl uctx decl) in
  { universes_entry_universes = entry;
    universes_entry_binders = binders }

let merge_graph_context g (us, csts) =
  let g = Level.Set.fold (fun v g -> if Level.is_set v then g else
    UGraph.add_universe v ~strict:false ~rigid:false g) us g in
  UGraph.merge_constraints csts g

let restrict_universe_context (univs, univ_csts) keep =
  debug Pp.(fun () -> str"Restricting universe context set: "  ++ Univ.ContextSet.pr Level.raw_pr (univs, univ_csts) ++
    str " to " ++ Level.Set.pr Level.raw_pr keep);
  let removed = Level.Set.diff univs keep in
  if Level.Set.is_empty removed then univs, univ_csts
  else
  let allunivs = UnivConstraints.fold (fun (u,_,v) all ->
    Level.Set.union (Level.Set.union (Universe.levels u) (Universe.levels v)) all) univ_csts univs in
  let g = UGraph.initial_universes in
  let g, _equivs = merge_graph_context g (allunivs, univ_csts) in
  let allkept = Level.Set.union (UGraph.domain UGraph.initial_universes) (Level.Set.diff allunivs removed) in
  let univ_csts = UGraph.constraints_for ~kept:allkept g in
  let univ_csts = UnivConstraints.filter (fun (l,d,r) -> not (Universe.is_type0 l && d == Le)) univ_csts in
  let uctx = (Level.Set.inter univs keep, univ_csts) in
  (* debug Pp.(fun () -> str"Extras" ++ Level.Set.pr Level.raw_pr extras); *)
  debug Pp.(fun () -> str"Restricted universe context" ++ Univ.ContextSet.pr Level.raw_pr uctx);
  uctx

let restrict_uctx uctx keep =
  debug Pp.(fun () -> str"Restricting universe context: "  ++ pr ~local:true uctx ++
    str " to " ++ Level.Set.pr Level.raw_pr keep);
  let removed = Level.Set.diff uctx.local_variables keep in
  if Level.Set.is_empty removed then uctx
  else
    let universes = UGraph.remove removed uctx.universes in
    let uctx' = { uctx with local_variables = Level.Set.diff uctx.local_variables removed;
      flexible_variables = Level.Set.diff uctx.flexible_variables removed;
      variances = Option.map (fun v -> Level.Set.fold Level.Map.remove removed v) uctx.variances;
      minim_extra = UnivMinim.remove_from_extra removed uctx.minim_extra;
      universes } in
    debug Pp.(fun () -> str"Restricted universe context" ++ pr ~local:true uctx');
    uctx'

let restrict uctx vars =
  let vars =
    Id.Map.fold (fun id l vars -> Level.Set.add l vars) (snd (fst uctx.names)) vars
  in
  restrict_uctx uctx vars

let restrict_even_binders uctx vars = restrict_uctx uctx vars

let restrict_univ_constraints uctx csts =
  let levels = UGraph.variables ~local:true ~with_subst:false uctx.universes in
  merge_context_universes { uctx with universes = uctx.initial_universes } ~strict:false (levels, csts)

let restrict_elim_constraints ?src uctx csts =
  let elim_csts = uctx.local in
  let g = initial_elim_graph uctx in
  (* XXX we are wreaking havoc with elimination constraints *)
  let sort_variables = QState.set_elims g uctx.sort_variables in
  let sort_variables = QState.merge_constraints (fun cst -> merge_elim_constraints ?src uctx elim_csts cst) sort_variables in
  { uctx with local = csts; sort_variables }

type rigid =
  | UnivRigid
  | UnivFlexible

let univ_rigid = UnivRigid
let univ_flexible = UnivFlexible

(** ~sideff indicates that it is ok to redeclare a universe.
    Also merges the universe context in the local constraint structures
    and not only in the graph. *)
let merge_universe_context_set ?loc ~sideff rigid uctx uctx' =
  if Univ.ContextSet.is_empty uctx' then uctx
  else
    let () = debug Pp.(fun () -> str"merge (sideff: " ++ bool sideff ++ str"):  " ++ Univ.ContextSet.pr (pr_uctx_level uctx) uctx' ++
      str " in " ++ fnl () ++ pr ~local:true uctx) in
    let levels = Univ.ContextSet.levels uctx' in
    let declare g =
      Level.Set.fold (fun u g ->
          try UGraph.add_universe ~strict:false ~rigid:(rigid == UnivRigid) u g
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
    let universes = declare uctx.universes in
    let uctx = { uctx with local_variables = Level.Set.union levels uctx.local_variables } in
    let uctx =
      match rigid with
      | UnivRigid -> uctx
      | UnivFlexible ->
        assert (not sideff);
        let uvars' = Level.Set.union levels uctx.flexible_variables in
        { uctx with flexible_variables = uvars' }
    in
    let variances =
      match uctx.variances with
      | None -> None
      | Some variances ->
        let fold u variances =
          Level.Map.add u InferCumulativity.default_occ variances
        in
        Some (Level.Set.fold fold levels variances)
    in
    let cstrs' = Univ.ContextSet.constraints uctx' in
    let demoted_local_context =
      let dlevels, dcstrs = uctx.demoted_local_context in
       Level.Set.diff dlevels levels, (if sideff then UnivConstraints.union dcstrs cstrs' else dcstrs)
    in
    let uctx = { uctx with names; demoted_local_context; universes; variances; initial_universes = initial } in
    let uctx = merge_constraints uctx cstrs'
      (* with Loop_checking.Undeclared u ->
        CErrors.user_err Pp.(str"Undeclared universe " ++ Level.raw_pr u ++ str" during UState.merge" ++
          bool (UGraph.is_declared uctx.universes u)) in *)
    in
    let () = debug Pp.(fun () -> str"merge = " ++ pr ~local:true uctx) in
    uctx

let merge_sort_variables ?loc ?(sort_rigid=false) ?src ~sideff uctx (qvars, csts) =
  let sort_variables =
    QVar.Set.fold (fun qv qstate -> QState.add ~check_fresh:(not sideff) ~rigid:sort_rigid qv qstate)
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
  let sort_variables = QState.merge_constraints (merge_elim_constraints ?src uctx csts) sort_variables in
  let local = Sorts.ElimConstraints.union uctx.local csts in
  { uctx with local; sort_variables; names }

let merge_sort_context_set ?loc ?sort_rigid ?src ~sideff rigid uctx ((qvars, levels), (qcst, ucst) as ctx) =
  if UnivGen.is_empty_sort_context ctx then uctx else
  let uctx = merge_sort_variables ?loc ?sort_rigid ?src ~sideff uctx (qvars, qcst) in
  merge_universe_context_set ?loc ~sideff rigid uctx (levels, ucst)

let demote_global_univs (lvl_set, univ_csts) uctx =
  debug Pp.(fun () -> str"demote_global_univs:" ++ Univ.ContextSet.pr Level.raw_pr (lvl_set, univ_csts) ++ fnl () ++ str"From: " ++ pr ~local:false uctx);
  let local_variables = Level.Set.fold Level.Set.remove lvl_set uctx.local_variables in
  let flexible_variables = Level.Set.fold Level.Set.remove lvl_set uctx.flexible_variables in
  let update_ugraph g =
    let g = Level.Set.fold (fun u g ->
        try UGraph.add_universe u ~strict:true ~rigid:true g
        with UGraph.AlreadyDeclared -> g)
        lvl_set
        g
    in
    UGraph.merge_constraints univ_csts g
  in
  let initial_universes, _equivs = update_ugraph uctx.initial_universes in
  let universes, _equivs' = update_ugraph uctx.universes in
  let demoted_local_context =
    let lvls, cstrs = uctx.demoted_local_context in
    Level.Set.union lvl_set lvls, Univ.UnivConstraints.union cstrs univ_csts
  in
  { uctx with local_variables; demoted_local_context; flexible_variables; universes; initial_universes }

let demote_global_univ_entry entry uctx = match entry with
| Monomorphic_entry ucst ->
  demote_global_univs ucst uctx
| Polymorphic_entry _ -> uctx

(* Check bug_4363 bug_6323 bug_3539 and success/rewrite lemma l1
   for quick feedback when changing this code *)
let emit_side_effects eff u =
  let uctx = Safe_typing.universes_of_private eff in
  demote_global_univs uctx u

let merge_subst uctx subst =
  let universes, equivs = push_subst subst uctx.universes in
  let local_variables, flexible_variables, variances =
    update_univ_subst uctx.local_variables uctx.flexible_variables uctx.variances equivs
  in
  { uctx with universes; local_variables; flexible_variables; variances }

let merge_seff (uctx : t) (uctx' : t) =
  debug Pp.(fun () -> str"merge_seff: " ++ Level.Set.pr Level.raw_pr uctx'.local_variables ++ pr ~local:true uctx' ++
    str " in " ++ Level.Set.pr Level.raw_pr uctx.local_variables ++ pr ~local:true uctx);
  let (levels, constraints, subst) = UGraph.constraints_of_universes ~only_local:true uctx'.universes in
  (* Declare all levels: we are going to [set] the defined ones *)
  debug Pp.(fun () -> str"merge_seff constraints: " ++ UnivConstraints.pr Level.raw_pr constraints);
  let levels = Level.Set.union levels (Level.Map.domain subst) in
  let declare g =
    Level.Set.fold (fun u g ->
        try UGraph.add_universe ~strict:false ~rigid:(not (Level.Set.mem u uctx'.flexible_variables)) u g
        with UGraph.AlreadyDeclared -> g)
      levels g
  in
  let initial_universes = declare uctx.initial_universes in
  let universes = declare uctx.universes in
  let uctx = { uctx with universes; initial_universes;
    local_variables = Level.Set.union uctx.local_variables uctx'.local_variables;
    flexible_variables = Level.Set.union uctx.flexible_variables uctx'.flexible_variables; }
  in
  let uctx = merge_subst uctx subst in
  let uctx = merge_constraints uctx constraints in
  debug Pp.(fun () -> str"Merge result: " ++ pr ~local:true uctx);
  uctx

let update_sigma_univs uctx univs =
  let eunivs =
    { uctx with
      initial_universes = UGraph.set_local univs;
      universes = UGraph.set_local univs }
  in
  merge_seff eunivs uctx

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

let add_quality_variable ?loc ?(check_fresh=true) ~name ~rigid uctx q =
  let sort_variables = QState.add ~check_fresh ~rigid q uctx.sort_variables in
  let names = match name with
    | Some n -> add_qnames ?loc n q uctx.names
    | None -> add_qloc q loc uctx.names
  in
  { uctx with sort_variables; names }

let add_universe ?loc name ~strict ~rigid uctx u =
  let initial_universes = UGraph.add_universe ~strict ~rigid u uctx.initial_universes in
  let universes = UGraph.add_universe ~strict ~rigid u uctx.universes in
  let local_variables = Level.Set.add u uctx.local_variables in
  let variances = Option.map (Level.Map.add u InferCumulativity.default_occ) uctx.variances in
  let names =
    match name with
    | Some n -> add_names ?loc n u uctx.names
    | None -> add_loc u loc uctx.names
  in
  { uctx with names; local_variables; initial_universes; universes; variances }

let new_quality_variable ?loc ?(sort_rigid = false) ?name uctx =
  let q = UnivGen.fresh_sort_quality () in
  (* don't need to check_fresh as it's guaranteed new *)
  add_quality_variable ?loc ~name ~rigid:(sort_rigid || Option.has_some name) uctx q, q

let new_univ_level_variable ?loc ?(strict=false) rigid name uctx =
  let u = UnivGen.fresh_level () in
  let uctx =
    match rigid with
    | UnivRigid -> uctx
    | UnivFlexible ->
      let flexible_variables = Level.Set.add u uctx.flexible_variables in
      { uctx with flexible_variables }
  in
  let uctx = add_universe ?loc name ~strict ~rigid:(rigid == UnivRigid) uctx u in
  uctx, u

let add_forgotten_univ uctx u = add_universe None ~strict:true ~rigid:true uctx u

let from_env env =
  let universes = UGraph.set_local (Environ.universes env) in
  { empty with
    universes;
    initial_universes = universes;
    sort_variables = QState.of_elims (Environ.qualities env);
  }

let from_auctx env auctx =
  let ustate = from_env env in
  let names = AbstractContext.names auctx in
  let name_to_option = function Name id -> Some id | Anonymous -> None in
  (* Inlined call to [AbstractContext.repr] to know what qvars, levels and constraints to add *)
  let ustate = Array.fold_left_i (fun i ustate name -> add_quality_variable ~rigid:true ~name:(name_to_option name) ustate (QVar.make_var i)) ustate names.quals in
  let ustate = Array.fold_left_i (fun i ustate name -> add_universe (name_to_option name) ~strict:false ~rigid:true ustate (Level.var i)) ustate names.univs in
  let ustate = add_poly_constraints ustate (AbstractContext.constraints auctx) in
  ustate

let normalize_quality_variables uctx =
  let elim_cstrs = uctx.local in
  let elim_cstrs = QState.normalize_elim_constraints uctx.sort_variables elim_cstrs in
  { uctx with local = elim_cstrs }

let normalize_variables uctx =
  normalize_quality_variables uctx

let fix_undefined_variables ?vars uctx =
  match vars with
  | None -> { uctx with flexible_variables = Level.Set.empty }
  | Some vars -> { uctx with flexible_variables = Level.Set.diff uctx.flexible_variables vars }

let disable_universe_extension uctx ~with_cstrs =
  { uctx with fixed_rigid_universes = true; fixed_rigid_constraints = with_cstrs }

let collapse_sort_variables ?except ~only_above_prop uctx =
  let sorts = QState.collapse ?except ~only_above_prop uctx.sort_variables in
  normalize_quality_variables { uctx with sort_variables = sorts }

let get_variances uctx = uctx.variances
let set_variances uctx variances = { uctx with variances = Some variances }

let warn_no_variances =
  CWarnings.create ~name:"minimization-without-variances" ~category:CWarnings.CoreCategories.universes ~default:CWarnings.Enabled
    Pp.(fun () -> str"Calling minimization without variance information is a noop, see dev/doc/universes.md for an explanation.")

let update_variances_qvars qs variances =
  let upd vocc =
    match vocc.InferCumulativity.infer_under_impred_qvars with
    | None -> vocc
    | qvars ->
      let upd qv = Some (QState.repr qv qs) in
      { vocc with infer_under_impred_qvars = UVars.update_impred_qvars upd qvars }
  in
  Univ.Level.Map.Smart.map upd variances

let minimize
  ~partial ?(solve_term=false) uctx =
  let open UnivMinim in
  match uctx.variances with
  | None -> warn_no_variances (); uctx
  | Some variances ->
    let variances = update_variances_qvars uctx.sort_variables variances in
    let local_variables, flexible_variables, variances, universes =
      normalize_context_set ~solve_flexibles:uctx.fixed_rigid_universes
        ~solve_term
        ~variances ~partial uctx.universes
        ~local_variables:uctx.local_variables
        ~flexible_variables:uctx.flexible_variables
        ~binders:(fst uctx.names) uctx.minim_extra
    in
    { names = uctx.names;
      local = uctx.local;
      local_variables = local_variables;
      demoted_local_context = uctx.demoted_local_context;
      flexible_variables = flexible_variables;
      fixed_rigid_universes = uctx.fixed_rigid_universes;
      fixed_rigid_constraints = uctx.fixed_rigid_constraints;
      sort_variables = uctx.sort_variables;
      universes;
      initial_universes = uctx.initial_universes;
      variances = Some variances;
      minim_extra = UnivMinim.empty_extra; (* weak constraints are consumed *) }

let universe_context_inst_decl decl qvars levels names =
  let leftqs = List.fold_left (fun acc l -> QSet.remove l acc) qvars decl.univdecl_qualities in
  let leftus = List.fold_left (fun acc l -> Level.Set.remove l acc) levels decl.univdecl_instance in
  let () =
    let unboundqs = if decl.univdecl_extensible_qualities then QSet.empty else leftqs in
    let unboundus = if decl.univdecl_extensible_instance then Level.Set.empty else leftus in
    if not (QSet.is_empty unboundqs && Level.Set.is_empty unboundus)
    then error_unbound_universes unboundqs unboundus names
  in
  let instq = Array.map_of_list (fun q -> QVar q) decl.univdecl_qualities in
  let instu = Array.of_list decl.univdecl_instance in
  let inst = LevelInstance.of_array (instq,instu) in
  inst

let check_univ_decl_rev uctx decl =
  let levels, (elim_csts, univ_csts as csts) = context_set uctx in
  let qvars = QState.undefined uctx.sort_variables in
  let inst = universe_context_inst_decl decl qvars levels uctx.names in
  let nas = compute_instance_binders uctx inst in
  let () = check_implication uctx csts (univ_decl_csts decl)
  in
  let uctx = fix_undefined_variables uctx in
  let uctx, univ_csts =
    if decl.univdecl_extensible_constraints
    then uctx, univ_csts
    else restrict_univ_constraints uctx decl.univdecl_univ_constraints,
         univ_csts
  in
  let uctx, elim_csts =
    if decl.univdecl_extensible_constraints
    then uctx, elim_csts
    else restrict_elim_constraints ~src:Rigid uctx decl.univdecl_elim_constraints,
         elim_csts
  in
  let uctx' = UContext.make nas (inst, (elim_csts,univ_csts)) in
  uctx, uctx'

let check_uctx_impl ~fail uctx uctx' =
  let local = context_set uctx in
  let levels, (elim_csts,univ_csts) = context_set uctx' in
  let qvars_diff =
    QVar.Set.diff
      (QState.undefined uctx'.sort_variables)
      (QState.undefined uctx.sort_variables)
  in
  let levels_diff = Level.Set.diff levels (fst local) in
  let () = if not @@ (QVar.Set.is_empty qvars_diff && Level.Set.is_empty levels_diff) then
    error_unbound_universes qvars_diff levels_diff uctx'.names
  in
  let () =
    let grext = ugraph uctx in
    let cstrs' = UnivConstraints.filter (fun c -> not (UGraph.check_constraint grext c)) univ_csts in
    if UnivConstraints.is_empty cstrs' then ()
    else fail (UnivConstraints.pr (pr_uctx_level uctx) cstrs')
  in
  let () =
    let grext = elim_graph uctx in
    let cstrs' = ElimConstraints.filter (fun c -> not (QGraph.check_constraint grext c)) elim_csts in
    if ElimConstraints.is_empty cstrs' then ()
    else fail (ElimConstraints.pr (quality_printer uctx) cstrs')
  in
  ()


let disable_minim, _ = CDebug.create_full ~name:"minimization" ()

let minimize ~partial ?(solve_term=false) uctx =
  if CDebug.get_flag disable_minim then uctx
  else minimize ~partial ~solve_term uctx

module Internal =
struct

let reboot env uctx =
  debug Pp.(fun () -> str"rebooting");
  let uctx_global = from_env env in
  { uctx_global with flexible_variables = Level.Set.empty;
    sort_variables = uctx.sort_variables; }

end
