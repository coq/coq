(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open Univ
open Sorts
open Names
open Constr
open Declarations
open Environ

module RelDecl = Context.Rel.Declaration

module QGraph = struct

  open Sorts
  open Quality

  module QMap = QVar.Map
  module QSet = QVar.Set

  type t = {
    qmap: Quality.t option QMap.t;
    above_prop: QSet.t;
  }

  let empty = { qmap = QMap.empty; above_prop = QSet.empty }

  let rec repr q (qmap : t) = match QMap.find q qmap.qmap with
  | None -> QVar q
  | Some (QVar q) -> repr q qmap
  | Some (QConstant _ as q) -> q
  | exception Not_found ->
    let () = assert !Flags.in_debugger in
    QVar q

  let nf_quality m = function
  | QConstant _ as q -> q
  | QVar q -> repr q m

  let relevance q qmap =
    match repr q qmap with
    | QConstant QSProp -> Irrelevant
    | QConstant (QProp | QType) -> Relevant
    | QVar qv ->
      if QSet.mem qv qmap.above_prop then
        Relevant
      else RelevanceVar qv

  let nf_relevance m = function
  | Relevant | Irrelevant as q -> q
  | RelevanceVar q -> relevance q m

  let repr_var q qmap =
    match repr q qmap with
    | QVar q -> q
    | QConstant _ ->
        CErrors.anomaly Pp.(str "tried to set a qvar which is already set")

  let check_eq_qvar q1 q2 qmap =
    Quality.equal (repr q1 qmap) (repr q2 qmap)

  let check_constraint (q1, knd, q2) qmap =
    let open QConstraint in
    match knd, nf_quality qmap q1, nf_quality qmap q2 with
    | _, QConstant QType, QConstant QType
    | _, QConstant QProp, QConstant QProp
    | _, QConstant QSProp, QConstant QSProp -> true
    | _, QVar q, QVar q' when QVar.equal q q' -> true
    | Leq, QConstant QProp, QConstant QType -> true
    | Leq, QConstant QProp, QVar q when QSet.mem q qmap.above_prop -> true
    | Leq, QVar q, QConstant QType when QSet.mem q qmap.above_prop -> true
    | _ -> false

  let set q qv qmap =
    let q = repr_var q qmap in
    let q' = nf_quality qmap qv in
    match q' with
    | QVar qv when QVar.equal q qv -> qmap
    | QVar qv ->
      let above_prop = if QSet.mem q qmap.above_prop then QSet.add qv @@ QSet.remove q qmap.above_prop else qmap.above_prop in
      { qmap = QMap.add q (Some q') qmap.qmap; above_prop }
    | QConstant _ ->
      { qmap with qmap = QMap.add q (Some q') qmap.qmap }

  let unify_quality cv_pb q1 q2 qmap =
    let open QConstraint in
    match cv_pb, nf_quality qmap q1, nf_quality qmap q2 with
    | _, QConstant QType, QConstant QType
    | _, QConstant QProp, QConstant QProp
    | _, QConstant QSProp, QConstant QSProp -> qmap, false
    | Leq, QConstant QProp, QConstant QType -> qmap, false
    | _, QConstant (QProp | QSProp | QType), QConstant (QProp | QSProp | QType) ->
        CErrors.anomaly Pp.(str "tried to unify ununifiable qualities")
    | Equal, QVar qv, q
    | Equal, q, QVar qv -> set qv q qmap, false
    | _, QVar q, (QConstant (QProp | QSProp) as qv)
    | _, (QConstant (QSProp | QType) as qv), QVar q ->
      (* The only cases where leq implies eq *)
      set q qv qmap, false
    | Leq, QVar _, QVar _ -> qmap, true
    | Leq, QVar q, QConstant QType
    | Leq, QConstant QProp, QVar q -> { qmap with above_prop = QSet.add q qmap.above_prop }, true

  let merge_qconstraints qcstrs qmap =
    let pre, post = List.partition
      (function (_, QConstraint.Equal, _) | (QConstant (QSProp | QType), _, _) | (_, _, QConstant (QProp | QSProp)) -> true
        | _ -> false) (QConstraints.elements qcstrs)
    in
    let qmap, pre' = List.fold_filter (fun qmap (q1, pb, q2) -> unify_quality pb q1 q2 qmap) qmap pre in
    let qmap, post' = List.fold_filter (fun qmap (q1, pb, q2) -> unify_quality pb q1 q2 qmap) qmap post in
    qmap, List.fold_left (fun s c -> QConstraints.add c s) QConstraints.empty (pre' @ post')

  let add_quality qv (qmap : t) : t = { qmap with qmap = QMap.add qv None qmap.qmap }


  let to_qconstraints qmap =
    let qcstrs = QConstraints.empty in
    let qcstrs = QMap.fold (fun q qo' qcstrs -> match qo' with Some q' -> QConstraints.add QConstraint.(QVar q, Equal, q') qcstrs | None -> qcstrs) qmap.qmap qcstrs in
    let qcstrs = QSet.fold (fun q qcstrs -> QConstraints.add QConstraint.(QConstant QProp, Leq, QVar q) qcstrs) qmap.above_prop qcstrs in
    qcstrs


  let to_pair qmap =
    (QMap.filter_map (fun _ q -> q) qmap.qmap, qmap.above_prop)

  let of_pair qualities (qgraph, above_prop) =
    let qmap = QMap.merge (fun _ u q -> if u = None then assert false else Some q) qualities qgraph in
    let () = QSet.iter (fun q -> if QMap.find q qmap <> None then assert false) above_prop in
    { qmap; above_prop }


end

open Conversion

type eq_cmp = LEQ | EQ | GEQ

type extra_env = {
  evar_list: Evar.t list; (* Context style, later evars may depend on earlier ones *)
  evar_map : (rel_context * types * relevance * Name.t) Evar.Map.t;
  qualities : bool QVar.Map.t;
  univs : bool Level.Map.t;
  evar_candidates : (eq_cmp * constr) list Evar.Map.t;
  equalities: (Sorts.relevance Range.t * QVar.t * constr * conv_pb * constr) list;
  qcstrs: QConstraints.t;
  ucstrs: (Quality.t * Universe.t * conv_pb * Universe.t) list;
  qgraph : QGraph.t;
  ulcstrs: Constraints.t;
  pattern_relevances: QVar.Set.t;
}

module ExtraEnv = struct

let sigma_of evd =
  let evar_types (evk, args) =
    match Evar.Map.find_opt evk evd.evar_map with
    | Some (_, ty, _, _) ->
        let args = args |> SList.to_list |> List.mapi (fun i t -> Option.default (mkRel (i+1)) t) in
        Vars.substl args ty
    | None -> assert false
  in
  { Typeops.evar_types;
    under_typing = true; }

let empty = {
  evar_list = [];
  evar_map = Evar.Map.empty;
  qualities = QVar.Map.empty;
  univs = Level.Map.empty;
  evar_candidates = Evar.Map.empty;
  equalities = [];
  qcstrs = QConstraints.empty;
  ucstrs = [];
  qgraph = QGraph.empty;
  ulcstrs = Constraints.empty;
  pattern_relevances = QVar.Set.empty;
}

let add_evar evk ctx ty rel pat evd =
  { evd with
    evar_list = evk :: evd.evar_list;
    evar_map = Evar.Map.add evk (ctx, ty, rel, pat) evd.evar_map;
    evar_candidates = Evar.Map.add evk [] evd.evar_candidates }


let define_evar ev cmp t evd =
  let evar_candidates = Evar.Map.update ev (function Some l -> Some ((cmp, t) :: l) | None -> None) evd.evar_candidates in
  { evd with evar_candidates }

let add_pattern_relevance r evd =
  match r with
  | Relevant -> evd
  | RelevanceVar q ->
    { evd with pattern_relevances = QVar.Set.add q evd.pattern_relevances }
  | Irrelevant -> CErrors.anomaly Pp.(str "Irrelevant subpattern in rewrite rules")

let add_quality q ~bound evd =
  assert (not @@ QVar.Map.mem q evd.qualities);
  { evd with qualities = QVar.Map.add q bound evd.qualities; qgraph = QGraph.add_quality q evd.qgraph }

let add_universe u ~bound evd =
  assert (not @@ Level.Map.mem u evd.univs);
  { evd with univs = Level.Map.add u bound evd.univs }

let enforce_cmp_quality cv_pb q1 q2 evd =
  let cv_pb = match cv_pb with CONV -> QConstraint.Equal | CUMUL -> QConstraint.Leq in
  let qgraph, b = QGraph.unify_quality cv_pb q1 q2 evd.qgraph in
  let qcstrs = if b then QConstraints.add (q1, cv_pb, q2) evd.qcstrs else evd.qcstrs in
  { evd with qgraph; qcstrs }

let enforce_cmp_universe cv_pb q u1 u2 evd =
  { evd with ucstrs = (q, u1, cv_pb, u2) :: evd.ucstrs }

let get_algebraic = function
| Prop | SProp -> Universe.type0
| QSort (_, u) -> u
| Set -> Universe.type0
| Type u -> u

let enforce_cmp_sort cv_pb s1 s2 evd =
  match s1, s2 with
  | SProp, SProp | Prop, Prop | Set, Set -> evd
  | Prop, (Set | Type _) when cv_pb = CUMUL -> evd
  | (Prop | Set | Type _ as s1), (Prop | SProp as s2)
  | (Prop | SProp as s1), (Prop | Set | Type _ as s2) ->
    raise (UGraph.UniverseInconsistency (None, ((match cv_pb with CONV -> Eq | CUMUL -> Le), s1, s2, None)))
  | (Set | Type _), (Set | Type _) ->
    enforce_cmp_universe cv_pb Quality.(QConstant QType) (get_algebraic s1) (get_algebraic s2) evd
  | QSort (q, u), s ->
    let evd = enforce_cmp_quality cv_pb (Quality.QVar q) (Sorts.quality s) evd in
    enforce_cmp_universe cv_pb (Quality.QVar q) u (get_algebraic s) evd
  | s, QSort (q, u) ->
    let evd = enforce_cmp_quality cv_pb (Sorts.quality s) (Quality.QVar q) evd in
    enforce_cmp_universe cv_pb (Sorts.quality s) (get_algebraic s) u evd

let enforce_constraint evd cstr =
  { evd with ulcstrs = Constraints.add cstr evd.ulcstrs }

let enforce_constraints evd cstrs =
  { evd with ulcstrs = Constraints.union evd.ulcstrs cstrs }


let enforce_super_level s u evd =
  let evd = enforce_constraint evd (Level.set, Lt, u) in (* Common case *)
  enforce_cmp_universe CUMUL (Sorts.quality s) (Universe.super (get_algebraic s)) (Universe.make u) evd

let enforce_product_level env s s' u evd =
  let evd = enforce_cmp_universe CUMUL (Sorts.quality s') (get_algebraic s') (Universe.make u) evd in
  match s' with
  | SProp | Prop -> evd
  | Set when Environ.is_impredicative_set env -> evd
  | QSort _ when Environ.is_impredicative_set env -> evd (* QType may still be impredicative Set *)
  | Set | Type _ | QSort _ ->
    enforce_cmp_universe CUMUL (Sorts.quality s') (get_algebraic s) (Universe.make u) evd


let compare_instances u1 u2 evd =
  let (qcstrs, ulcstrs) = UVars.enforce_eq_instances u1 u2 (QConstraints.empty, evd.ulcstrs) in
  let qgraph, qcstrs = QGraph.merge_qconstraints qcstrs evd.qgraph in
  { evd with qgraph; ulcstrs; qcstrs = QConstraints.union qcstrs evd.qcstrs }

let compare_cumul_instances cv_pb variance u u' evd =
  let qucstrs = QConstraints.empty, evd.ulcstrs in
  let (qcstrs, ulcstrs) = match cv_pb with
    | CONV ->
      UVars.enforce_eq_variance_instances variance u u' qucstrs
    | CUMUL ->
      UVars.enforce_leq_variance_instances variance u u' qucstrs
  in
  let qgraph, qcstrs = QGraph.merge_qconstraints qcstrs evd.qgraph in
  { evd with qgraph; ulcstrs; qcstrs = QConstraints.union qcstrs evd.qcstrs }


let enforce_equality_relevancevar rels q cv_pb t1 t2 evd =
  { evd with equalities = (rels, q, t1, cv_pb, t2) :: evd.equalities }

end

type conv_tab = {
  cnv_inf : CClosure.clos_infos;
  lft_tab : CClosure.clos_tab;
  rgt_tab : CClosure.clos_tab;
}
(** Invariant: for any tl ∈ lft_tab and tr ∈ rgt_tab, there is no mutable memory
    location contained both in tl and in tr. *)

(** The same heap separation invariant must hold for the fconstr arguments
    passed to each respective side of the conversion function below. *)

open CClosure
open Esubst

exception MustExpand
exception NotConvertible

type conv_pb = Conversion.conv_pb = CONV | CUMUL



let push_relevance infos r =
  { infos with cnv_inf = CClosure.push_relevance infos.cnv_inf r }

let push_relevances infos nas =
  { infos with cnv_inf = CClosure.push_relevances infos.cnv_inf nas }


let inductive_cumulativity_arguments (mind,ind) =
  mind.mind_nparams +
  mind.mind_packets.(ind).mind_nrealargs

let convert_inductives cv_pb (mind, ind) nargs u1 u2 s =
  match mind.mind_variance with
  | None -> ExtraEnv.compare_instances u1 u2 s
  | Some variances ->
    let num_param_arity = inductive_cumulativity_arguments (mind,ind) in
    if not (Int.equal num_param_arity nargs) then
      (* shortcut, not sure if worth doing, could use perf data *)
      if UVars.Instance.equal u1 u2 then s else raise MustExpand
    else
      ExtraEnv.compare_cumul_instances cv_pb variances u1 u2 s

let constructor_cumulativity_arguments (mind, ind, ctor) =
  mind.mind_nparams +
  mind.mind_packets.(ind).mind_consnrealargs.(ctor - 1)

let convert_constructors (mind, ind, cns) nargs u1 u2 s =
  match mind.mind_variance with
  | None -> ExtraEnv.compare_instances u1 u2 s
  | Some _ ->
    let num_cnstr_args = constructor_cumulativity_arguments (mind, ind, cns) in
    if not (Int.equal num_cnstr_args nargs) then
      if UVars.Instance.equal u1 u2 then s else raise MustExpand
    else
      s


let esubst_of_rel_context_instance_list ctx u args e =
  let open Context.Rel.Declaration in
  let rec aux e args ctx = match ctx with
  | [] -> e
  | LocalAssum _ :: ctx -> aux (usubs_lift e) (usubs_lift args) ctx
  | LocalDef (_, c, _) :: ctx ->
    let c = Vars.subst_instance_constr u c in
    let c = mk_clos args c in
    aux (usubs_cons c e) (usubs_cons c args) ctx
  in
  aux e args (List.rev ctx)

let identity_of_ctx (ctx : Constr.rel_context) =
  Context.Rel.instance mkRel 0 ctx

let eta_expand_ind env (ind,u as pind) =
  let mib = Environ.lookup_mind (fst ind) env in
  let mip = mib.mind_packets.(snd ind) in
  let ctx = Vars.subst_instance_context u mip.mind_arity_ctxt in
  let args = identity_of_ctx ctx in
  let c = mkApp (mkIndU pind, args) in
  let c = Term.it_mkLambda_or_LetIn c ctx in
  inject c

let eta_expand_constructor env ((ind,ctor),u as pctor) =
  let mib = Environ.lookup_mind (fst ind) env in
  let mip = mib.mind_packets.(snd ind) in
  let ctx = Vars.subst_instance_context u (fst mip.mind_nf_lc.(ctor-1)) in
  let args = identity_of_ctx ctx in
  let c = mkApp (mkConstructU pctor, args) in
  let c = Term.it_mkLambda_or_LetIn c ctx in
  inject c


let is_frel_inst e inst = List.for_all_i CClosure.(fun i arg -> fterm_of @@ mk_clos e arg = FRel i) 1 inst

let cmp_of_pb = function CUMUL -> GEQ | CONV -> EQ
let cmp_of_pb_r : _ -> eq_cmp = function CUMUL -> LEQ | CONV -> EQ

let rec fterm_relevance infos evd lft c =
  let open Relevanceops in
  QGraph.nf_relevance evd.qgraph @@
  match fterm_of c with
  | FEvar (evk, _, _, _) -> let (_, _, rel, _) = Evar.Map.find evk evd.evar_map in rel
  | FRel n -> Range.get (info_relevances infos) (n - 1)
  | FAtom _ -> Relevant (* Sorts *)
  | FInd _ | FProd _ -> Relevant
  | FFlex (RelKey n) -> Range.get (info_relevances infos) (reloc_rel n lft - 1)
  | FFlex (VarKey v) -> relevance_of_var (info_env infos) v
  | FFlex (ConstKey cst) -> relevance_of_constant (info_env infos) cst
  | FConstruct cstr -> relevance_of_constructor (info_env infos) cstr
  | FApp (hd, _) -> fterm_relevance infos evd lft hd
  | FLambda _ -> Relevant
    (* We can't tell yet, but the congruence is fine thanks to the shared type *)
  | FProj (_, r, _) -> r
  | FFix (((_, i), (nas, _, _)), e)
  | FCoFix ((i, (nas, _, _)), e) -> usubst_relevance e nas.(i).Context.binder_relevance
  | FCaseT (_, _, _, (_, r), _, _, e)
  | FCaseInvert (_, _, _, (_, r), _, _, _, e) -> usubst_relevance e r
  | FLIFT (n, f) -> fterm_relevance infos evd (el_shft n lft) f
  | FLetIn _ ->
    CErrors.anomaly Pp.(str "is_fterm_irrelevant called on non-whnf term")
  | FInt _ | FFloat _ | FString _ | FArray (_, _, _) -> Relevant
  | FIrrelevant -> Irrelevant (* Should never be reached *)
  | FLOCKED | FCLOS _ -> CErrors.anomaly Pp.(str "is_fterm_irrelevant called on improper fterm")


let rec strip_flift lft t =
  match fterm_of t with
  | FLIFT (n, c) -> strip_flift (el_shft n lft) c
  | _ -> lft, t

type elim_context = Elim of int option [@@unboxed]
exception FailElim
let elim_napp (Elim e) = Option.default 0 e
let in_elim (Elim e) = Option.has_some e

let rec _unify cv_pb infos ?(elim=Elim None) lft1 t1 lft2 t2 evd =
  let t1 = whd_fterm infos.cnv_inf infos.lft_tab t1 in
  let t2 = whd_fterm infos.cnv_inf infos.rgt_tab t2 in
  let lft1, t1 = strip_flift lft1 t1 in
  let lft2, t2 = strip_flift lft2 t2 in
  match fterm_relevance infos.cnv_inf evd lft1 t1, fterm_relevance infos.cnv_inf evd lft2 t2 with
  | Irrelevant, Irrelevant -> evd
  | RelevanceVar q, RelevanceVar q' when QGraph.check_eq_qvar q q' evd.qgraph ->
      ExtraEnv.enforce_equality_relevancevar (CClosure.info_relevances infos.cnv_inf) q cv_pb (term_of_fconstr t1) (term_of_fconstr t2) evd
  | RelevanceVar _, _ | _, RelevanceVar _ ->
      CErrors.anomaly Pp.(str "tried to compare two terms with different relevances")
  | Relevant, Irrelevant | Irrelevant, Relevant ->
      CErrors.anomaly Pp.(str "tried to compare two terms with different relevances")
  | Relevant, Relevant ->
  match fterm_of t1, fterm_of t2 with
  | FEvar (ev, args, e, _), FEvar (ev', args', e', _) ->
    if in_elim elim then raise FailElim else
    let evd =
      if is_frel_inst e args then
        ExtraEnv.define_evar ev (cmp_of_pb cv_pb) (term_of_fconstr t2) evd
      else evd
    in
    if is_frel_inst e' args' then
      ExtraEnv.define_evar ev' (cmp_of_pb_r cv_pb) (term_of_fconstr t1) evd
    else evd

  | FEvar (ev, args, e, _), _ ->
    if in_elim elim then raise FailElim else
    if is_frel_inst e args then
      ExtraEnv.define_evar ev (cmp_of_pb cv_pb) (term_of_fconstr t2) evd
    else evd

  | _, FEvar (ev, args, e, _) ->
    if in_elim elim then raise FailElim else
    if is_frel_inst e args then
      ExtraEnv.define_evar ev (cmp_of_pb_r cv_pb) (term_of_fconstr t1) evd
    else evd

  (* case of leaves *)
  | FAtom a1, FAtom a2 ->
    begin match kind a1, kind a2 with
    | Sort s1, Sort s2 ->
      ExtraEnv.enforce_cmp_sort cv_pb s1 s2 evd
    | Meta n, Meta m when n = m -> evd
    | _ -> raise NotConvertible
    end

  (* 2 index known to be bound to no constant *)
  | FRel n, FRel m ->
      if n = m then
        evd
      else
        raise NotConvertible

  (* Inductive types:  MutInd MutConstruct Fix Cofix *)
  | FInd (ind1, u1 as pind1), FInd (ind2, u2 as pind2) ->
    if not (Ind.CanOrd.equal ind1 ind2) then
      raise NotConvertible
    else if UVars.Instance.is_empty u1 || UVars.Instance.is_empty u2 then
      ExtraEnv.compare_instances u1 u2 evd
    else
      let mind = Environ.lookup_mind (fst ind1) (info_env infos.cnv_inf) in
      begin match convert_inductives cv_pb (mind, snd ind1) (elim_napp elim) u1 u2 evd with
      | evd -> evd
      | exception MustExpand ->
        let env = info_env infos.cnv_inf in
        let t1 = eta_expand_ind env pind1 in
        let t2 = eta_expand_ind env pind2 in
        unify cv_pb infos lft1 t1 lft2 t2 evd
      end

  | FConstruct ((ind1, j1), u1 as pctor1), FConstruct ((ind2, j2), u2 as pctor2) ->
    if not (Int.equal j1 j2 && Ind.CanOrd.equal ind1 ind2) then
      raise NotConvertible
    else if UVars.Instance.is_empty u1 || UVars.Instance.is_empty u2 then
      ExtraEnv.compare_instances u1 u2 evd
    else
      let mind = Environ.lookup_mind (fst ind1) (info_env infos.cnv_inf) in
      begin match convert_constructors (mind, snd ind1, j1) (elim_napp elim) u1 u2 evd with
      | evd -> evd
      | exception MustExpand ->
        let env = info_env infos.cnv_inf in
        let t1 = eta_expand_constructor env pctor1 in
        let t2 = eta_expand_constructor env pctor2 in
        unify cv_pb infos lft1 t1 lft2 t2 evd
      end

  | FProj (p1, r1, c1), FProj (p2, r2, c2) ->
    if is_irrelevant infos.cnv_inf r1 && is_irrelevant infos.cnv_inf r2 then
      evd
    else if Projection.Repr.CanOrd.equal (Projection.repr p1) (Projection.repr p2) then
      unify CONV infos ~elim:(Elim (Some 0)) lft1 c1 lft2 c2 evd
    else raise NotConvertible

  | FProd (na, dom1, codom1, e1), FProd (_, dom2, codom2, e2) ->
      let evd = unify CONV infos lft1 dom1 lft2 dom2 evd in
      let na = usubst_binder e1 na in
      unify cv_pb (push_relevance infos na) lft1 (mk_clos (usubs_lift e1) codom1) lft2 (mk_clos (usubs_lift e2) codom2) evd

  (* other constructors *)
  | FLambda _, FLambda _ ->
    let (na, ty1, bd1) = destFLambda mk_clos t1 in
    let (_,  ty2, bd2) = destFLambda mk_clos t2 in
    let evd = unify CONV infos lft1 ty1 lft2 ty2 evd in
    unify CONV (push_relevance infos na) (el_lift lft1) bd1 (el_lift lft2) bd2 evd

  (* Eta-expansion on the fly *)
  | FLambda _, _ ->
    let (na, _, bd1) = destFLambda mk_clos t1 in
    let t2 = eta_expand_fterm t2 in
    unify CONV (push_relevance infos na) (el_lift lft1) bd1 (el_lift lft2) t2 evd

  | _, FLambda _ ->
    let (na, _, bd2) = destFLambda mk_clos t2 in
    let t1 = eta_expand_fterm t1 in
    unify CONV (push_relevance infos na) (el_lift lft1) t1 (el_lift lft2) bd2 evd

  | FFix (((op1, i1), (na1, tys1, cl1)), e1), FFix (((op2, i2), (_, tys2, cl2)), e2) ->
    if not (Int.equal i1 i2 && Array.equal Int.equal op1 op2) then
      raise NotConvertible;

    let n = Array.length cl1 in
    let fty1 = Array.map (mk_clos e1) tys1 in
    let fty2 = Array.map (mk_clos e2) tys2 in
    let fcl1 = Array.map (mk_clos (usubs_liftn n e1)) cl1 in
    let fcl2 = Array.map (mk_clos (usubs_liftn n e2)) cl2 in
    let evd = Array.fold_left2 (fun evd t1 t2 -> unify CONV infos lft1 t1 lft2 t2 evd) evd fty1 fty2 in
    let evd =
      let na1 = Array.map (usubst_binder e1) na1 in
      let infos = push_relevances infos na1 in
      let lft1 = el_liftn n lft1 and lft2 = el_liftn n lft2 in
      Array.fold_left2 (fun evd t1 t2 -> unify CONV infos lft1 t1 lft2 t2 evd) evd fcl1 fcl2
    in
    evd

  | FCoFix ((op1, (na1, tys1, cl1)), e1), FCoFix ((op2, (_, tys2, cl2)), e2) ->
    if not (Int.equal op1 op2) then
      raise NotConvertible;

    let n = Array.length cl1 in
    let fty1 = Array.map (mk_clos e1) tys1 in
    let fty2 = Array.map (mk_clos e2) tys2 in
    let fcl1 = Array.map (mk_clos (usubs_liftn n e1)) cl1 in
    let fcl2 = Array.map (mk_clos (usubs_liftn n e2)) cl2 in
    let evd = Array.fold_left2 (fun evd t1 t2 -> unify CONV infos lft1 t1 lft2 t2 evd) evd fty1 fty2 in
    let evd =
      let na1 = Array.map (usubst_binder e1) na1 in
      let infos = push_relevances infos na1 in
      let lft1 = el_liftn n lft1 and lft2 = el_liftn n lft2 in
      Array.fold_left2 (fun evd t1 t2 -> unify CONV infos lft1 t1 lft2 t2 evd) evd fcl1 fcl2
    in
    evd

  | FInt i1, FInt i2 ->
      if Uint63.equal i1 i2 then evd
      else raise NotConvertible

  | FFloat f1, FFloat f2 ->
      if Float64.equal f1 f2 then evd
      else raise NotConvertible

  | FString s1, FString s2 ->
    if Pstring.equal s1 s2 then evd
    else raise NotConvertible

  | FArray (u1, t1, ty1), FArray (u2, t2, ty2) ->
    let len = Parray.length_int t1 in
    if not (Int.equal len (Parray.length_int t2)) then raise NotConvertible;
    let evd = ExtraEnv.compare_cumul_instances CONV [|UVars.Variance.Irrelevant|] u1 u2 evd in
    let evd = unify CONV infos lft1 ty1 lft2 ty2 evd in
    let evd = Parray.fold_left2 (fun u v1 v2 -> unify CONV infos lft1 v1 lft2 v2 u) evd t1 t2 in
    evd

  | FCaseT (ci1, u1, pms1, p1, c1, br1, e1), FCaseT (ci2, u2, pms2, p2, c2, br2, e2) ->
    if not (Ind.CanOrd.equal ci1.ci_ind ci2.ci_ind) then
      raise NotConvertible;

    (** FIXME: cache the presence of let-bindings in the case_info *)
    let mind = Environ.lookup_mind (fst ci1.ci_ind) (info_env infos.cnv_inf) in
    let mip = mind.mind_packets.(snd ci1.ci_ind) in
    let evd =
      let ind = (mind, snd ci1.ci_ind) in
      let nargs = inductive_cumulativity_arguments ind in
      let u1 = CClosure.usubst_instance e1 u1 in
      let u2 = CClosure.usubst_instance e2 u2 in
      convert_inductives CONV ind nargs u1 u2 evd
    in
    let evd = unify CONV infos ~elim:(Elim (Some 0)) lft1 c1 lft2 c2 evd in
    let pms1 = mk_clos_vect e1 pms1 in
    let pms2 = mk_clos_vect e2 pms2 in
    let evd = Array.fold_left2 (fun u v1 v2 -> unify CONV infos lft1 v1 lft2 v2 u) evd pms1 pms2 in
    let evd = convert_return_clause mind mip infos e1 e2 lft1 lft2 u1 u2 pms1 pms2 p1 p2 evd in
    convert_branches mind mip infos e1 e2 lft1 lft2 u1 u2 pms1 pms2 br1 br2 evd

  | FCaseInvert (ci1, u1, pms1, p1, iv1, _, br1, e1), FCaseInvert (ci2, u2, pms2, p2, iv2, _, br2, e2) ->
    if not (Ind.CanOrd.equal ci1.ci_ind ci2.ci_ind) then
      raise NotConvertible;

    (** FIXME: cache the presence of let-bindings in the case_info *)
    let mind = Environ.lookup_mind (fst ci1.ci_ind) (info_env infos.cnv_inf) in
    let mip = mind.mind_packets.(snd ci1.ci_ind) in
    let evd =
      let ind = (mind, snd ci1.ci_ind) in
      let nargs = inductive_cumulativity_arguments ind in
      let u1 = CClosure.usubst_instance e1 u1 in
      let u2 = CClosure.usubst_instance e2 u2 in
      convert_inductives CONV ind nargs u1 u2 evd
    in
    let pms1 = mk_clos_vect e1 pms1 in
    let pms2 = mk_clos_vect e2 pms2 in
    let evd = Array.fold_left2 (fun u v1 v2 -> unify CONV infos lft1 v1 lft2 v2 u) evd pms1 pms2 in
    let evd = Array.fold_left2 (fun u v1 v2 -> unify CONV infos lft1 v1 lft2 v2 u) evd (get_invert iv1) (get_invert iv2) in
    let evd = convert_return_clause mind mip infos e1 e2 lft1 lft2 u1 u2 pms1 pms2 p1 p2 evd in
    convert_branches mind mip infos e1 e2 lft1 lft2 u1 u2 pms1 pms2 br1 br2 evd

  (* 2 constants, 2 local defined vars or 2 defined rels *)
  | FFlex _, _ | _, FFlex _ -> raise FailElim

  | FApp (hd1, args1), FApp (hd2, args2) ->
    let nargs1 = Array.length args1 in
    let nargs2 = Array.length args2 in
    let lft_hd1, hd1 = strip_flift lft1 hd1 in
    let lft_hd2, hd2 = strip_flift lft2 hd2 in
    begin match fterm_of hd1, fterm_of hd2 with
    | FConstruct _, FConstruct _ ->
        if nargs1 != nargs2 then raise NotConvertible;
        let evd = unify cv_pb infos ~elim:(Elim (Some nargs1)) lft_hd1 hd1 lft_hd2 hd2 evd in
        Array.fold_left2 (fun u v1 v2 -> unify CONV infos lft1 v1 lft2 v2 u) evd args1 args2

    (* Eta expansion of records *)
    | FConstruct ((ind1, _), u1), _ ->
      begin match eta_expand_ind_fterm (info_env infos.cnv_inf) (ind1, u1) args1 t2 with
      | args1, args2 -> Array.fold_left2 (fun u v1 v2 -> unify CONV infos lft1 v1 lft2 v2 u) evd args1 args2
      | exception Not_found -> raise NotConvertible
      end

    | _, FConstruct ((ind2, _), u2) ->
      begin match eta_expand_ind_fterm (info_env infos.cnv_inf) (ind2, u2) args2 t1 with
      | args2, args1 -> Array.fold_left2 (fun u v1 v2 -> unify CONV infos lft1 v1 lft2 v2 u) evd args1 args2
      | exception Not_found -> raise NotConvertible
      end

    | FFix (((op1, i1), _), _), FFix (((op2, i2), _), _) ->
      if not (Int.equal i1 i2 && Array.equal Int.equal op1 op2) then
        raise NotConvertible;
      let index = op1.(i1) in
      let evd = unify cv_pb infos ~elim:(Elim (Some 0)) lft1 args1.(index) lft2 args2.(index) evd in
      let evd = unify cv_pb infos lft_hd1 hd1 lft_hd2 hd2 evd in
      Array.fold_left2_i (fun i u v1 v2 -> if i = index then u else unify CONV infos lft1 v1 lft2 v2 u) evd args1 args2

    | _ ->
      if nargs1 != nargs2 then raise NotConvertible;
      let evd = unify cv_pb infos ~elim:(Elim (Some nargs1)) lft_hd1 hd1 lft_hd2 hd2 evd in
      Array.fold_left2 (fun u v1 v2 -> unify CONV infos lft1 v1 lft2 v2 u) evd args1 args2
    end

  | FApp (hd1, args1), _ ->
    let _, hd1 = strip_flift lft1 hd1 in
    begin match fterm_of hd1 with
    (* Eta expansion of records *)
    | FConstruct ((ind1, _), u1) ->
      begin match eta_expand_ind_fterm (info_env infos.cnv_inf) (ind1, u1) args1 t2 with
      | args1, args2 -> Array.fold_left2 (fun u v1 v2 -> unify CONV infos lft1 v1 lft2 v2 u) evd args1 args2
      | exception Not_found -> raise NotConvertible
      end

    | _ -> raise NotConvertible
    end

  | _, FApp (hd2, args2) ->
    let _, hd2 = strip_flift lft1 hd2 in
    begin match fterm_of hd2 with
    (* Eta expansion of records *)
    | FConstruct ((ind, _), u) ->
      begin match eta_expand_ind_fterm (info_env infos.cnv_inf) (ind, u) args2 t1 with
      | args2, args1 -> Array.fold_left2 (fun u v1 v2 -> unify CONV infos lft1 v1 lft2 v2 u) evd args1 args2
      | exception Not_found -> raise NotConvertible
      end

    | _ -> raise NotConvertible
    end

    (* Should not happen because both (hd1,v1) and (hd2,v2) are in whnf *)
    | ( (FLetIn _, _) | (FIrrelevant, _) | (FCLOS _, _) | (FLIFT _, _) | (FLOCKED, _)
      | (_, FLetIn _) | (_, FIrrelevant) | (_, FCLOS _) | (_, FLIFT _) | (_, FLOCKED) ) -> assert false

    | (FRel _ | FAtom _ | FConstruct _ | FInd _ | FProj _ | FFix _ | FCoFix _ | FCaseInvert _
      | FProd _ | FInt _ | FFloat _ | FString _ | FArray _ | FCaseT _), _ -> raise NotConvertible

and unify cv_pb infos ?(elim=Elim None) lft1 t1 lft2 t2 evd =
  match _unify cv_pb infos ~elim lft1 t1 lft2 t2 evd with
  | res -> res
  | exception FailElim when not @@ in_elim elim -> evd

and convert_under_context infos e1 e2 lft1 lft2 ctx (nas1, c1) (nas2, c2) cu =
  let n = Array.length nas1 in
  let () = assert (Int.equal n (Array.length nas2)) in
  let e1, e2 = match ctx with
  | None -> (* nolet *)
    let e1 = usubs_liftn n e1 in
    let e2 = usubs_liftn n e2 in
    e1, e2
  | Some (ctx, u1, u2, args1, args2) ->
    let e1 = esubst_of_rel_context_instance_list ctx u1 args1 e1 in
    let e2 = esubst_of_rel_context_instance_list ctx u2 args2 e2 in
    e1, e2
  in
  let infos = push_relevances infos (Array.map (usubst_binder e1) nas1) in
  unify CONV infos (el_liftn n lft1) (mk_clos e1 c1) (el_liftn n lft2) (mk_clos e2 c2) cu

and convert_return_clause mib mip infos e1 e2 lft1 lft2 u1 u2 pms1 pms2 p1 p2 cu =
  let ctx =
    if Int.equal mip.mind_nrealargs mip.mind_nrealdecls then None
    else
      let ctx, _ = List.chop mip.mind_nrealdecls mip.mind_arity_ctxt in
      let pms1 = inductive_subst mib u1 pms1 in
      let pms2 = inductive_subst mib u1 pms2 in
      let open Context.Rel.Declaration in
      (* Add the inductive binder *)
      let dummy = mkProp in
      let ctx = LocalAssum (Context.anonR, dummy) :: ctx in
      Some (ctx, u1, u2, pms1, pms2)
  in
  convert_under_context infos e1 e2 lft1 lft2 ctx (fst p1) (fst p2) cu

and convert_branches mib mip infos e1 e2 lft1 lft2 u1 u2 pms1 pms2 br1 br2 evd =
  let fold i (ctx, _) evd =
    let ctx =
      if Int.equal mip.mind_consnrealdecls.(i) mip.mind_consnrealargs.(i) then None
      else
        let ctx, _ = List.chop mip.mind_consnrealdecls.(i) ctx in
        let pms1 = inductive_subst mib u1 pms1 in
        let pms2 = inductive_subst mib u2 pms2 in
        Some (ctx, u1, u2, pms1, pms2)
    in
    let c1 = br1.(i) in
    let c2 = br2.(i) in
    convert_under_context infos e1 e2 lft1 lft2 ctx c1 c2 evd
  in
  Array.fold_right_i fold mip.mind_nf_lc evd


let evar_handler =
  let evar_expand (ev, inst) =
    EvarUndefined (ev, inst |> SList.to_list |> List.map Option.get)
  in
  let qvar_irrelevant _ = assert false in (* Only used in conversion mode, but we use reduction mode here *)
  let qnorm q = Sorts.Quality.QVar q in
  let evar_irrelevant _ = false in
  let evar_repack (ev, args) = mkEvar (ev, SList.of_full_list args) in
  { CClosure.evar_expand; evar_irrelevant; evar_repack; qvar_irrelevant; qnorm; }

let cumul_lax env evd t1 t2 =
  let infos = create_clos_infos ~evars:evar_handler RedFlags.all env in
  let lft_tab = create_tab () and rgt_tab = create_tab () in
  let t1 = inject t1 and t2 = inject t2 in
  unify CUMUL { cnv_inf = infos; lft_tab; rgt_tab } el_id t1 el_id t2 evd


let mk_sort_qvar q u = Sorts.qsort q (Universe.make u)
let mk_type_lvl u = Sorts.sort_of_univ (Universe.make u)

let quality_of_quality_mask evd =
  let open Sorts.Quality in
  function
  | PQConstant q -> evd, QConstant q
  | PQVar (q, bound) -> ExtraEnv.add_quality q ~bound evd, QVar q

let sort_of_sort_pattern evd = function
  | PSSProp -> evd, sprop
  | PSProp -> evd, prop
  | PSSet -> evd, set
  | PSType (u, bound) -> ExtraEnv.add_universe u ~bound evd, mk_type_lvl u
  | PSQSort ((q, qbound), (u, ubound)) ->
      evd |> ExtraEnv.add_quality q ~bound:qbound |> ExtraEnv.add_universe u ~bound:ubound, mk_sort_qvar q u

let instance_of_instance_mask evd (qs, us : _ instance_mask) =
  let evd, qs = Array.fold_left_map quality_of_quality_mask evd qs in
  let evd, us = Array.fold_left_map (fun evd (lvl, bound) -> ExtraEnv.add_universe lvl ~bound evd, lvl) evd us in
  evd, UVars.Instance.of_array (qs, us)

let declare_instance_annot evd (qs, us) =
  let evd = Array.fold_left (fun evd q -> ExtraEnv.add_quality q ~bound:false evd) evd qs in
  let evd = Array.fold_left (fun evd lvl -> ExtraEnv.add_universe lvl ~bound:false evd) evd us in
  evd

let instance_of_instance_annot (qs, us) =
  let qs = Array.map (fun q -> Sorts.Quality.QVar q) qs in
  UVars.Instance.of_array (qs, us)


let declare_app_annots env evd ((evkty, qty, uty), (evkret, qret, uret)) =
  let ctx = Environ.rel_context env in

  let evd = evd |> ExtraEnv.add_quality qty ~bound:false |> ExtraEnv.add_universe uty ~bound:false in
  let argsort = mk_sort_qvar qty uty in
  let evd = ExtraEnv.add_evar evkty ctx (mkSort argsort) Relevant Anonymous evd in
  let argty = mkEvar (evkty, SList.of_full_list (List.mapi (fun i _ -> mkRel (i+1)) ctx)) in
  let argrel = RelevanceVar qty in
  let decl = Context.Rel.Declaration.LocalAssum (Context.make_annot Anonymous argrel, argty) in
  let ctx' = Context.Rel.add decl ctx in

  let evd = evd |> ExtraEnv.add_quality qret ~bound:false |> ExtraEnv.add_universe uret ~bound:false in
  let retsort = mk_sort_qvar qret uret in
  let evd = ExtraEnv.add_evar evkret ctx' (mkSort retsort) Relevant Anonymous evd in

  evd

let reduce_to_prod env evd ((evkty, qty, _uty), (evkret, _qret, _uret)) t =
  let open CClosure in
  let infos = create_conv_infos ~evars:evar_handler RedFlags.all env in
  let st = inject t in
  let ft = whd_fterm infos (create_tab ()) st in
  match fterm_of ft with
  | FProd (na, c1, c2, e) ->
      let ty = term_of_fconstr c1 in
      let ret = term_of_fconstr (mk_clos e c2) in
      let evd = ExtraEnv.define_evar evkty EQ ty evd in
      let evd = ExtraEnv.define_evar evkret EQ ret evd in
      evd, (ty, na.Context.binder_relevance, ret)

  | FEvar (ev, inst, e, _) ->

    let instlen = Environ.nb_rel env in

    let argty = mkEvar (evkty, SList.of_full_list (List.init instlen (fun i -> mkRel (i+1)))) in
    let retty = mkEvar (evkret, SList.of_full_list (List.init (instlen+1) (fun i -> mkRel (i+1)))) in

    let argrel = RelevanceVar qty in
    let decl = Context.Rel.Declaration.LocalAssum (Context.make_annot Anonymous argrel, argty) in
    let prodty = Term.mkProd_wo_LetIn decl retty in

    let evd =
      if is_frel_inst e inst then
        ExtraEnv.define_evar ev EQ prodty evd
      else evd
    in
    evd, (argty, argrel, retty)
  | _ -> CErrors.anomaly (Pp.str "Typing in rewrite rules")

let declare_ind_annots env evd ind (qinst_annot, uinst_annot, args_annot) =

  let evd = declare_instance_annot evd (qinst_annot, uinst_annot) in

  let (_, mip) = Inductive.lookup_mind_specif env ind in

  let ctx = Environ.rel_context env in
  let ar_ctx = mip.mind_arity_ctxt in

  let rec apply_rec evd ar_telescope evks subst =
    match ar_telescope, evks with
    | Context.Rel.Declaration.LocalDef (_, b, _) :: l, evks ->
      let b = Vars.substl subst b in
      apply_rec evd l evks (b :: subst)
    | Context.Rel.Declaration.LocalAssum (na, ty) :: l, evk :: evks ->
      let ty = Vars.substl subst ty in
      let evd = ExtraEnv.add_evar evk ctx ty na.Context.binder_relevance Anonymous evd in
      let ev = mkEvar (evk, SList.of_full_list (List.mapi (fun i _ -> mkRel (i+1)) ctx)) in
      apply_rec evd l evks (ev :: subst)
    | [], [] -> evd
    | _ -> CErrors.anomaly (Pp.str"Bad length")
  in
  let evd = apply_rec evd (List.rev ar_ctx) (Array.to_list args_annot) [] in
  evd


let reduce_to_appind env evd ind (qinst_annot, uinst_annot, args_annot) t =
  let open CClosure in
  let infos = create_conv_infos ~evars:evar_handler RedFlags.all env in
  let st = inject t in
  let ft = whd_fterm infos (create_tab ()) st in
  match fterm_of ft with
  | FInd (ind', u) when Ind.CanOrd.equal ind ind' ->
      let u' = instance_of_instance_annot (qinst_annot, uinst_annot) in
      let evd = ExtraEnv.compare_instances u u' evd in
      let args = [||] in
      let evd = Array.fold_left2 (fun evd evk arg -> ExtraEnv.define_evar evk EQ arg evd) evd args_annot args in
      evd, (u, args)
  | FApp (hd, args) ->
      begin match fterm_of hd with
      | FInd (ind', u) when Ind.CanOrd.equal ind ind' ->
        let u' = instance_of_instance_annot (qinst_annot, uinst_annot) in
        let evd = ExtraEnv.compare_instances u u' evd in
        let args = Array.map term_of_fconstr args in
        let evd = Array.fold_left2 (fun evd evk arg -> ExtraEnv.define_evar evk EQ arg evd) evd args_annot args in
        evd, (u, args)
      | _ -> CErrors.anomaly (Pp.str "Typing in rewrite rules")
      end
  | FEvar (ev, inst, e, _) ->

    let u = instance_of_instance_annot (qinst_annot, uinst_annot) in
    let (mib, _) = Inductive.lookup_mind_specif env ind in

    let cst = Inductive.instantiate_inductive_constraints mib u in
    let evd = ExtraEnv.enforce_constraints evd cst in

    let instlen = Environ.nb_rel env in
    let args = Array.map (fun evk -> mkEvar (evk, SList.of_full_list (List.init instlen (fun i -> mkRel (i+1))))) args_annot in
    let indargs = mkApp (mkIndU (ind, u), args) in

    let evd =
      if is_frel_inst e inst then
        ExtraEnv.define_evar ev EQ indargs evd
      else evd
    in
    evd, (u, args)
  | _ -> CErrors.anomaly (Pp.str "Typing in rewrite rules")




let warn_irrelevant_pattern = CWarnings.create ~name:"irrelevant-pattern" Fun.id

let warn_eta_in_pattern =
  CWarnings.create ~name:"eta-in-pattern" Fun.id

let warn_redex_in_rewrite_rules =
  CWarnings.create ~name:"redex-in-rewrite-rules"
  (fun redex -> Pp.(str "This pattern contains a" ++ redex ++ str " which may prevent this rule from being triggered."))

let rec check_may_eta ?loc env evd ?tryother t =
  match kind (Reduction.whd_all ~evars:evar_handler env t) with
  | Prod _ ->
      warn_eta_in_pattern ?loc
        Pp.(str "This subpattern has a product type, but pattern-matching is not done modulo eta, so this rule may not trigger at required times.")
  | Sort _ -> ()
  | Ind (ind, _) ->
      let specif = Inductive.lookup_mind_specif env ind in
      if not @@ Inductive.is_primitive_record specif then () else
        warn_eta_in_pattern ?loc
          Pp.(str "This subpattern has a primitive record type, but pattern-matching is not done modulo eta, so this rule may not trigger at required times.")
  | App (i, _) -> check_may_eta ?loc env evd ?tryother i
  | _ ->
      match tryother with
      | Some t -> check_may_eta ?loc env evd t
      | None ->
        warn_eta_in_pattern ?loc
          Pp.(str "This subpattern has a yet unknown type, which may be a product type, but pattern-matching is not done modulo eta, so this rule may not trigger at required times.")


let type_of_relative env n =
  env |> lookup_rel n |> RelDecl.get_type |> lift n

let type_of_inductive env evd (ind, u) =
  let (mib, _ as specif) = Inductive.lookup_mind_specif env ind in
  assert (List.is_empty mib.mind_hyps);
  let t, cstrs = Inductive.constrained_type_of_inductive (specif, u) in
  let evd = ExtraEnv.enforce_constraints evd cstrs in
  evd, t

let type_of_constructor env evd (c, _ as cu) =
  let (mib, _ as specif) = Inductive.lookup_mind_specif env (inductive_of_constructor c) in
  assert (List.is_empty mib.mind_hyps);
  let t, cstrs = Inductive.constrained_type_of_constructor cu specif in
  let evd = ExtraEnv.enforce_constraints evd cstrs in
  evd, t

let type_of_constant env evd (kn, _ as cst) =
  let cb = lookup_constant kn env in
  assert (List.is_empty cb.const_hyps);
  let ty, cu = constant_type env cst in
  let evd = ExtraEnv.enforce_constraints evd cu in
  evd, ty


let judge_of_relative env k = make_judge (mkRel k) (type_of_relative env k)

let judge_of_inductive env evd indu =
  let evd, ty = type_of_inductive env evd indu in
  evd, make_judge (mkIndU indu) ty

let judge_of_constructor env evd cu =
  let evd, ty = type_of_constructor env evd cu in
  evd, make_judge (mkConstructU cu) ty

let judge_of_constant env evd cst =
  let evd, ty = type_of_constant env evd cst in
  evd, make_judge (mkConstU cst) ty

let instantiate_context u subst nas ctx =
  let open Context.Rel.Declaration in
  let open Context in
  let open Vars in
  let instantiate_relevance na =
    { na with binder_relevance = UVars.subst_instance_relevance u na.binder_relevance }
  in
  let rec instantiate i ctx = match ctx with
  | [] -> assert (Int.equal i (-1)); []
  | LocalAssum (na, ty) :: ctx ->
    let ctx = instantiate (pred i) ctx in
    let ty = substnl subst i (subst_instance_constr u ty) in
    let na = instantiate_relevance na in
    let na = Context.map_annot (fun _ -> nas.(i)) na in
    LocalAssum (na, ty) :: ctx
  | LocalDef (na, ty, bdy) :: ctx ->
    let ctx = instantiate (pred i) ctx in
    let ty = substnl subst i (subst_instance_constr u ty) in
    let bdy = substnl subst i (subst_instance_constr u bdy) in
    let na = instantiate_relevance na in
    let na = Context.map_annot (fun _ -> nas.(i)) na in
    LocalDef (na, ty, bdy) :: ctx
  in
  instantiate (List.length ctx - 1) ctx


let rec instantiate ctx args subst =
  let open Context.Rel.Declaration in
  match ctx, args with
  | [], [] -> subst
  | LocalAssum _ :: ctx, a :: args ->
    let subst = Esubst.subs_cons (Vars.make_substituend a) subst in
    instantiate ctx args subst
  | LocalDef (_, a, _) :: ctx, args ->
    let a = Vars.esubst Vars.lift_substituend subst a in
    let subst = Esubst.subs_cons (Vars.make_substituend a) subst in
    instantiate ctx args subst
  | _ -> assert false


(* Annotation for cases *)
let make_case_info env ind =
  let (mib,mip) = Inductive.lookup_mind_specif env ind in
  let print_info = { style = RegularStyle } in
  (* Reasonable dummy, even if unused *)
  { ci_ind     = ind;
    ci_npar    = mib.mind_nparams;
    ci_cstr_ndecls = mip.mind_consnrealdecls;
    ci_cstr_nargs = mip.mind_consnrealargs;
    ci_pp_info = print_info }

let rec is_applied_ind_template env = function
  | PApp (f, _, _, _) -> is_applied_ind_template env f
  | PInd (ind, _) -> ignore (env, ind); false
  | _ -> false

let rec typecheck_pattern env evd = function

  | p when is_applied_ind_template env p -> assert false

  | PRel n -> evd, judge_of_relative env n
  | PSort (s, retu) ->
      let evd, s = sort_of_sort_pattern evd s in
      let evd = ExtraEnv.add_universe retu ~bound:false evd in
      let evd = ExtraEnv.enforce_super_level s retu evd in
      evd, make_judge (mkSort s) (mkSort @@ Sorts.sort_of_univ (Universe.make retu))
  | PInd (ind, u) ->
      let evd, u = instance_of_instance_mask evd u in
      judge_of_inductive env evd (ind, u)
  | PConstr (cstr, u) ->
      let evd, u = instance_of_instance_mask evd u in
      judge_of_constructor env evd (cstr, u)
  | PSymbol (s, u) ->
      let evd, u = instance_of_instance_mask evd u in
      judge_of_constant env evd (s, u)
  | PInt i ->
      evd, make_judge (mkInt i) (Typeops.type_of_int env)
  | PFloat f ->
      evd, make_judge (mkFloat f) (Typeops.type_of_float env)
  | PString s ->
      evd, make_judge (mkString s) (Typeops.type_of_string env)
  | PLambda (na, argty, (argq, argu), bod) ->
      let evd = evd |> ExtraEnv.add_quality argq ~bound:false |> ExtraEnv.add_universe argu ~bound:false in
      let evd, argtyj = typecheck_arg_pattern env evd (mkSort @@ mk_sort_qvar argq argu, Relevant) argty in
      let decl = Context.Rel.Declaration.LocalAssum (Context.make_annot na (Sorts.RelevanceVar argq), j_val argtyj) in
      let env = Environ.push_rel decl env in
      let evd, bodj = typecheck_pattern env evd bod in
      let () = check_may_eta env evd (j_type bodj) in
      let tm = Term.mkLambda_or_LetIn decl (j_val bodj) in
      let ty = Term.mkProd_or_LetIn decl (j_type bodj) in
      evd, make_judge tm ty
  | PProd (na, domty, (domq, domu), codty, (codq, codu), retu) ->
      let evd = evd |> ExtraEnv.add_quality domq ~bound:false |> ExtraEnv.add_universe domu ~bound:false in
      let doms = mk_sort_qvar domq domu in
      let evd, domtyj = typecheck_arg_pattern env evd (mkSort doms, Relevant) domty in
      let decl = Context.Rel.Declaration.LocalAssum (Context.make_annot na (Sorts.RelevanceVar domq), j_val domtyj) in
      let env = Environ.push_rel decl env in

      let evd = evd |> ExtraEnv.add_quality codq ~bound:false |> ExtraEnv.add_universe codu ~bound:false in
      let cods = mk_sort_qvar codq codu in
      let evd, codj = typecheck_arg_pattern env evd (mkSort cods, Relevant) codty in

      let evd = ExtraEnv.add_universe retu ~bound:false evd in
      let evd = ExtraEnv.enforce_product_level env doms cods retu evd in

      let tm = Term.mkProd_or_LetIn decl (j_val codj) in
      let ty = mkSort @@ Sorts.make (Sorts.quality cods) (Universe.make retu) in
      evd, make_judge tm ty

  | PApp (f, arg, (evkty, qty, uty), (evkret, qret, uret)) ->

    let evd, j_head = typecheck_pattern env evd f in

    let evd = declare_app_annots env evd ((evkty, qty, uty), (evkret, qret, uret)) in
    let evd, (argty, argrel, retty) = reduce_to_prod env evd ((evkty, qty, uty), (evkret, qret, uret)) (j_type j_head) in

    let evd, j_arg = typecheck_arg_pattern env evd (argty, argrel) arg in

    let retty = Vars.subst1 (j_val j_arg) retty in
    let head = mkApp (j_val j_head, [|j_val j_arg|]) in
    evd, make_judge head retty

  | PProj (c, p, annots) ->

    let evd, j_head = typecheck_pattern env evd c in

    let ind = Projection.Repr.inductive p in

    let evd = declare_ind_annots env evd ind annots in
    let evd, (u, args) = reduce_to_appind env evd ind annots (j_type j_head) in

    let p = Projection.make p true in
    let pr, pty = lookup_projection p env in
    let pr = UVars.subst_instance_relevance u pr in
    let ty = Vars.subst_instance_constr u pty in
    let bod = mkProj (p, pr, j_val j_head) in
    evd, make_judge bod (Vars.substl (j_val j_head :: CArray.rev_to_list args) ty)

  | PCase (c, ind, annots, (ret, (qr, ur)), brs) ->

    let evd, j_head = typecheck_pattern env evd c in
    let evd = ExtraEnv.add_pattern_relevance (Relevanceops.relevance_of_term env (j_val j_head)) evd in
    (* There may be a relevance change here *)

    let evd = declare_ind_annots env evd ind annots in
    let evd, (u, args) = reduce_to_appind env evd ind annots (j_type j_head) in
    let (mib, mip) = Inductive.lookup_mind_specif env ind in

    let (params, realargs) = Array.chop mib.mind_nparams args in
    let paramdecl = Vars.subst_instance_context u mib.mind_params_ctxt in
    let paramsubst = Vars.subst_of_rel_context_instance paramdecl params in

    let pctx =
      let realdecls, _ = List.chop mip.mind_nrealdecls mip.mind_arity_ctxt in
      let self =
        let args = Context.Rel.instance mkRel 0 mip.mind_arity_ctxt in
        let inst = UVars.Instance.(abstract_instance (length u)) in
        mkApp (mkIndU (ind, inst), args)
      in
      let realdecls = Context.Rel.Declaration.LocalAssum (Context.make_annot Anonymous mip.mind_relevance, self) :: realdecls in
      instantiate_context u paramsubst (fst ret) realdecls
    in

    let (evd, p) =
      let p_env = Environ.push_rel_context pctx env in
      let evd = evd |> ExtraEnv.add_quality qr ~bound:false |> ExtraEnv.add_universe ur ~bound:false in
      let evd, j_p = typecheck_arg_pattern p_env evd (mkSort @@ mk_sort_qvar qr ur, Relevant) (snd ret) in
      (evd, (Array.map_of_list Context.Rel.Declaration.get_annot pctx, j_val j_p))
    in

    let build_one_branch i evd (brnas, br) =
      let (ctx, cty) = mip.mind_nf_lc.(i) in

      let bctx, _ = List.chop mip.mind_consnrealdecls.(i) ctx in
      let bctx = instantiate_context u paramsubst brnas bctx in
      let br_env = Environ.push_rel_context bctx env in
      let cty = Vars.substnl paramsubst mip.mind_consnrealdecls.(i) (Vars.subst_instance_constr u cty) in

      let (_, retargs) = Inductive.find_rectype br_env cty in

      let params = Array.map (fun c -> lift mip.mind_consnrealdecls.(i) c) params in
      let cargs = Context.Rel.instance mkRel 0 bctx in
      let cstr = mkApp (mkConstructU ((ind, i + 1), u), Array.append params cargs) in
      let indices = List.lastn mip.mind_nrealargs retargs in
      let subst = instantiate (List.rev pctx) (indices @ [cstr]) (Esubst.subs_shft (mip.mind_consnrealdecls.(i), Esubst.subs_id 0)) in

      let brty = Vars.esubst Vars.lift_substituend subst (snd p) in

      let evd, j_br = typecheck_arg_pattern br_env evd (brty, RelevanceVar qr) br in
      evd, (Array.map_of_list Context.Rel.Declaration.get_annot ctx, j_val j_br)
    in
    let evd, brs = Array.fold_left_map_i build_one_branch evd brs in

    let rp = RelevanceVar qr in
    let ci = make_case_info env ind in
    let body = mkCase (ci, u, params, (p, rp), NoInvert, j_val j_head, brs) in

    let ty =
      let subst = Vars.subst_of_rel_context_instance_list pctx (CArray.to_list realargs @ [j_val j_head]) in
      Vars.substl subst (snd p)
    in

    evd, make_judge body ty


and typecheck_arg_pattern env evd (typ, rel) = function
  | PVar (evk, ido) ->
    let ctx = Environ.rel_context env in
    let evd = ExtraEnv.add_evar evk ctx typ rel ido evd in
    evd, make_judge (mkEvar (evk, SList.of_full_list (List.mapi (fun i _ -> mkRel (i+1)) ctx))) typ

  | Pat p ->
    let evd, j = typecheck_pattern env evd p in
    let evd = cumul_lax env evd (j_type j) typ in
    let evd = ExtraEnv.add_pattern_relevance (Relevanceops.relevance_of_term env (j_val j)) evd in
    let () = check_may_eta env evd ~tryother:(j_type j) typ in
    evd, make_judge (j_val j) typ


let typecheck_pattern env pattern =
  typecheck_pattern env ExtraEnv.empty pattern




let evar_handler_defs defs =
  let evar_expand (ev, inst) =
    match Evar.Map.find_opt ev defs with
    | Some (_, def) -> CClosure.EvarDefined (Vars.substl (inst |> SList.to_list |> List.map Option.get) def)
    | None -> CClosure.EvarUndefined (ev, inst |> SList.to_list |> List.map Option.get)
  in
  let qvar_irrelevant _ = assert false in (* Only used in conversion mode, but we use reduction mode here *)
  let qnorm q = Sorts.Quality.QVar q in
  let evar_irrelevant _ = false in
  let evar_repack (ev, args) = mkEvar (ev, SList.of_full_list args) in
  { CClosure.evar_expand; evar_irrelevant; evar_repack; qvar_irrelevant; qnorm; }


let unify_lax rels conv_pb defs env evd t1 t2 =
  let infos = create_clos_infos ~evars:(evar_handler_defs defs) RedFlags.all env in
  let infos = CClosure.set_info_relevances infos rels in
  let lft_tab = create_tab () and rgt_tab = create_tab () in
  let t1 = inject t1 and t2 = inject t2 in
  unify conv_pb { cnv_inf = infos; lft_tab; rgt_tab } el_id t1 el_id t2 evd



let iter_with_full_binders env g f n c =
  let open Context.Rel.Declaration in
  match kind c with
  | (Rel _ | Meta _ | Var _   | Sort _ | Const _ | Ind _
    | Construct _ | Int _ | Float _ | String _) -> ()
  | Cast (c,_,t) -> f n c; f n t
  | Prod (na,t,c) -> f n t; f (g (LocalAssum (na, t)) n) c
  | Lambda (na,t,c) -> f n t; f (g (LocalAssum (na, t)) n) c
  | LetIn (na,b,t,c) -> f n b; f n t; f (g (LocalDef (na, b, t)) n) c
  | App (c,l) -> f n c; Array.Fun1.iter f n l
  | Evar (_, l) ->
    SList.Skip.iter (fun c -> f n c) l
  | Case (ci,u,pms,p,iv,c,bl) ->
    let (_, _, pms, (p,_), iv, c, bl) = Inductive.annotate_case env (ci, u, pms, p, iv, c, bl) in
    let f_ctx (ctx, c) = f (List.fold_right g ctx n) c in
    Array.Fun1.iter f n pms; f_ctx p; iter_invert (f n) iv; f n c; Array.iter f_ctx bl
  | Proj (_,_,c) -> f n c
  | Fix (_,(lna,tl,bl)) ->
    Array.iter (f n) tl;
    let n' = Array.fold_left2_i (fun i n na t -> g (LocalAssum (na, lift i t)) n) n lna tl in
    Array.iter (f n') bl
  | CoFix (_,(lna,tl,bl)) ->
    Array.iter (f n) tl;
    let n' = Array.fold_left2_i (fun i n na t -> g (LocalAssum (na,lift i t)) n) n lna tl in
    Array.iter (f n') bl
  | Array (_u,t,def,ty) -> Array.Fun1.iter f n t; f n def; f n ty

let noccur_evar env evd defs evk c =
  let open Context.Rel.Declaration in
  let exception Occur in
  let cache = ref Int.Set.empty (* cache for let-ins *) in
  let rec occur_rec check_types (k, env as acc) c =
  match kind c with
  | Evar (evk', args') ->
    if Evar.equal evk evk' then raise Occur
    else begin
      match Evar.Map.find_opt evk' defs with
      | Some (_, def) -> occur_rec check_types acc def
      | None ->
          if check_types then
            occur_rec false acc (Typeops.type_of env (ExtraEnv.sigma_of evd) (evar_handler_defs defs) c);
          SList.Skip.iter (occur_rec check_types acc) args'
      end
  | Rel i when i > k ->
     if not (Int.Set.mem (i-k) !cache) then
       let decl = Environ.lookup_rel i env in
       if check_types then
         (cache := Int.Set.add (i-k) !cache; occur_rec false acc (lift i (get_type decl)));
       (match decl with
        | LocalAssum _ -> ()
        | LocalDef (_,b,_) -> cache := Int.Set.add (i-k) !cache; occur_rec false acc (lift i b))
  | Proj (_, _, c) -> occur_rec true acc c
  | _ -> iter_with_full_binders env (fun rd (k,env) -> (succ k, push_rel rd env))
    (occur_rec check_types) acc c
  in
  try occur_rec false (0,env) c; true with Occur -> false

type 'a imitation = Same | Reconstructed of extra_env * Level.t list * 'a | Impossible

let imitate_sort evd univ_gen cmp s =
  match s with
  | Prop | SProp -> Same
  | Set when cmp = GEQ -> Same
  | Set | Type _ | QSort _ ->
    let qorig = Sorts.quality s in
    let uorig = ExtraEnv.get_algebraic s in
    let evd, l = univ_gen evd () in
    let u = Universe.make l in
    let evd =
      match cmp with
      | LEQ -> ExtraEnv.enforce_cmp_universe CUMUL qorig uorig u evd
      | GEQ -> ExtraEnv.enforce_cmp_universe CUMUL qorig u uorig evd
      | EQ -> assert false
    in
    Reconstructed (evd, [l], mkSort @@ Sorts.(make qorig u))

let imitate_instance evd univ_gen cmp variance ui =
  let open UVars in
  let qs, us = Instance.to_array ui in
  let generated_univs = ref [] in
  let evd, us = Array.fold_left2_map (fun evd v u ->
    match v with
    | Variance.Covariant ->
        let evd, u' = univ_gen evd () in
        generated_univs := u' :: !generated_univs;
        let evd = match cmp with
          | LEQ -> ExtraEnv.enforce_constraint evd (u, Le, u')
          | GEQ -> ExtraEnv.enforce_constraint evd (u', Le, u)
          | EQ -> assert false
        in
        evd, u'
    | Variance.Invariant | Variance.Irrelevant -> evd, u) evd variance us
  in
  if List.is_empty !generated_univs then
    Same
  else
    Reconstructed (evd, List.rev !generated_univs, Instance.of_array (qs, us))

let rec imitate env evd defs univ_gen cmp t =
  match kind @@ Reduction.whd_all ~evars:(evar_handler_defs defs) env t with
  | Sort s -> imitate_sort evd univ_gen cmp s
  | Prod (na, ty, cod) ->
    begin match imitate env evd defs univ_gen cmp cod with
    | Same -> Same
    | Impossible -> Impossible
    | Reconstructed (evd, us, cod') -> Reconstructed (evd, us, mkProd (na, ty, cod'))
    end
  | Evar _ -> Impossible
  | App (f, args) when isInd f ->
      let ind, u = destInd f in
      let mind = Environ.lookup_mind (fst ind) env in
      begin match mind.mind_variance with
      | None -> Same
      | Some variances ->
        let num_param_arity = inductive_cumulativity_arguments (mind, snd ind) in
        if not (Int.equal num_param_arity (Array.length args)) then Same (* Not a type *)
        else
          begin match imitate_instance evd univ_gen cmp variances u with
          | Same | Impossible as r -> r
          | Reconstructed (evd, us, ui) ->
            Reconstructed (evd, us, mkApp (mkIndU (ind, ui), args))
          end
      end
  | _ -> (* All other types are neutral *) Same

let eq_cmp_to_imitation_cmp ?(us = []) = function
  | LEQ -> LESS us
  | EQ -> EQUAL
  | GEQ -> GREATER us

let imitate env evd defs univ_gen cmp t =
  match imitate env evd defs univ_gen cmp t with
  | Same -> Some (evd, (eq_cmp_to_imitation_cmp cmp, t))
  | Reconstructed (evd, us, t) -> Some (evd, (eq_cmp_to_imitation_cmp ~us cmp, t))
  | Impossible -> None


let check_sort_imitation evd us cmp sorig s =
  match sorig, s with
  | Prop, Prop | SProp, SProp -> if List.is_empty us then Some evd else None
  | Set, Set when cmp = GEQ -> if List.is_empty us then Some evd else None
  | Set, Type _ | Type _, Type _ | QSort _, QSort _ ->
    let qorig = Sorts.quality sorig in
    let uorig = ExtraEnv.get_algebraic sorig in
    if not @@ Quality.equal qorig (Sorts.quality s) then None else
    begin match us with
    | [] | _ :: _ :: _ -> None
    | [l] ->
    let evd = ExtraEnv.add_universe l ~bound:false evd in
    let u = Universe.make l in
    let evd =
      match cmp with
      | LEQ -> ExtraEnv.enforce_cmp_universe CUMUL qorig uorig u evd
      | GEQ -> ExtraEnv.enforce_cmp_universe CUMUL qorig u uorig evd
      | EQ -> assert false
    in
    Some evd
    end
  | (Prop | SProp | Set | Type _ | QSort _), _ -> None

let check_instance_imitation evd us cmp variance ui_orig ui =
  let open UVars in
  let qs_orig, us_orig = Instance.to_array ui_orig in
  let qs, uis = Instance.to_array ui in
  if not @@ Array.equal Quality.equal qs_orig qs then None else
  let error = ref false in
  let evd, us = Array.fold_left3 (fun (evd, us) v u u' ->
    match v, us with
    | Variance.Covariant, u'' :: us ->
        if not @@ Level.equal u' u'' then error := true;
        let evd = match cmp with
          | LEQ -> ExtraEnv.enforce_constraint evd (u, Le, u')
          | GEQ -> ExtraEnv.enforce_constraint evd (u', Le, u)
          | EQ -> assert false
        in
        evd, us
    | Variance.Covariant, ([] as us) -> error := true; evd, us
    | Variance.Invariant, us | Variance.Irrelevant, us ->
      if not @@ Level.equal u u' then error := true; evd, us)
        (evd, us) variance us_orig uis
  in
  if !error || not @@ List.is_empty us then
    None
  else
    Some evd

let rec check_imitation env evd defs us cmp t t' =
  match kind @@ Reduction.whd_all ~evars:(evar_handler_defs defs) env t with
  | Sort s ->
      if not @@ isSort t' then None else
        let s' = destSort t' in
        check_sort_imitation evd us cmp s s'
  | Prod (na, ty, cod) ->
    if not @@ isProd t' then None else
    let (na', ty', cod') = destProd t' in
    if not @@ Context.eq_annot Name.equal relevance_equal na na' && Constr.equal ty ty' then None else
    check_imitation env evd defs us cmp cod cod'
  | Evar _ -> None
  | App (f, args) when isInd f ->
      if not @@ isApp t' then None else
      let (f', args') = destApp t' in
      if not @@ Array.equal Constr.equal args args' then None else
      if not @@ isInd f' then None else
      let ind, u = destInd f in
      let ind', u' = destInd f' in
      if not @@ Ind.CanOrd.equal ind ind' then None else
      let mind = Environ.lookup_mind (fst ind) env in
      begin match mind.mind_variance with
      | None -> if List.is_empty us then Some evd else None
      | Some variances ->
        let num_param_arity = inductive_cumulativity_arguments (mind, snd ind) in
        if not (Int.equal num_param_arity (Array.length args)) then
          (if List.is_empty us then Some evd else None) (* Not a type *)
        else
          check_instance_imitation evd us cmp variances u u'
      end
  | _ -> (* All other types are neutral *)
      if Constr.equal t t' && List.is_empty us then Some evd else None


let add_evar_definition env evd defs evk (cmp, def) =
  let eqs = Evar.Map.find evk evd.evar_candidates in
  let evd = { evd with evar_candidates = Evar.Map.remove evk evd.evar_candidates } in
  let (ctx, evty, _, _) = Evar.Map.find evk evd.evar_map in
  let env = Environ.push_rel_context ctx env in
  if not @@ noccur_evar env evd defs evk def then
    CErrors.anomaly Pp.(str "looping definition in rewrite rules")
  else
  let defs = Evar.Map.add evk (cmp, def) defs in
  let defty = Typeops.type_of env (ExtraEnv.sigma_of evd) (evar_handler_defs defs) def in
  let rels = List.fold_right (fun decl rels -> Range.cons (RelDecl.get_relevance decl) rels) ctx Range.empty in
  let evd = unify_lax rels CUMUL defs env evd defty evty in

  let evd = List.fold_left (fun evd (cmp, t) ->
    match cmp with
    | LEQ    -> unify_lax rels CUMUL defs env evd t def
    | EQ   -> unify_lax rels CONV  defs env evd t def
    | GEQ -> unify_lax rels CUMUL defs env evd def t
    ) evd eqs
  in
  evd, defs

let find_evar_definition env evd defs evk def =
  let eqs = Evar.Map.find evk evd.evar_candidates in
  match def with
  | None ->
      (* If [eqs] is not empty, equalities got lost *)
      { evd with evar_candidates = Evar.Map.remove evk evd.evar_candidates }, defs, true
  | Some (cmp, def) ->
      let filter (cmp', t') =
        match cmp, cmp' with
        | EQUAL, EQ -> if Constr.equal def t' then Some evd else None
        | LESS us, LEQ | GREATER us, GEQ -> check_imitation env evd defs us cmp' t' def
        | _, (LEQ | EQ | GEQ) -> None
      in
      match List.find_map filter eqs with
      | None -> evd, defs, false
      | Some evd ->
      let evd, defs = add_evar_definition env evd defs evk (cmp, def) in
      evd, defs, true

let push_equality env evd defs (rels, q, t1, cv_pb, t2) =
  match QGraph.relevance q evd.qgraph with
  | RelevanceVar q' -> ExtraEnv.enforce_equality_relevancevar rels q' cv_pb t1 t2 evd, false
  | Irrelevant -> evd, false
  | Relevant -> unify_lax rels cv_pb defs env evd t1 t2, true


let push_constraints env evd defs =
  let push_evar_definitions evd defs_ok evks =
    List.fold_left (fun (evd, defs_ok, evks', flag) evk ->
      let evd, defs_ok, b = find_evar_definition env evd defs_ok evk (Evar.Map.find_opt evk defs) in
      evd, defs_ok, (if b then evks' else evk :: evks'), flag || b
      ) (evd, defs_ok, [], false) evks
  in
  let push_equalities evd defs_ok =
    let evd, equalities = { evd with equalities = [] }, evd.equalities in
    List.fold_left (fun (evd, flag) eq ->
      let evd, b = push_equality env evd defs_ok eq in
      evd, flag || b
      ) (evd, false) equalities
  in
  let push_qconstraints evd =
    let qgraph, qcstrs = QGraph.merge_qconstraints evd.qcstrs evd.qgraph in
    { evd with qgraph; qcstrs }, QConstraints.cardinal qcstrs <> QConstraints.cardinal evd.qcstrs
  in

  let rec round evd defs_ok evks =
    let evd, defs_ok, evks, b1 = push_evar_definitions evd defs_ok evks in

    let evd, b2 = push_qconstraints evd in

    let evd, b3 = push_equalities evd defs_ok in

    if b1 || b2 || b3 then
      round evd defs_ok evks
    else if List.is_empty evks then
      evd
    else
      CErrors.anomaly (Pp.str "Error in found equalities in rewrite rules")
  in
  round evd Evar.Map.empty (List.rev evd.evar_list)


let cumul_uconstraint u1 u2 c =
  match Universe.level u2 with
  | Some l2 -> List.fold_left (fun c (l, n) -> if n = 0 then enforce_leq_level l l2 c else Constraints.add (l, Lt, l2) c) c (Universe.repr u1)
  | None -> c

let conv_uconstraints u1 u2 c =
  c
  |> cumul_uconstraint u1 u2
  |> cumul_uconstraint u2 u1


let push_uconstraint qgraph (q, u1, cv_pb, u2) ucstrs =
  let open Sorts.Quality in
  match QGraph.nf_quality qgraph q with
  | QConstant (QSProp | QProp) | QVar _ -> ucstrs
  | QConstant QType ->
    match cv_pb with
    | CONV -> conv_uconstraints u1 u2 ucstrs
    | CUMUL -> cumul_uconstraint u1 u2 ucstrs


let nf_evar evars qgraph defs c =
  let rec nf_evar c =
    match kind c with
    | Evar (evk, inst) ->
      begin match Evar.Map.find_opt evk defs with
      | Some (_, def) ->
          let inst = SList.Smart.map nf_evar inst in
          let args = inst |> SList.to_list |> List.mapi (fun i t -> Option.default (mkRel (i+1)) t) in
          Vars.substl args def
        | None ->
          if not @@ List.mem evk evars then CErrors.anomaly Pp.(str "Unknown evar")
          else Constr.map nf_evar c
        end
    | _ -> Constr.map nf_evar c
  in
  let c = nf_evar c in
  let usubst = QVar.Map.mapi (fun qv q -> Option.default (Sorts.Quality.QVar qv) q) qgraph.QGraph.qmap, Level.Map.empty in
  let subst_rel = Sorts.relevance_subst_rel_fn (fun qv -> QGraph.relevance qv qgraph) in
  Vars.subst_univs_level_constr ~subst_rel usubst c

let nf_evar_ctx evars qgraph defs c =
  let subst_rel = Sorts.relevance_subst_rel_fn (fun qv -> QGraph.relevance qv qgraph) in
  Context.Rel.map_with_relevance subst_rel (nf_evar evars qgraph defs) c

let nf_evar_map evars qgraph defs =
  Evar.Map.map (fun (ctx, ty, rel, ido) -> (
      nf_evar_ctx evars qgraph defs ctx,
      nf_evar evars qgraph defs ty,
      Sorts.relevance_subst_rel_fn (fun qv -> QGraph.relevance qv qgraph) rel,
      ido))


let nf_evar_info (Info info) =
  let qgraph = QGraph.of_pair info.qualities (info.qgraph, info.qabove_prop) in
  Info { info with
    evar_map = Evar.Map.map (fun (ctx, ty, rel, ido) -> (
      nf_evar_ctx info.evars qgraph info.evar_defs ctx,
      nf_evar info.evars qgraph info.evar_defs ty,
      Sorts.relevance_subst_rel_fn (fun qv -> QGraph.relevance qv qgraph) rel,
      ido)) info.evar_map;
  }

let nf_evar (Info info) c =
  let qgraph = QGraph.of_pair info.qualities (info.qgraph, info.qabove_prop) in
  nf_evar info.evars qgraph info.evar_defs c

let check_inferred_constraints env evd (Info info) =
  let () =
    if not @@ List.equal Evar.equal evd.evar_list info.evars then
      CErrors.anomaly (Pp.str "Different evars in rewrite rules")
  in
  let evd = push_constraints env evd info.evar_defs in
  (* The evar_map field shouldn't have changed and the equalities field should be emptied *)
  let ustate = List.fold_left (fun ucstrs cstr -> push_uconstraint evd.qgraph cstr ucstrs) evd.ulcstrs evd.ucstrs in

  let () = Evar.Map.iter (fun ev _ ->
      if not @@ List.mem ev info.evars then
        CErrors.anomaly (Pp.str "Evar definition on unknown evar in rewrite rules"))
      info.evar_defs
  in

  let evar_map = nf_evar_map info.evars (QGraph.of_pair info.qualities (info.qgraph, info.qabove_prop)) info.evar_defs evd.evar_map in

  let () =
    Evar.Map.symmetric_diff_fold
    (fun _ found expected () ->
        match found, expected with
        | None, None -> assert false
        | Some _, None -> CErrors.anomaly (Pp.str "Missing evar information in rewrite rules")
        | None, Some _ -> CErrors.anomaly (Pp.str "Unknown evar information in rewrite rules")
        | Some (ctx, ty, rel, ido), Some (ctx', ty', rel', ido') ->
          let eqctx = Context.Rel.equal relevance_equal Constr.equal ctx ctx' in
          let eqty = Constr.equal ty ty' in
          let eqrel = relevance_equal rel rel' in
          let eqid = Name.equal ido ido' in
          if not (eqctx && eqty && eqrel && eqid) then
            CErrors.anomaly (Pp.str "Wrong information in rewrite rules")
    )
    evar_map info.evar_map ()
  in

  let () = QVar.Map.symmetric_diff_fold (fun _ q1 q2 () ->
    match q1, q2 with
    | Some b, Some b' -> if b <> b' then CErrors.anomaly (Pp.str "Incompatible quality information in rewrite rules")
    | Some _, None -> CErrors.anomaly (Pp.str "Missing quality information in rewrite rules")
    | None, Some _ -> CErrors.anomaly (Pp.str "Unknown quality information in rewrite rules")
    | _, _ -> assert false) evd.qualities info.qualities ()
  in
  let () = Level.Map.symmetric_diff_fold (fun _ u1 u2 () ->
    match u1, u2 with
    | Some b, Some b' -> if b <> b' then CErrors.anomaly (Pp.str "Incompatible universe information in rewrite rules")
    | Some _, None -> CErrors.anomaly (Pp.str "Missing universe information in rewrite rules")
    | None, Some _ -> CErrors.anomaly (Pp.str "Unknown universe information in rewrite rules")
    | _, _ -> assert false) evd.univs info.univs ()
  in
  let qcstrs = QGraph.to_qconstraints @@ QGraph.of_pair info.qualities (info.qgraph, info.qabove_prop) in
  if not @@ QConstraints.for_all (fun qcstr -> QGraph.check_constraint qcstr evd.qgraph) qcstrs then
    CErrors.anomaly (Pp.str "Quality equalities could not be confirmed");
  let ug = Environ.universes env
    |> Level.Map.fold (fun lvl _ ug -> UGraph.add_universe lvl ~lbound:UGraph.Bound.Prop ~strict:false ug) evd.univs
    |> UGraph.merge_constraints ustate
  in
  if not @@ UGraph.check_constraints info.ucstrs ug then
    CErrors.anomaly (Pp.str "Universe constraints could not be confirmed");
  ()

let check_pattern_relevances evd pat_rel =
  QVar.Set.iter (fun q ->
    match QGraph.relevance q evd.qgraph with
    | Irrelevant -> warn_irrelevant_pattern Pp.(str "Irrelevant subpattern in rewrite rules")
    | RelevanceVar q when match pat_rel with RelevanceVar q' -> QVar.equal q q' | _ -> false -> ()
    | RelevanceVar _ ->
        warn_irrelevant_pattern Pp.(str "Subpattern has different relevance than whole pattern in rewrite rules")
    | Relevant -> ()
    ) evd.pattern_relevances


let check_ucstr_slow env (Info info) (s1, cv_pb, s2) =
  let open Quality in
  let q1 = Sorts.quality s1 in
  let q2 = Sorts.quality s2 in
  let qgraph = QGraph.of_pair info.qualities (info.qgraph, info.qabove_prop) in
  let qgraph = match QGraph.nf_quality qgraph q1 with
    | QConstant _ -> qgraph
    | QVar q ->
      if cv_pb = CUMUL && (
        QGraph.check_constraint (q1, QConstraint.Leq, QConstant QType) qgraph ||
        not @@ QGraph.check_constraint (q2, QConstraint.Leq, QConstant QType) qgraph
      )
      then
        let qgraph = QGraph.set q (QConstant QType) qgraph in
        fst @@ QGraph.merge_qconstraints info.full_qcstrs qgraph
      else
        qgraph
  in
  let kind = QConstraint.(match cv_pb with CONV -> Equal | CUMUL -> Leq) in
  QGraph.check_constraint (q1, kind, q2) qgraph &&
  match s1, s2 with
  | (SProp | Prop | Set), _ | _, (SProp | Prop) -> true (* Quality unification is enough *)
  | _ ->
    let ustate = List.fold_left (fun ucstrs cstr -> push_uconstraint qgraph cstr ucstrs) info.ucstrs info.full_ucstrs in
    let ug = Environ.universes env
      |> Level.Map.fold (fun lvl _ ug -> UGraph.add_universe lvl ~lbound:UGraph.Bound.Prop ~strict:false ug) info.univs
      |> UGraph.merge_constraints ustate
    in
    begin match cv_pb with CONV -> UGraph.check_eq | CUMUL -> UGraph.check_leq end
      ug (ExtraEnv.get_algebraic s1) (ExtraEnv.get_algebraic s2)


let rec get_pconstrapp args = function
  | PApp (p, arg, _, _) -> get_pconstrapp (arg :: args) p
  | PConstr (c, _) -> Some (c, args)
  | _ -> None
let get_pconstrapp = get_pconstrapp []

let test_projection_apps env pat =
  match get_pconstrapp pat with None -> ()
  | Some (cst, args) ->
    let ind = fst cst in
  let specif = Inductive.lookup_mind_specif env ind in
  if not @@ Inductive.is_primitive_record specif then () else
  if List.for_all_i (fun i arg ->
    match arg with
    | PVar _ -> true
    | Pat PProj (_, p, _) -> Ind.CanOrd.equal (Projection.Repr.inductive p) ind && Projection.Repr.arg p = i
    | Pat _ -> false
  ) 0 args then
    warn_redex_in_rewrite_rules Pp.(str " subpattern compatible with an eta-long form for " ++ Id.print (snd specif).mind_typename ++ str"," )

let rec check_pattern_redex env = function
  | PApp (PLambda _, _, _, _) -> warn_redex_in_rewrite_rules (Pp.str " beta redex")
  | PCase (p, _, _, _, _) | PProj (p, _, _) when Option.has_some @@ get_pconstrapp p -> warn_redex_in_rewrite_rules (Pp.str " iota redex")
  | PLambda _ -> warn_redex_in_rewrite_rules (Pp.str " lambda pattern")
  | PApp (p, arg, _, _) -> check_pattern_redex env p; check_pattern_redex_aux env arg
  | PCase (p, _, _, (ret, _), brs) -> test_projection_apps env p; check_pattern_redex env p; check_pattern_redex_aux env (snd ret); Array.iter (snd %> check_pattern_redex_aux env) brs
  | PProj (p, _, _) -> test_projection_apps env p; check_pattern_redex env p
  | PProd (_, ty, _, bod, _, _) -> check_pattern_redex_aux env ty; check_pattern_redex_aux env bod
  | PRel _ | PInt _ | PFloat _ | PString _ | PSort _ | PInd _ | PConstr _ | PSymbol _ -> ()
and check_pattern_redex_aux env = function
  | PVar _ -> ()
  | Pat p -> check_pattern_redex env p

type pattern_translation_error =
  | UnknownEvar
  | UnknownQVar of QVar.t
  | UnknownLevel of Level.t
  | DuplicatePatVar of Evar.t * Id.t * int * int
  | DuplicateQVar of QVar.t * int * int
  | DuplicateUVar of Level.t * int * int
  | NoHeadSymbol

exception PatternTranslationError of pattern_translation_error


let update_invtbl evk id (curvar, tbl) =
  curvar, (succ curvar, tbl |> Evar.Map.update evk @@ function
  | None -> Some curvar
  | Some k as c when k = curvar -> c
  | Some k ->
      raise (PatternTranslationError (DuplicatePatVar (evk, id, k, curvar))))

let update_invtblu1 ~(alg:bool) lvl (curvaru, alg_vars, tbl) =
  curvaru, (succ curvaru, alg :: alg_vars, tbl |> Level.Map.update lvl @@ function
    | None -> Some curvaru
    | Some k as c when k = curvaru -> c
    | Some k ->
        raise (PatternTranslationError (DuplicateUVar (lvl, k, curvaru))))

let update_invtblq1 qvar (curvarq, tbl) =
  curvarq, (succ curvarq, tbl |> QVar.Map.update qvar @@ function
    | None -> Some curvarq
    | Some k as c when k = curvarq -> c
    | Some k ->
        raise (PatternTranslationError (DuplicateQVar (qvar, k, curvarq))))

let translate_quality_pattern stateq = function
  | PQConstant _ as q -> stateq, q
  | PQVar (_, false) -> stateq, PQVar None
  | PQVar (qvar, true) ->
      let qi, stateq = update_invtblq1 qvar stateq in
      stateq, PQVar (Some qi)

let translate_instance (state, stateq, stateu) (q, u) =
  let stateq, maskq = Array.fold_left_map translate_quality_pattern stateq q in
  let stateu, masku = Array.fold_left_map (fun stateu (lvl, pat) ->
      if pat then
        let ui, stateu = update_invtblu1 ~alg:false lvl stateu in
        stateu, Some ui
      else stateu, None
    ) stateu u
  in
  (state, stateq, stateu), (maskq, masku)

let translate_sort_pattern (st, sq, su as state) = function
  | PSProp | PSSProp | PSSet as sp -> state, sp
  | PSType (lvl, pat) ->
      if pat then
        let ui, su = update_invtblu1 ~alg:true lvl su in
        (st, sq, su), PSType (Some ui)
      else state, PSType None
  | PSQSort ((q, patq), (lvl, patu)) ->
      let sq, bq =
        if patq then
          let qi, sq = update_invtblq1 q sq in
          sq, Some qi
        else sq, None
      in
      let su, ba =
        if patu then
          let ui, su = update_invtblu1 ~alg:true lvl su in
          su, Some ui
        else su, None
      in
      (st, sq, su), PSQSort (bq, ba)


let rec translate_pattern state = function
  | PRel n -> state, (PHRel n, [])
  | PSort (sp, _) ->
      let state, sp = translate_sort_pattern state sp in
      state, (PHSort sp, [])
  | PSymbol (cst, mask) ->
      let state, mask = translate_instance state mask in
      state, (PHSymbol (cst, mask), [])
  | PInd (ind, mask) ->
      let state, mask = translate_instance state mask in
      state, (PHInd (ind, mask), [])
  | PConstr (cstr, mask) ->
      let state, mask = translate_instance state mask in
      state, (PHConstr (cstr, mask), [])
  | PInt i -> state, (PHInt i, [])
  | PFloat f -> state, (PHFloat f, [])
  | PString s -> state, (PHString s, [])
  | PLambda (_, arg, _, bod) ->
      let state, arg = translate_arg_pattern state arg in
      let state, bod = translate_pattern state bod in
      let lambda = begin match bod with PHLambda (args, bod), [] -> PHLambda (Array.append [|arg|] args, bod) | _ -> PHLambda ([|arg|], bod) end in
      state, (lambda, [])
  | PProd (_, arg, _, bod, _, _) ->
      let state, arg = translate_arg_pattern state arg in
      let state, bod = translate_arg_pattern state bod in
      let prod = begin match bod with ERigid (PHProd (args, bod), []) -> PHProd (Array.append [|arg|] args, bod) | _ -> PHProd ([|arg|], bod) end in
      state, (prod, [])
  | PApp (f, arg, _, _) ->
      let state, (head, elims) = translate_pattern state f in
      let state, arg = translate_arg_pattern state arg in
      let elims = begin match elims with PEApp args :: elims -> PEApp (Array.append args [|arg|]) :: elims | _ -> PEApp [|arg|] :: elims end in
      state, (head, elims)
  | PCase (c, ind, _, (ret, _), brs) ->
      let state, (head, elims) = translate_pattern state c in
      let state, ret = translate_arg_pattern state (snd ret) in
      let state, brs = Array.fold_left_map (fun state (_, br) -> translate_arg_pattern state br) state brs in
      state, (head, PECase (ind, ret, brs) :: elims)
  | PProj (c, p, _) ->
      let state, (head, elims) = translate_pattern state c in
      state, (head, PEProj p :: elims)

and translate_pattern_rev state p =
  let state, (h, e) = translate_pattern state p in
  state, (h, List.rev e)

and translate_arg_pattern (st, sq, su as state) = function
  | PVar (evk, Name id) ->
      let i, st = update_invtbl evk id st in
      (st, sq, su), EHole i
  | PVar (_, Anonymous) ->
      state, EHoleIgnored
  | Pat p ->
      let state, p = translate_pattern_rev state p in
      state, ERigid p

let translate_pattern = translate_pattern_rev

(* relocation of evars into de Bruijn indices *)
let rec evar_subst evmap evd k t =
  match kind t with
  | Evar (evk, inst) -> begin
    match Evar.Map.find_opt evk evmap with
    | None -> raise (PatternTranslationError UnknownEvar)
    | Some n ->
        let head = mkRel (n + k) in
        let (ctx, _, _, _) = Evar.Map.find evk evd in
        let args = identity_of_ctx ctx in
        let inst = inst |> SList.Smart.map (evar_subst evmap evd k) in
        let inst = inst |> SList.to_list |> List.map Option.get in
        let args = Array.map (Vars.substl inst) args in
        mkApp (head, args)
    end
  | _ -> map_with_binders succ (evar_subst evmap evd) k t

let make_usubst (qvmap, uvmap) : UVars.sort_level_subst =
  let qsubst = QVar.Map.map Quality.var qvmap in
  let usubst = Level.Map.map Level.var uvmap in
  qsubst, usubst

let test_qvar env nvarqs q =
  match Sorts.QVar.var_index q with
  | Some n when n < 0 || n > nvarqs -> CErrors.anomaly Pp.(str "Unknown sort variable in rewrite rule.")
  | Some _ -> ()
  | None ->
      if not @@ Sorts.QVar.Set.mem q env.env_qualities then
        raise (PatternTranslationError (UnknownQVar q))

let test_level env nvarus lvl =
  match Univ.Level.var_index lvl with
  | Some n when n < 0 || n > nvarus -> CErrors.anomaly Pp.(str "Unknown universe level variable in rewrite rule")
  | Some _ -> ()
  | None ->
      match UGraph.check_declared_universes (Environ.universes env) (Univ.Level.Set.singleton lvl) with
      | Ok () -> ()
      | Error l ->
        let lvl = Univ.Level.Set.choose l in (* Subsingleton of size 1 *)
        raise (PatternTranslationError (UnknownLevel lvl))



let translate_rewrite_rule env { pattern; replacement; info=Info info } =
  let empty_state = ((1, Evar.Map.empty), (0, QVar.Map.empty), (0, [], Level.Map.empty)) in
  let state, lhs_pat = translate_pattern empty_state pattern in
  let (nvars, evmap), (nvarqs, qvmap), (nvarus, _, uvmap) = state in
  let rhs = evar_subst evmap info.evar_map 0 replacement in
  let usubst = make_usubst (qvmap, uvmap) in
  let rhs = Vars.subst_univs_level_constr usubst rhs in
  let () =
    let qs, us = Vars.sort_and_universes_of_constr rhs in
    Sorts.QVar.Set.iter (test_qvar env nvarqs) qs;
    Univ.Level.Set.iter (test_level env nvarqs) us
  in
  let symb, head_umask, elims = match lhs_pat with
    | (PHSymbol (symb, mask), elims) -> symb, mask, elims
    | _ -> raise (PatternTranslationError NoHeadSymbol)
  in

  symb, { nvars = (nvars-1, nvarqs, nvarus); lhs_pat = (head_umask, elims); rhs }

let rec head_symbol = function
  | PSymbol (cst, _) -> cst
  | PApp (f, _, _, _) -> head_symbol f
  | PCase (c, _, _, _, _) -> head_symbol c
  | PProj (c, _, _) -> head_symbol c
  | PRel _ | PSort _ | PInd _ | PConstr _ | PInt _ | PFloat _ | PString _ | PLambda _ | PProd _ ->
      raise (PatternTranslationError NoHeadSymbol)
