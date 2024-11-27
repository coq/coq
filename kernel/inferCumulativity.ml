(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Declarations
open Constr
open Univ
open UVars
open Variance
open Util

let debug = CDebug.create ~name:"inferCumul" ()
let debug_infer_term = CDebug.create ~name:"inferCumul_infer_term" ()

type cumul_pb =
  | Conv | Cumul | InvCumul

let pr_cumul_pb = Pp.(function
  | Conv -> str"="
  | Cumul -> str"≤"
  | InvCumul -> str"≥")

(** Not the same as Type_errors.BadVariance because we don't have the env where we raise. *)
exception BadVariance of Level.t * VariancePos.t * VariancePos.t
(* some ocaml bug is triggered if we make this an inline record *)

exception NotInferring

type mode = Check | Infer
let pr_mode m =
  let open Pp in
  match m with
  | Check -> str"check"
  | Infer -> str"infer"

type infer_binders = (mode * (Variance.t option * int list))

type impred_qvars = UVars.impred_qvars
(** Set of potentially impredicative QVars under which the universe lives.
  If there is an occurrence under a non-impredicative QVar somewhere, this is empty. *)

type infer_variance_occurrence =
  { infer_binders : infer_binders;
    infer_term : mode * UVars.Variance.t option;
    infer_type : mode * UVars.Variance.t option;
    infer_principal : bool;
    infer_under_impred_qvars : impred_qvars }

type variances = infer_variance_occurrence Univ.Level.Map.t
let default_occ =
  { infer_binders = (Infer, (None, []));
    infer_term = (Infer, None);
    infer_type = (Infer, None);
    infer_principal = false;
    infer_under_impred_qvars = None }

let make_checked_occ ~infer_in_type
  UVars.VarianceOccurrence.{ in_binders; in_term; in_type; under_impred_qvars } =
  { infer_binders = ((if infer_in_type then Infer else Check), in_binders);
    infer_term = Check, in_term;
    infer_type = (if infer_in_type then Infer else Check), in_type;
    infer_principal = false (* ignored when checking *);
    infer_under_impred_qvars = under_impred_qvars }

let forget_infer_variance_occurrence
  { infer_binders; infer_term; infer_type; infer_principal = _; infer_under_impred_qvars = impred_qvars } =
  UVars.VarianceOccurrence.{ in_binders = snd infer_binders;
    in_term = snd infer_term;
    in_type = snd infer_type;
    under_impred_qvars = impred_qvars }

let of_variance_occurrences ~infer_in_type (vs : (Level.t * UVars.VarianceOccurrence.t option) array) : variances =
  Array.fold_left (fun vs (l, vocc) ->
    Level.Map.add l (Option.cata (make_checked_occ ~infer_in_type) default_occ vocc) vs) Level.Map.empty vs

let pr_variance_occurrence (occ : infer_variance_occurrence) =
  let open Pp in
  let pr_binders (m, (v, bs)) =
    if List.is_empty bs then [] else
    [spc () ++ pr_mode m ++ str":" ++ pr_opt Variance.pr v ++ spc () ++ str "in" ++ spc () ++
      prlist_with_sep pr_comma (fun i -> pr_nth (succ i)) bs ++ str (String.plural (List.length bs) " binder")] in
  let pr_term (m, v) = [spc () ++ pr_mode m ++ str": " ++ pr_opt Variance.pr v ++ str" in term"] in
  let pr_type (m, v) = [spc () ++ pr_mode m ++ str": " ++ pr_opt Variance.pr v ++ str" in type"] in
  let pr_principal = if occ.infer_principal then [str"in principal type"] else [] in
  let pr_impred =
    match occ.infer_under_impred_qvars with
    | Some _ as x -> [UVars.pr_impred_qvars x]
    | None -> []
  in
  let variances = pr_binders occ.infer_binders @ pr_term occ.infer_term @ pr_type occ.infer_type @ pr_principal @ pr_impred in
    if List.is_empty variances then mt ()
    else hov 0 (str"(" ++ prlist_with_sep pr_comma identity variances ++ str")")

let make_infer_occ (variance, position) =
  let open Position in
  match position with
  | InBinder i ->
    { default_occ with infer_binders = (Check, (Some variance, [i])) }
  | InType ->
    { default_occ with infer_type = Check, Some variance }
  | InTerm ->
    { default_occ with infer_term = Check, Some variance }

(** Level variances *)

(* The position records the last position in the term where the variable was used relevantly. *)

let empty_variances = Univ.Level.Map.empty
let is_empty_variances = Univ.Level.Map.is_empty

let pr_variances prl variances =
  Univ.Level.Map.pr prl pr_variance_occurrence variances

let mode_sup x y =
  match x, y with
  | Check, _ -> Check
  | _, Check -> Check
  | Infer, Infer -> Infer

let rec union_binders l1 l2 =
  match l1, l2 with
  | [], l2 -> l2
  | l1, [] -> l1
  | i1 :: t1, i2 :: t2 ->
    let c = Int.compare i1 i2 in
    if Int.equal c 0
    then i1 :: union_binders t1 t2
    else if c <= 0
    then i1 :: union_binders t1 l2
    else i2 :: union_binders l1 t2

let sup_occs { infer_binders = (mode, (bindersv, binders)); infer_term; infer_type; infer_principal; infer_under_impred_qvars }
  { infer_binders = (mode', (bindersv', binders')); infer_term = infer_term';
    infer_type = infer_type'; infer_principal = infer_principal';
    infer_under_impred_qvars = infer_under_impred_qvars' } =
  let infer_binders = (mode_sup mode mode', (Option.union Variance.sup bindersv bindersv', union_binders binders binders')) in
  let mode_var_sup (mode, v) (mode', v') = (mode_sup mode mode', Option.union Variance.sup v v') in
  let infer_term = mode_var_sup infer_term infer_term' in
  let infer_type = mode_var_sup infer_type infer_type' in
  let infer_principal = infer_principal || infer_principal' in
  let infer_under_impred_qvars = union_impred_qvars infer_under_impred_qvars infer_under_impred_qvars' in
  { infer_binders; infer_term; infer_type; infer_principal; infer_under_impred_qvars }

let union_variances : variances -> variances -> variances =
  let union _ x y = Some (sup_occs x y) in
  Univ.Level.Map.union union

let sup_vopt x y =
  match x, y with
  | None, None -> x
  | Some _, None -> x
  | None, Some _ -> y
  | Some v, Some v' -> Some (UVars.Variance.sup v v')

let max_binder = function
  | [] -> None
  | v :: vs -> Some (List.fold_left max v vs)
let binder_pos (infer_binders, pos) =
  match infer_binders with
  | None -> None
  | Some v ->
    match max_binder pos with
    | None -> None
    | Some i -> Some (i, v)

let occurrence_to_variance_pos
  ({ infer_binders = (modeb, infer_binders); infer_term = (modet, infer_term);
     infer_type = (modety, infer_type); infer_principal = _;
     infer_under_impred_qvars = _ } : infer_variance_occurrence) =
  let open Position in
  let binders = binder_pos infer_binders in
  match binders, infer_term, infer_type with
  | in_binder, Some v, _ when (v <> Variance.Irrelevant) ->
     (mode_sup modeb modet, (Option.get (sup_vopt (Option.map snd in_binder) (Some v)), InTerm))
  | Some (i, v), _, _ when v <> Irrelevant -> (modeb, (v, InBinder i))
  | _, _, infer_type -> (modety, (Option.default Irrelevant infer_type, InType))

let term_type_variances
  ({ infer_binders = (_, (infer_binders, _)); infer_term = (_, infer_term); infer_type = (_, infer_type);
     infer_principal; infer_under_impred_qvars = _ } : infer_variance_occurrence) =
  let sup_opt x y =
    match x, y with
    | None, None -> x
    | Some _, None -> x
    | None, Some _ -> y
    | Some v, Some v' -> Some (UVars.Variance.sup v v')
  in
  infer_term, sup_opt infer_binders infer_type, infer_principal

let binders_term_and_type_variances ({ infer_binders = (_, (infer_binders, _)); infer_term = (_, infer_term);
  infer_type = (_, infer_type); infer_principal; infer_under_impred_qvars = _ } : infer_variance_occurrence) =
  let sup_opt x y =
    match x, y with
    | None, None -> x
    | Some _, None -> x
    | None, Some _ -> y
    | Some v, Some v' -> Some (UVars.Variance.sup v v')
  in
  sup_opt infer_binders infer_term, infer_type, infer_principal


type pre_variances = (Univ.Level.t * VarianceOccurrence.t option) array
type infer_variance_occurrences = infer_variance_occurrence array

module Inf : sig
  type status

  val pr : (Level.t -> Pp.t) -> status -> Pp.t

  val infer_level_eq : principal:bool -> impred_qvars -> Level.t -> status -> status
  val infer_level_leq : principal:bool -> impred_qvars -> Level.t -> status -> status
  val infer_level_geq : principal:bool -> impred_qvars -> Level.t -> status -> status
  val infer_level_principal : impred_qvars -> Level.t -> status -> status

  val get_infer_mode : status -> bool
  val set_infer_mode : bool -> status -> status

  val set_position : Position.t -> status -> status
  val get_position : status -> Position.t

  val start : infer_in_type:bool -> pre_variances -> Position.t -> status
  val start_variances : variances -> Position.t -> status

  val start_inference : Level.Set.t -> Position.t -> status

  val inferred : status -> variances
  val finish : Environ.env -> status -> UVars.variances

end = struct

  (**
     Each local universe is either in the [univs] map or is Invariant.

     If [univs] is empty all universes are Invariant and there is nothing more to do,
     so we stop by raising [TrivialVariance]. The [soft] check comes before that.
  *)
  type status = {
    orig_array : pre_variances;
    univs : variances;
    infer_mode : bool;
    position : Position.t;
  }

  let get_infer_mode v = v.infer_mode
  let set_infer_mode b v = if v.infer_mode == b then v else {v with infer_mode=b}

  let get_position v = v.position
  let set_position p v = if v.position == p then v else {v with position=p}

  let get_variance_at_position variances u =
    match Level.Map.find_opt u variances.univs with
    | None -> None
    | Some occ ->
      let open Position in
      match variances.position with
      | InBinder _ ->
        let (mode, (v, _)) = occ.infer_binders in
        Some (mode, Option.default Irrelevant v)
      | InTerm -> let (mode, v) = occ.infer_term in
        Some (mode, Option.default Irrelevant v)
      | InType -> let (mode, v) = occ.infer_type in
        Some (mode, Option.default Irrelevant v)

  let update_binder_variance (_, binders) i variance =
    let rec aux binders =
      match binders with
      | [] -> [i]
      | i' :: binders' ->
        match Int.compare i i' with
        | 0 -> i :: binders'
        | x when x < 0 -> i :: binders
        | _ -> i' :: aux binders'
    in (Some variance, aux binders)

  let update_variance ~principal variances q u variance =
    let upd = function
      | None -> assert false
      | Some occs ->
        let open Position in
        let infer_principal = principal || occs.infer_principal in
        let infer_under_impred_qvars = union_impred_qvars occs.infer_under_impred_qvars q in
        let occs' = match variances.position with
        | InBinder i ->
          let (mode, binders) = occs.infer_binders in
          { occs with infer_binders = (mode, update_binder_variance binders i variance); infer_principal;
            infer_under_impred_qvars }
        | InTerm ->
          let (mode, _) = occs.infer_term in
          { occs with infer_term = (mode, Some variance); infer_principal; infer_under_impred_qvars }
        | InType ->
          let (mode, _) = occs.infer_type in
          { occs with infer_type = (mode, Some variance); infer_principal; infer_under_impred_qvars }
        in Some occs'
    in {variances with univs = Level.Map.update u upd variances.univs}


  let set_principal q u variances =
    let upd = function
      | None -> None
      | Some occ -> Some { occ with infer_principal = true; infer_under_impred_qvars = union_impred_qvars occ.infer_under_impred_qvars q }
    in
    { variances with univs = Level.Map.update u upd variances.univs }

  let infer_level_cmp ~principal q variance u variances =
    match get_variance_at_position variances u with
    | None -> variances
    | Some (Check, expected) ->
      if Variance.le variance expected then variances
      else raise (BadVariance (u, (expected, variances.position), (variance, variances.position)))
    | Some (Infer, inferred) ->
      if not variances.infer_mode then raise NotInferring;
      update_variance ~principal variances q u (Variance.sup inferred variance)

  let infer_level_eq ~principal q u variances = infer_level_cmp ~principal q Invariant u variances
  let infer_level_leq ~principal q u variances = infer_level_cmp ~principal q Covariant u variances
  let infer_level_geq ~principal q u variances = infer_level_cmp ~principal q Contravariant u variances
  let infer_level_principal q u variances = set_principal q u variances

  let start ~infer_in_type univs position =
    { univs = of_variance_occurrences ~infer_in_type univs; orig_array = univs; infer_mode = true; position}

  let start_variances univs position =
    { univs; orig_array = [| |]; infer_mode = true; position}

  let start_inference levels position =
    let univs = Level.Set.fold (fun level -> Level.Map.add level default_occ) levels Level.Map.empty in
    { univs; orig_array = [||]; infer_mode=true; position}

let variance_occurrence_to_variance_pos VarianceOccurrence.{ in_binders; in_term; in_type; under_impred_qvars = _ } =
  let open Position in
  let binders = binder_pos in_binders in
  match binders, in_term, in_type with
  | in_binder, Some v, _ when (v <> Variance.Irrelevant) -> (Option.get (sup_vopt (Option.map snd in_binder) (Some v)), InTerm)
  | Some (i, v), _, _ when v <> Irrelevant -> (v, InBinder i)
  | _, _, in_type -> (Option.default Irrelevant in_type, InType)

  let variance_of_occ u expected occ =
    let imode, inferred = occurrence_to_variance_pos occ in
    match expected with
    | None -> inferred
    | Some expected ->
      let expectedvpos = variance_occurrence_to_variance_pos expected in
      if imode == Infer || VariancePos.le inferred expectedvpos then expectedvpos
      else raise (BadVariance (u, expectedvpos, inferred))

  let to_variance_opt u expected o =
    Option.cata (fun occ -> variance_of_occ u expected occ) (Irrelevant,Position.InTerm) o

  let inferred variances = variances.univs

  let pr prl status = pr_variances prl status.univs

  let finish env variances =
    try
      let arr =
        Array.map
          (fun (u,expected) ->
            let occ = Level.Map.find_opt u variances.univs in
            Option.default VarianceOccurrence.default_occ (Option.map forget_infer_variance_occurrence occ),
            to_variance_opt u expected occ)
          variances.orig_array
      in
      let vs, apps = Array.split arr in
      Variances.make_full vs (ApplicationVariances.of_array apps)
  with BadVariance (lev, expected, actual) ->
    Type_errors.error_bad_variance env ~lev ~expected ~actual

end
open Inf

let infer_generic_instance_eq variances u =
  Array.fold_left (fun variances u ->
    Level.Set.fold (fun l -> infer_level_eq ~principal:true None l) (Universe.levels u) variances)
    variances u

let instance_univs u = snd (Instance.to_array u)

let extend_con_instance cb u =
  Instance.append (Instance.of_level_instance cb.const_univ_hyps) u

let extend_ind_instance mib u =
  Instance.append (Instance.of_level_instance mib.mind_univ_hyps) u

let extended_mind_variance mind =
  match Declareops.universes_variances mind.mind_universes, mind.mind_sec_variance with
  | None, None -> None
  | Some _ as variance, None -> variance
  | None, Some _ -> assert false
  | Some variance, Some sec_variance -> Some (UVars.Variances.append sec_variance variance)

let extended_const_variance cb =
  match Declareops.universes_variances cb.const_universes, cb.const_sec_variance with
  | None, None -> None
  | Some _ as variance, None -> variance
  | None, Some _ -> assert false
  | Some variance, Some sec_variance -> Some (UVars.Variances.append sec_variance variance)

let compute_impred_qvars qs vocc =
  let vars = UVars.VarianceOccurrence.under_impred_qvars vocc in
  update_impred_qvars (fun qv -> Option.map (fun idx -> qs.(idx)) (Sorts.QVar.var_index qv)) vars

let infer_cumulative_instance cv_pb nargs gvariances variances u =
  let qs, us = Instance.to_array u in
  debug_infer_term Pp.(fun () -> str"infer_cumulative_instance: " ++ Variances.pr gvariances);
  Array.fold_left2 (fun variances vocc u ->
    let variance, principal = VarianceOccurrence.variance_and_principality_app nargs vocc in
    let q = compute_impred_qvars qs vocc in
    match cv_pb, variance with
    | _, Irrelevant ->
      if principal then Level.Set.fold (infer_level_principal q) (Universe.levels u) variances else variances
    | _, Invariant
    | Conv, (Covariant | Contravariant) ->
      (* Co/contravariant in invariant position, becomes invariant *)
      Level.Set.fold (infer_level_eq ~principal q) (Universe.levels u) variances
    | Cumul, Covariant ->
      (* Covariant in covariant position -> covariant *)
      Level.Set.fold (infer_level_leq ~principal q) (Universe.levels u) variances
    | Cumul, Contravariant ->
      (* Contravariant in covariant position -> contravariant *)
      Level.Set.fold (infer_level_geq ~principal q) (Universe.levels u) variances
    | InvCumul, Contravariant ->
      (* Contravariant in contravariant position -> covariant *)
      Level.Set.fold (infer_level_leq ~principal q) (Universe.levels u) variances
    | InvCumul, Covariant ->
      (* Covariant in contravariant position -> contravariant *)
      Level.Set.fold (infer_level_geq ~principal q) (Universe.levels u) variances)
    variances
    (Variances.repr gvariances)
    us

let infer_inductive_instance cv_pb env variances ind nargs u =
  if not (Environ.mem_mind (fst ind) env) then
    infer_generic_instance_eq variances (instance_univs u)
  else
  let mind = Environ.lookup_mind (fst ind) env in
  let u = extend_ind_instance mind u in
  match extended_mind_variance mind with
  | None -> infer_generic_instance_eq variances (instance_univs u)
  | Some mind_variance -> infer_cumulative_instance cv_pb (UVars.NumArgs nargs) mind_variance variances u

let constructor_variances _mind _ind _ctor variance =
  (* let npars = mind.Declarations.mind_nparams in *)
  (* let nargs = mind.Declarations.mind_packets.(ind).Declarations.mind_consnrealargs.(ctor - 1) in *)
  let open VarianceOccurrence in
  let map vocc = { vocc with in_type = vocc.in_term; in_term = None } in
  Variances.make (Array.map map (Variances.repr variance))

let infer_constructor_instance_eq env variances ((mi,ind),ctor) nargs u =
  if not (Environ.mem_mind mi env) then
    infer_generic_instance_eq variances (instance_univs u)
  else
  let mind = Environ.lookup_mind mi env in
  let u = extend_ind_instance mind u in
  match extended_mind_variance mind with
  | None -> infer_generic_instance_eq variances (instance_univs u)
  | Some mind_variance ->
    let cstr_variance = constructor_variances mind ind ctor mind_variance in
    infer_cumulative_instance Cumul (UVars.NumArgs nargs) cstr_variance variances u

    (*if not (Int.equal (UCompare.constructor_cumulativity_arguments (mind, ind, ctor)) nargs)
    then infer_generic_instance_eq variances u
    else variances (* constructors are convertible at common supertype *) *)

let infer_sort cv_pb variances s =
  let impred_qvars = Some (impred_qvars_of_quality (Sorts.quality s)) in
  let levels = Sorts.levels s in
  match cv_pb with
  | Conv ->
    Level.Set.fold (infer_level_eq ~principal:true impred_qvars) levels variances
  | Cumul ->
    Level.Set.fold (infer_level_leq ~principal:true impred_qvars) levels variances
  | InvCumul ->
    Level.Set.fold (infer_level_geq ~principal:true impred_qvars) levels variances

let infer_constant cv_pb env nargs variances has_def (con,u) =
  let cb = Environ.lookup_constant con env in
  let u = extend_con_instance cb u in
  match extended_const_variance cb with
  | None ->
    let variances = if has_def then set_infer_mode false variances else variances in
    infer_generic_instance_eq variances (instance_univs u)
  | Some cst_variance -> infer_cumulative_instance cv_pb nargs cst_variance variances u

let whd_stack (infos, tab) hd stk = CClosure.whd_stack infos tab hd stk

let flip_pb = function
  | Conv -> Conv
  | Cumul -> InvCumul
  | InvCumul -> Cumul

let rec infer_fterm cv_pb infos variances hd stk =
  Control.check_for_interrupt ();
  let hd,stk = whd_stack infos hd stk in
  let open CClosure in
  debug_infer_term Pp.(fun () -> str"infer_fterm " ++ pr_mode (if Inf.get_infer_mode variances then Infer else Check) ++  Position.pr (Inf.get_position variances) ++ str", cv_pb = " ++ pr_cumul_pb cv_pb ++ str" term: " ++ Constr.debug_print (CClosure.term_of_fconstr hd));
  let push_relevance (infos, tab) n = (push_relevance infos n, tab) in
  let push_relevances (infos, tab) n = (push_relevances infos n, tab) in
  match fterm_of hd with
  | FAtom a ->
    begin match kind a with
      | Sort s -> infer_sort cv_pb variances s
      | Meta _ -> infer_stack infos variances stk
      | _ -> assert false
    end
  | FEvar (_, _, usubs, _) ->
    let variances = infer_generic_instance_eq variances (instance_univs (snd usubs))in
    infer_stack infos variances stk
  | FRel _ -> infer_stack infos variances stk
  | FInt _ -> infer_stack infos variances stk
  | FFloat _ -> infer_stack infos variances stk
  | FString _ -> infer_stack infos variances stk
  | FFlex Names.(RelKey _ | VarKey _ as fl) ->
    (* We could try to lazily unfold but then we have to analyse the
       universes in the bodies, not worth coding at least for now. *)
    begin match unfold_ref_with_args (fst infos) (snd infos) fl stk with
    | Some (hd,stk) -> infer_fterm cv_pb infos variances hd stk
    | None -> infer_stack infos variances stk
    end
  | FFlex (Names.ConstKey con as fl) ->
    begin
      if not (Environ.mem_constant (fst con) (info_env (fst infos))) then
        let variances = infer_generic_instance_eq variances (snd (Instance.to_array (snd con))) in
        let variances = infer_stack infos variances stk in
        variances
      else
      let def = unfold_ref_with_args (fst infos) (snd infos) fl stk in
      try
        let infer_mode = get_infer_mode variances in
        let nargs = stack_args_size stk in
        let variances = infer_constant cv_pb (info_env (fst infos)) (UVars.NumArgs nargs) variances (Option.has_some def) con in
        let variances = infer_stack infos variances stk in
        set_infer_mode infer_mode variances
      with BadVariance _ | NotInferring as e ->
      match def with
      | None -> raise e
      | Some (hd,stk) ->
        debug_infer_term Pp.(fun () -> str"expanding constant: " ++ Names.GlobRef.print (Names.GlobRef.ConstRef (fst con)));
        infer_fterm cv_pb infos variances hd stk
    end
  | FProj (_,_,c) ->
    let variances = infer_fterm Conv infos variances c [] in
    infer_stack infos variances stk
  | FLambda _ ->
    let (na,ty,bd) = destFLambda mk_clos hd in
    let variances = infer_fterm (flip_pb cv_pb) infos variances ty [] in
    infer_fterm cv_pb (push_relevance infos na) variances bd []
  | FProd (na,dom,codom,e) ->
    let na = usubst_binder e na in
    let variances = infer_fterm (flip_pb cv_pb) infos variances dom [] in
    infer_fterm cv_pb (push_relevance infos na) variances (mk_clos (CClosure.usubs_lift e) codom) []
  | FInd (ind, u) ->
    let variances =
      let nargs = stack_args_size stk in
      infer_inductive_instance cv_pb (info_env (fst infos)) variances ind nargs u
    in
    infer_stack infos variances stk
  | FConstruct (ctor,u) ->
    let variances =
      let nargs = stack_args_size stk in
      infer_constructor_instance_eq (info_env (fst infos)) variances ctor nargs u
    in
    infer_stack infos variances stk
  | FFix ((_,(na,tys,cl)),e) | FCoFix ((_,(na,tys,cl)),e) ->
    let n = Array.length cl in
    let variances = infer_vect infos variances Conv (Array.map (mk_clos e) tys) in
    let le = CClosure.usubs_liftn n e in
    let variances =
      let na = Array.map (usubst_binder e) na in
      let infos = push_relevances infos na in
      infer_vect infos variances Conv (Array.map (mk_clos le) cl)
    in
    infer_stack infos variances stk
  | FArray (u,elemsdef,ty) -> (* False? Not implemnting irrelevance *)
    let variances = infer_generic_instance_eq variances (instance_univs u) in
    let variances = infer_fterm Conv infos variances ty [] in
    let elems, def = Parray.to_array elemsdef in
    let variances = infer_fterm Conv infos variances def [] in
    let variances = infer_vect infos variances Conv elems in
    infer_stack infos variances stk

  | FCaseInvert (_, _, _, p, _, _, br, e) ->
    infer_case infos variances cv_pb p br e
  (* Removed by whnf *)
  | FLOCKED | FCaseT _ | FLetIn _ | FApp _ | FLIFT _ | FCLOS _ -> assert false
  | FIrrelevant -> assert false (* TODO: use create_conv_infos below and use it? *)

and infer_case infos variances cv_pb p br e =
  let open CClosure in
  let push_relevances (infos, tab) n = (push_relevances infos n, tab) in
  let orig_pos = get_position variances in
  debug Pp.(fun () -> str"computing variance of case with conv_pb = " ++ pr_cumul_pb cv_pb ++ str " and position " ++ Position.pr orig_pos);
  (* let variances =
    if cv_pb == Cumul && orig_pos == Position.InTerm then
      set_position Position.InType variances
    else variances
   *)
  let variances =
    let (ctx, arity), _r = p in
    let ctx = Array.map (usubst_binder e) ctx in
    let infos = push_relevances infos ctx in
    let e = CClosure.usubs_liftn (Array.length ctx) e in
    infer_fterm cv_pb infos variances (mk_clos e arity) [] in
  let variances = set_position orig_pos variances in
  let infer_br br variances =
    let (ctx, body) = br in
    let ctx = Array.map (usubst_binder e) ctx in
    let infos = push_relevances infos ctx in
    let e = CClosure.usubs_liftn (Array.length ctx) e in
    infer_fterm cv_pb infos variances (mk_clos e body) []
  in
  Array.fold_right infer_br br variances

and infer_stack infos variances (stk:CClosure.stack) =
  match stk with
  | [] -> variances
  | z :: stk ->
    let open CClosure in
    let variances = match z with
      | Zapp v -> infer_vect infos variances Conv v
      | Zproj _ -> variances
      | Zfix (fx,a) ->
        let variances = infer_fterm Conv infos variances fx [] in
        infer_stack infos variances a
      | ZcaseT (_,_,_,p,br,e) ->
        infer_case infos variances Conv p br e
      | Zshift _ -> variances
      | Zupdate _ -> variances
      | Zprimitive (_,_,rargs,kargs) ->
        let variances = List.fold_left (fun variances c -> infer_fterm Conv infos variances c []) variances rargs in
        let variances = List.fold_left (fun variances (_,c) -> infer_fterm Conv infos variances c []) variances kargs in
        variances
    in
    infer_stack infos variances stk

and infer_vect infos variances cv_pb v =
  Array.fold_left (fun variances c -> infer_fterm cv_pb infos variances c []) variances v

let infer_infos env ~evars =
  let open CClosure in
  let reds = RedFlags.red_add_transparent RedFlags.betaiotazeta TransparentState.full in
  (create_clos_infos reds ~evars env, create_tab ())

let infer_term cv_pb env ~evars variances c =
  let infos = infer_infos env ~evars in
  infer_fterm cv_pb infos variances (CClosure.inject c) []

let infer_named_context env ~evars variances ctx =
  let infer_typ typ (env, i, variances) =
    let variances = Inf.set_position (Position.InBinder i) variances in
    match typ with
    | Context.Named.Declaration.LocalAssum (_, typ') ->
      (Environ.push_named typ env, succ i,
       infer_term InvCumul env ~evars variances typ')
    | Context.Named.Declaration.LocalDef _ ->
      (Environ.push_named typ env, i, variances)
      (* Skip let-bound variables *)
  in
  let _env, sec_binders, variances = Context.Named.fold_outside infer_typ ctx ~init:(env, 0, variances) in
  sec_binders, variances

let infer_context env ~evars ?(shift = 0) variances ctx =
  let infer_typ typ (env, i, variances) =
    let variances = Inf.set_position (Position.InBinder i) variances in
    match typ with
    | Context.Rel.Declaration.LocalAssum (_, typ') ->
      (Environ.push_rel typ env, succ i,
       infer_term InvCumul env ~evars variances typ')
    | Context.Rel.Declaration.LocalDef _ -> assert false
  in
  let env, _, variances = Context.Rel.fold_outside infer_typ ctx ~init:(env, shift, variances) in
  env, variances

let whd_decompose_lambda env ?(evars = CClosure.default_evar_handler env) c =
  let open Context.Rel.Declaration in
  let infos = infer_infos env ~evars in
  let rec decrec env m c =
    let t = CClosure.whd_val (fst infos) (snd infos) (CClosure.inject c) in
    match kind t with
      | Lambda (n,a,c0) ->
          let d = LocalAssum (n,a) in
          decrec (Environ.push_rel d env) (Context.Rel.add d m) c0
      | _ -> m,t
  in
  decrec env Context.Rel.empty c

let whd_decompose_prod env ?(evars = CClosure.default_evar_handler env) c =
    let open Context.Rel.Declaration in
    let infos = infer_infos env ~evars in
    let rec decrec env m c =
      let t = CClosure.whd_val (fst infos) (snd infos) (CClosure.inject c) in
      match kind t with
        | Prod (n,a,c0) ->
            let d = LocalAssum (n,a) in
            decrec (Environ.push_rel d env) (Context.Rel.add d m) c0
        | _ -> m,t
    in
    decrec env Context.Rel.empty c

let infer_body env ~evars ~shift variances body =
  let ctx, body = whd_decompose_lambda ~evars env body in
  let env, variances = infer_context env ~evars ~shift variances ctx in
  let variances = Inf.set_position Position.InTerm variances in
  infer_term Cumul env ~evars variances body

let infer_type env ~evars ?(shift = 0) variances arcn =
  let ctx, codom = whd_decompose_prod ~evars env arcn in
  let env, variances = infer_context env ~evars ~shift variances ctx in
  let variances = Inf.set_position Position.InType variances in
  infer_term Cumul env ~evars variances codom

let infer_definition_core env ?(evars = CClosure.default_evar_handler env) ~infer_in_type ?in_ctx ~typ ?body variances =
  let shift, variances =
    match in_ctx with
    | None -> 0, Inf.start ~infer_in_type variances Position.InType
    | Some ctx ->
      let shift = Context.Named.nhyps ctx in
      let variances = Inf.start ~infer_in_type (Array.map (fun (l, occ) -> (l, Option.map (VarianceOccurrence.lift shift) occ)) variances) Position.InType in
      infer_named_context env ~evars variances ctx
  in
  debug Pp.(fun () -> str"infer_definition: " ++ Inf.pr Level.raw_pr variances ++
    str" in type: " ++ Constr.debug_print typ ++ spc () ++
    str " and body; " ++ pr_opt Constr.debug_print body);
  let variances = infer_type env ~evars ~shift variances typ in
  debug Pp.(fun () -> str"infer_definition after type: " ++ Inf.pr Level.raw_pr variances);
  let variances = Option.cata (infer_body env ~evars ~shift variances) variances body in
  debug Pp.(fun () -> str"infer_definition finished with: " ++ Inf.pr Level.raw_pr variances);
  shift, Inf.finish env variances

let infer_definition env ?(evars = CClosure.default_evar_handler env) ?(infer_in_type=false) ?in_ctx ~typ ?body variances =
  try infer_definition_core env ~evars ~infer_in_type ?in_ctx ~typ ?body variances
  with BadVariance (lev, expected, actual) ->
    Type_errors.error_bad_variance env ~lev ~expected ~actual

let infer_arity_constructor is_arity env ~evars ?(shift = 0) variances arcn =
  let infer_typ typ (env, i, variances) =
    let variances = if is_arity then Inf.set_position (Position.InBinder i) variances else variances in
    match typ with
    | Context.Rel.Declaration.LocalAssum (_, typ') ->
      (Environ.push_rel typ env, succ i,
       infer_term (if is_arity then InvCumul else Cumul) env ~evars variances typ')
    | Context.Rel.Declaration.LocalDef _ -> assert false
  in
  let typs, codom = Reduction.whd_decompose_prod ~evars env arcn in
  let env, _, variances = Context.Rel.fold_outside infer_typ typs ~init:(env, shift, variances) in
  (* If we have Inductive foo@{i j} : ... -> Type@{i} := C : ... -> foo Type@{j}
     i is irrelevant, j is invariant. *)
  if not is_arity then
    let variances = Inf.set_position Position.InTerm variances in
    infer_term Cumul env ~evars variances codom
  else variances

let infer_inductive_core ~env_params ~env_ar_par ~evars ~arities ~ctors univs =
  let variances = Inf.start ~infer_in_type:false univs Position.InType in
  let variances = List.fold_left (fun variances arity ->
      infer_arity_constructor true env_params ~evars variances arity)
      variances arities
  in
  let variances = Inf.set_position Position.InTerm variances in
  let variances = List.fold_left
      (List.fold_left (infer_arity_constructor false env_ar_par ~shift:0 ~evars))
      variances ctors
  in
  Inf.finish env_params variances

let infer_inductive ~env_params ~env_ar_par ?(evars = CClosure.default_evar_handler env_params) ~arities ~ctors univs =
  try infer_inductive_core ~env_params ~env_ar_par ~evars ~arities ~ctors univs
  with
  | BadVariance (lev, expected, actual) ->
    Type_errors.error_bad_variance env_params ~lev ~expected ~actual
