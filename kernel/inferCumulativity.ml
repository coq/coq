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

type variance_occurrence =
  { in_binder : (int * UVars.Variance.t) option;
    in_term : UVars.Variance.t option;
    in_type : UVars.Variance.t option }

let _lift_variance_occurrence n occ =
  { occ with in_binder = Option.map (fun (i, v) -> (i + n, v)) occ.in_binder }

let pr_variance_occurrence { in_binder; in_term; in_type } =
  let open Pp in
  let pr_binder =
    match in_binder with
    | None -> mt()
    | Some (i, variance) -> str": " ++ UVars.Variance.pr variance ++ str " in " ++ pr_nth (i+1) ++ str" binder"
  in
  let pr_in_type =
    match in_type with
  | None -> pr_binder
  | Some variance -> pr_binder ++ (if Option.is_empty in_binder then str": " else str", ") ++ UVars.Variance.pr variance ++ str " in type"
  in
  match in_term with
  | None -> pr_in_type
  | Some variance -> pr_in_type ++ (if Option.is_empty in_binder && Option.is_empty in_type then str": " else str", ") ++ UVars.Variance.pr variance ++ str " in term"

let default_occ =
  { in_binder = None; in_term = None; in_type = None }

let make_occ (variance, position) =
  let open Position in
  match position with
  | InBinder i ->
    { in_binder = Some (i, variance); in_term = None; in_type = Some Invariant }
  | InType ->
    { in_binder = Some (-1, variance); in_type = Some variance; in_term = None }
  | InTerm ->
    { in_binder = Some (-1, variance); in_type = Some Invariant; in_term = Some variance }

(** Level variances *)

(* The position records the last position in the term where the variable was used relevantly. *)

type variances = (mode * variance_occurrence) Univ.Level.Map.t

let empty_variances = Univ.Level.Map.empty
let is_empty_variances = Univ.Level.Map.is_empty

let sup_occs { in_binder; in_term; in_type } { in_binder = in_binder'; in_term = in_term'; in_type = in_type' } =
  let in_binder = Option.union (fun (i, v) (i', v') -> (max i i', Variance.sup v v')) in_binder in_binder' in
  let in_term = Option.union Variance.sup in_term in_term' in
  let in_type = Option.union Variance.sup in_type in_type' in
  { in_binder; in_term; in_type }

let mode_sup x y =
  match x, y with
  | Check, _ -> Check
  | _, Check -> Check
  | Infer, Infer -> Infer

let union_variances : variances -> variances -> variances =
  let union _ (mode, occ) (mode', occ') = Some (mode_sup mode mode', sup_occs occ occ') in
  Univ.Level.Map.union union

let pr_variances prl variances =
  let open Pp in
  let prmocc (mode, occ) =
    let pr_mode = function Infer -> str" infer:" | Check -> str" check:" in
    pr_mode mode ++ pr_variance_occurrence occ
  in
  Univ.Level.Map.pr prl prmocc variances

let position_variance_sup mode infer_mode u ({ in_binder; in_term; in_type } as o) (variance, position as vp) =
  let open Variance in
  let open Position in
  debug Pp.(fun () -> str"position_variance_sup: " ++ Level.raw_pr u ++ pr_variance_occurrence o ++ str", " ++ VariancePos.pr vp);
  match variance with
  | Irrelevant -> o (* The new variance is irrelevant, we keep record of the last relevant positions *)
  | _ ->
    match position with
    | InBinder i ->
      (match in_binder with
      | Some (i', old_variance) ->
        (match mode with
        | Infer ->
          if not infer_mode then raise NotInferring;
          { o with in_binder = Some (max i i', Variance.sup old_variance variance) }
        | Check ->
          if not (Variance.le variance old_variance) then
            raise (BadVariance (u, (old_variance, InBinder i'), vp))
          else o)
      | None ->
        (match mode with
         | Infer ->
          if not infer_mode then raise NotInferring;
          { o with in_binder = Some (i, variance) }
         | Check -> raise (BadVariance (u, (Irrelevant, InBinder i), vp))))
    | InType ->
        (match in_type with
        | Some old_variance ->
          (match mode with
          | Infer ->
            if not infer_mode then raise NotInferring;
            { o with in_type = Some (Variance.sup variance old_variance) }
          | Check ->
            if not (Variance.le variance old_variance) then
              raise (BadVariance (u, (old_variance, InType), vp))
            else o)
        | None ->
          (match mode with
          | Infer -> { o with in_type = Some variance }
          | Check -> raise (BadVariance (u, (Irrelevant, InType), vp))))
    | InTerm ->
      (match in_term with
      | Some old_variance ->
        (match mode with
        | Infer ->
          if not infer_mode then raise NotInferring;
          { o with in_term = Some (Variance.sup variance old_variance) }
        | Check ->
          if not (Variance.le variance old_variance) then
            raise (BadVariance (u, (old_variance, InType), vp))
          else o)
      | None ->
        (match mode with
        | Infer -> { o with in_term = Some variance }
        | Check -> raise (BadVariance (u, (Irrelevant, InType), vp))))

let term_type_variances { in_binder; in_term; in_type } =
  let in_binder = Option.map snd in_binder in
  let sup_opt x y =
    match x, y with
    | None, None -> x
    | Some _, None -> x
    | None, Some _ -> y
    | Some v, Some v' -> Some (UVars.Variance.sup v v')
  in
  in_term, sup_opt in_binder in_type

let min_pos_variance position { in_binder; in_term; in_type } =
  let open Position in
  match position with
  | InBinder i ->
    (match in_binder with
    | Some (i', v) when Int.equal i i' -> Some v
    | Some (_, v) -> Some v
    | None -> None)
  | InTerm -> in_term
  | InType -> in_type


module Inf : sig
  type status

  val pr : (Level.t -> Pp.t) -> status -> Pp.t

  val infer_level_eq : Level.t -> status -> status
  val infer_level_leq : Level.t -> status -> status
  val infer_level_geq : Level.t -> status -> status

  val get_infer_mode : status -> bool
  val set_infer_mode : bool -> status -> status

  val set_position : Position.t -> status -> status
  val get_position : status -> Position.t

  val start_variances : variances -> Position.t -> status
  val start : (Level.t * VariancePos.t option) array -> Position.t -> status

  val start_inference : Level.Set.t -> Position.t -> status

  val inferred : status -> variances
  val finish : status -> Variances.t

end = struct

  (**
     Each local universe is either in the [univs] map or is Invariant.

     If [univs] is empty all universes are Invariant and there is nothing more to do,
     so we stop by raising [TrivialVariance]. The [soft] check comes before that.
  *)
  type status = {
    orig_array : (Level.t * VariancePos.t option) array;
    univs : variances;
    infer_mode : bool;
    position : Position.t;
  }

  let get_infer_mode v = v.infer_mode
  let set_infer_mode b v = if v.infer_mode == b then v else {v with infer_mode=b}

  let get_position v = v.position
  let set_position p v = if v.position == p then v else {v with position=p}

  let to_variance_pos position vocc =
    match min_pos_variance position vocc with
    | Some v -> (v, position)
    | None -> (Irrelevant, position)

  let infer_level_eq u variances =
    match Level.Map.find_opt u variances.univs with
    | None -> variances
    | Some (Check, expected) ->
      let expected = to_variance_pos variances.position expected in
      if VariancePos.le (Invariant, variances.position) expected then variances
      else raise (BadVariance (u, expected, (Invariant, variances.position)))
    | Some (Infer, inferred) ->
      if not variances.infer_mode then raise NotInferring;
      let newv = position_variance_sup Infer true u inferred (Invariant, variances.position) in
      let univs = Level.Map.add u (Infer, newv) variances.univs in
      {variances with univs}

  let infer_level_leq u variances =
    let univs =
      Level.Map.update u (function
          | None -> Some (Infer, position_variance_sup Infer variances.infer_mode u default_occ (Covariant, variances.position))
          | Some (mode, occ) ->
            let occ' = position_variance_sup mode variances.infer_mode u occ (Covariant, variances.position) in
            Some (mode, occ'))
        variances.univs
    in
    if univs == variances.univs then variances else {variances with univs}

  let infer_level_geq u variances =
    let univs =
      Level.Map.update u (function
          | None -> Some (Infer, position_variance_sup Infer variances.infer_mode u default_occ (Contravariant, variances.position))
          | Some (mode, occ) ->
            let occ' = position_variance_sup mode variances.infer_mode u occ (Contravariant, variances.position) in
            Some (mode, occ'))
        variances.univs
    in
    if univs == variances.univs then variances else {variances with univs}

  let start_variances univs position =
    { univs; orig_array = [| |]; infer_mode = true; position}

  let start us position =
    let univs = Array.fold_left (fun univs (u,variance) ->
        match variance with
        | None -> Level.Map.add u (Infer, default_occ) univs
        | Some occ -> Level.Map.add u (Check, make_occ occ) univs)
      Level.Map.empty us
    in
    {univs; orig_array=us; infer_mode=true; position}

  let start_inference levels position =
    let univs = Level.Set.fold (fun level -> Level.Map.add level (Infer, default_occ)) levels Level.Map.empty in
    { univs; orig_array = [||]; infer_mode=true; position}

  let sup_vopt x y =
    match x, y with
    | None, None -> x
    | Some _, None -> x
    | None, Some _ -> y
    | Some v, Some v' -> Some (UVars.Variance.sup v v')

  let variance_of_occ { in_binder; in_term; in_type } =
    let open Position in
    match in_binder, in_term, in_type with
    | Some (i, v), (None | Some Irrelevant), (None | Some Irrelevant) -> (v, InBinder i)
    | in_binder, Some v, None -> (Option.get (sup_vopt (Option.map snd in_binder) (Some v)), InTerm)
    | in_binder, in_term, in_type ->
      let in_binder = Option.map snd in_binder in
      match sup_vopt in_binder in_type, in_term with
      | Some v, None -> (v, InType)
      | None, Some v -> (v, InTerm)
      | Some vty, Some vterm -> (UVars.Variance.sup vty vterm, InTerm)
      | None, None -> (Irrelevant, InTerm)

  let to_variance_opt o =
    Option.cata (fun (_mode, occ) -> variance_of_occ occ) (Irrelevant,Position.InTerm) o

  let inferred variances = variances.univs

  let pr prl status = pr_variances prl status.univs

  let finish variances =
    Variances.of_array @@
    Array.map
      (fun (u,_) -> to_variance_opt (Level.Map.find_opt u variances.univs))
      variances.orig_array

end
open Inf

let infer_generic_instance_eq variances u =
  Array.fold_left (fun variances u ->
    Level.Set.fold (fun l -> infer_level_eq l) (Universe.levels u) variances)
    variances u

(* no variance for qualities *)
let level_instance_univs u = snd (Instance.to_array (Instance.of_level_instance u))
let instance_univs u = snd (Instance.to_array u)

let extend_con_instance cb u =
  (Array.append (level_instance_univs cb.const_univ_hyps) (instance_univs u))

let extend_ind_instance mib u =
  (Array.append (level_instance_univs mib.mind_univ_hyps) (instance_univs u))

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

let infer_cumulative_instance cv_pb nargs gvariances variances u =
  let open Position in
  Array.fold_left2 (fun variances varu u ->
      match cv_pb, varu with
      | _, (Irrelevant, _) -> variances
      | _, (_, InType) -> variances (* Irrelevant due to appearing only in the type *)
      | _, (_, InBinder i) when i < nargs -> variances (* Irrelevance due to enough applied arguments *)
      | _, (Invariant, _)
      | Conv, ((Covariant | Contravariant), _) ->
        (* Co/contravariant in invariant position, becomes invariant *)
        Level.Set.fold infer_level_eq (Universe.levels u) variances
      | Cumul, (Covariant, _) ->
        (* Covariant in covariant position -> covariant *)
        Level.Set.fold infer_level_leq (Universe.levels u) variances
      | Cumul, (Contravariant, _) ->
        (* Contravariant in covariant position -> contravariant *)
        Level.Set.fold infer_level_geq (Universe.levels u) variances
      | InvCumul, (Contravariant, _) ->
        (* Contravariant in contravariant position -> covariant *)
        Level.Set.fold infer_level_leq (Universe.levels u) variances
      | InvCumul, (Covariant, _) ->
        (* Covariant in contravariant position -> contravariant *)
        Level.Set.fold infer_level_geq (Universe.levels u) variances)
    variances
    (UVars.Variances.repr gvariances)
    u

let infer_inductive_instance cv_pb env variances ind nargs u =
  if not (Environ.mem_mind (fst ind) env) then
    infer_generic_instance_eq variances (instance_univs u)
  else
  let mind = Environ.lookup_mind (fst ind) env in
  let u = extend_ind_instance mind u in
  match extended_mind_variance mind with
  | None -> infer_generic_instance_eq variances u
  | Some mind_variance ->
    if not (Int.equal (UCompare.inductive_cumulativity_arguments (mind,snd ind)) nargs)
    then infer_generic_instance_eq variances u
    else infer_cumulative_instance cv_pb nargs mind_variance variances u

let infer_constructor_instance_eq env variances ((mi,ind),ctor) nargs u =
  if not (Environ.mem_mind mi env) then
    infer_generic_instance_eq variances (instance_univs u)
  else
  let mind = Environ.lookup_mind mi env in
  let u = extend_ind_instance mind u in
  match extended_mind_variance mind with
  | None -> infer_generic_instance_eq variances u
  | Some _ ->
    if not (Int.equal (UCompare.constructor_cumulativity_arguments (mind, ind, ctor)) nargs)
    then infer_generic_instance_eq variances u
    else variances (* constructors are convertible at common supertype *)

let infer_sort cv_pb variances s =
  match cv_pb with
  | Conv ->
    Level.Set.fold infer_level_eq (Sorts.levels s) variances
  | Cumul ->
    Level.Set.fold infer_level_leq (Sorts.levels s) variances
  | InvCumul ->
    Level.Set.fold infer_level_geq (Sorts.levels s) variances

let infer_constant cv_pb env nargs variances has_def (con,u) =
  let cb = Environ.lookup_constant con env in
  let u = extend_con_instance cb u in
  match extended_const_variance cb with
  | None ->
    let variances = if has_def then set_infer_mode false variances else variances in
    infer_generic_instance_eq variances u
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
        let variances = infer_constant cv_pb (info_env (fst infos)) nargs variances (Option.has_some def) con in
        let variances = infer_stack infos variances stk in
        set_infer_mode infer_mode variances
      with BadVariance _ | NotInferring as e ->
      match def with
      | None -> raise e
      | Some (hd,stk) -> infer_fterm cv_pb infos variances hd stk
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
    let variances = infer_vect infos variances (Array.map (mk_clos e) tys) in
    let le = CClosure.usubs_liftn n e in
    let variances =
      let na = Array.map (usubst_binder e) na in
      let infos = push_relevances infos na in
      infer_vect infos variances (Array.map (mk_clos le) cl)
    in
    infer_stack infos variances stk
  | FArray (u,elemsdef,ty) -> (* False? Not implemnting irrelevance *)
    let variances = infer_generic_instance_eq variances (instance_univs u) in
    let variances = infer_fterm Conv infos variances ty [] in
    let elems, def = Parray.to_array elemsdef in
    let variances = infer_fterm Conv infos variances def [] in
    let variances = infer_vect infos variances elems in
    infer_stack infos variances stk

  | FCaseInvert (ci, u, pms, p, _, _, br, e) ->
    infer_case infos variances cv_pb ci u pms p br e
  (* Removed by whnf *)
  | FLOCKED | FCaseT _ | FLetIn _ | FApp _ | FLIFT _ | FCLOS _ -> assert false
  | FIrrelevant -> assert false (* TODO: use create_conv_infos below and use it? *)

and infer_case infos variances cv_pb ci u pms p br e =
  let open CClosure in
  let push_relevances (infos, tab) n = (push_relevances infos n, tab) in
  let mib = Environ.lookup_mind (fst ci.ci_ind) (info_env (fst infos)) in
  let (_, (_, _), _, _, br) =
    Inductive.expand_case_specif mib (ci, u, pms, p, NoInvert, mkProp, br)
  in
  debug Pp.(fun () -> str"computing variance of case with conv_pb = " ++ pr_cumul_pb cv_pb);
  let infer cv_pb c variances = infer_fterm cv_pb infos variances (mk_clos e c) [] in
  let orig_pos = get_position variances in
  let variances =
    if cv_pb == Cumul && orig_pos == Position.InTerm then
      set_position Position.InType variances
    else variances
  in
  let variances =
    let (ctx, arity), _r = p in
    let ctx = Array.map (usubst_binder e) ctx in
    let infos = push_relevances infos ctx in
    let e = CClosure.usubs_liftn (Array.length ctx) e in
    infer_fterm cv_pb infos variances (mk_clos e arity) [] in
  let variances = set_position orig_pos variances in
  Array.fold_right (infer cv_pb) br variances

and infer_stack infos variances (stk:CClosure.stack) =
  match stk with
  | [] -> variances
  | z :: stk ->
    let open CClosure in
    let variances = match z with
      | Zapp v -> infer_vect infos variances v
      | Zproj _ -> variances
      | Zfix (fx,a) ->
        let variances = infer_fterm Conv infos variances fx [] in
        infer_stack infos variances a
      | ZcaseT (ci,u,pms,p,br,e) ->
        infer_case infos variances Cumul ci u pms p br e
      | Zshift _ -> variances
      | Zupdate _ -> variances
      | Zprimitive (_,_,rargs,kargs) ->
        let variances = List.fold_left (fun variances c -> infer_fterm Conv infos variances c []) variances rargs in
        let variances = List.fold_left (fun variances (_,c) -> infer_fterm Conv infos variances c []) variances kargs in
        variances
    in
    infer_stack infos variances stk

and infer_vect infos variances v =
  Array.fold_left (fun variances c -> infer_fterm Conv infos variances c []) variances v

let infer_term cv_pb env ~evars variances c =
  let open CClosure in
  let reds = RedFlags.red_add_transparent RedFlags.betaiotazeta TransparentState.full in
  let infos = (create_clos_infos reds ~evars env, create_tab ()) in
  infer_fterm cv_pb infos variances (CClosure.inject c) []

type pre_variances =
  (Univ.Level.t * VariancePos.t option) array

type variance_occurrences = variance_occurrence array

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

let infer_body env ~evars ~shift variances body =
  let ctx, body = Reduction.whd_decompose_lambda ~evars env body in
  let env, variances = infer_context env ~evars ~shift variances ctx in
  let variances = Inf.set_position Position.InTerm variances in
  infer_term Cumul env ~evars variances body

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

let infer_definition_core env ?(evars = CClosure.default_evar_handler env) ?in_ctx ~typ ?body variances =
  let shift, variances =
    match in_ctx with
    | None -> 0, Inf.start variances Position.InType
    | Some ctx ->
      let shift = Context.Named.nhyps ctx in
      let variances = Inf.start (Array.map (fun (l, occ) -> (l, Option.map (VariancePos.lift shift) occ)) variances) Position.InType in
      infer_named_context env ~evars variances ctx
  in
  debug Pp.(fun () -> str"infer_definition: " ++ Inf.pr Level.raw_pr variances ++
    str" in type: " ++ Constr.debug_print typ ++ spc () ++
    str " and body; " ++ pr_opt Constr.debug_print body);
  let variances = infer_arity_constructor true env ~evars ~shift variances typ in
  debug Pp.(fun () -> str"infer_definition after type: " ++ Inf.pr Level.raw_pr variances);
  let variances = Option.cata (infer_body env ~evars ~shift variances) variances body in
  debug Pp.(fun () -> str"infer_definition finished with: " ++ Inf.pr Level.raw_pr variances);
  shift, Inf.finish variances

let infer_definition env ?(evars = CClosure.default_evar_handler env) ?in_ctx ~typ ?body variances =
  try infer_definition_core env ~evars ?in_ctx ~typ ?body variances
  with BadVariance (lev, expected, actual) ->
    Type_errors.error_bad_variance env ~lev ~expected ~actual

let infer_inductive_core ~env_params ~env_ar_par ~evars ~arities ~ctors univs =
  let variances = Inf.start univs Position.InType in
  let variances = List.fold_left (fun variances arity ->
      infer_arity_constructor true env_params ~evars variances arity)
      variances arities
  in
  let variances = Inf.set_position Position.InTerm variances in
  let variances = List.fold_left
      (List.fold_left (infer_arity_constructor false env_ar_par ~shift:0 ~evars))
      variances ctors
  in
  Inf.finish variances

let infer_inductive ~env_params ~env_ar_par ?(evars = CClosure.default_evar_handler env_params) ~arities ~ctors univs =
  try infer_inductive_core ~env_params ~env_ar_par ~evars ~arities ~ctors univs
  with
  | BadVariance (lev, expected, actual) ->
    Type_errors.error_bad_variance env_params ~lev ~expected ~actual
