(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Reduction
open Declarations
open Constr
open Univ
open Variance
open Util

exception TrivialVariance

(** Not the same as Type_errors.BadVariance because we don't have the env where we raise. *)
exception BadVariance of Level.t * Variance.t * Variance.t
(* some ocaml bug is triggered if we make this an inline record *)

exception NotInferring

module Inf : sig
  type variances
  val infer_level_eq : Level.t -> variances -> variances
  val infer_level_leq : Level.t -> variances -> variances

  val get_infer_mode : variances -> bool
  val set_infer_mode : bool -> variances -> variances

  val start : (Level.t * Variance.t option) array -> variances
  val finish : variances -> Variance.t array
end = struct
  type inferred = IrrelevantI | CovariantI
  type mode = Check | Infer

  (**
     Each local universe is either in the [univs] map or is Invariant.

     If [univs] is empty all universes are Invariant and there is nothing more to do,
     so we stop by raising [TrivialVariance]. The [soft] check comes before that.
  *)
  type variances = {
    orig_array : (Level.t * Variance.t option) array;
    univs : (mode * inferred) Level.Map.t;
    infer_mode : bool;
  }

  let get_infer_mode v = v.infer_mode
  let set_infer_mode b v = if v.infer_mode == b then v else {v with infer_mode=b}

  let to_variance = function
    | IrrelevantI -> Irrelevant
    | CovariantI -> Covariant

  let to_variance_opt o = Option.cata to_variance Invariant o

  let infer_level_eq u variances =
    match Level.Map.find_opt u variances.univs with
    | None -> variances
    | Some (Check, expected) ->
      let expected = to_variance expected in
      raise (BadVariance (u, expected, Invariant))
    | Some (Infer, _) ->
      if not variances.infer_mode then raise NotInferring;
      let univs = Level.Map.remove u variances.univs in
      if Level.Map.is_empty univs then raise TrivialVariance;
      {variances with univs}

  let infer_level_leq u variances =
    (* can only set Irrelevant -> Covariant so no TrivialVariance *)
    let univs =
      Level.Map.update u (function
          | None -> None
          | Some (_,CovariantI) as x -> x
          | Some (Infer,IrrelevantI) ->
            if not variances.infer_mode then raise NotInferring;
            Some (Infer,CovariantI)
          | Some (Check,IrrelevantI) ->
            raise (BadVariance (u, Irrelevant, Covariant)))
        variances.univs
    in
    if univs == variances.univs then variances else {variances with univs}

  let start us =
    let univs = Array.fold_left (fun univs (u,variance) ->
        match variance with
        | None -> Level.Map.add u (Infer,IrrelevantI) univs
        | Some Invariant -> univs
        | Some Covariant -> Level.Map.add u (Check,CovariantI) univs
        | Some Irrelevant -> Level.Map.add u (Check,IrrelevantI) univs)
        Level.Map.empty us
    in
    if Level.Map.is_empty univs then raise TrivialVariance;
    {univs; orig_array=us; infer_mode=true}

  let finish variances =
    Array.map
      (fun (u,_check) -> to_variance_opt (Option.map snd (Level.Map.find_opt u variances.univs)))
      variances.orig_array

end
open Inf

let infer_generic_instance_eq variances u =
  Array.fold_left (fun variances u -> infer_level_eq u variances)
    variances (Instance.to_array u)

let extend_con_instance cb u =
  Instance.(of_array (Array.append (to_array cb.const_univ_hyps) (to_array u)))

let extend_ind_instance mib u =
  Instance.(of_array (Array.append (to_array mib.mind_univ_hyps) (to_array u)))

let extended_mind_variance mind =
  match mind.mind_variance, mind.mind_sec_variance with
  | None, None -> None
  | Some _ as variance, None -> variance
  | None, Some _ -> assert false
  | Some variance, Some sec_variance -> Some (Array.append sec_variance variance)

let infer_cumulative_ind_instance cv_pb mind_variance variances u =
  Array.fold_left2 (fun variances varu u ->
      match cv_pb, varu with
      | _, Irrelevant -> variances
      | _, Invariant | CONV, Covariant -> infer_level_eq u variances
      | CUMUL, Covariant -> infer_level_leq u variances)
    variances mind_variance (Instance.to_array u)

let infer_inductive_instance cv_pb env variances ind nargs u =
  let mind = Environ.lookup_mind (fst ind) env in
  let u = extend_ind_instance mind u in
  match extended_mind_variance mind with
  | None -> infer_generic_instance_eq variances u
  | Some mind_variance ->
    if not (Int.equal (inductive_cumulativity_arguments (mind,snd ind)) nargs)
    then infer_generic_instance_eq variances u
    else infer_cumulative_ind_instance cv_pb mind_variance variances u

let infer_constructor_instance_eq env variances ((mi,ind),ctor) nargs u =
  let mind = Environ.lookup_mind mi env in
  let u = extend_ind_instance mind u in
  match extended_mind_variance mind with
  | None -> infer_generic_instance_eq variances u
  | Some _ ->
    if not (Int.equal (constructor_cumulativity_arguments (mind,ind,ctor)) nargs)
    then infer_generic_instance_eq variances u
    else variances (* constructors are convertible at common supertype *)

let infer_sort cv_pb variances s =
  match cv_pb with
  | CONV ->
    Level.Set.fold infer_level_eq (Sorts.levels s) variances
  | CUMUL ->
    Level.Set.fold infer_level_leq (Sorts.levels s) variances

let infer_constant env variances (con,u) =
  let cb = Environ.lookup_constant con env in
  let u = extend_con_instance cb u in
  infer_generic_instance_eq variances u

let whd_stack (infos, tab) hd stk = CClosure.whd_stack infos tab hd stk

let rec infer_fterm cv_pb infos variances hd stk =
  Control.check_for_interrupt ();
  let hd,stk = whd_stack infos hd stk in
  let open CClosure in
  match fterm_of hd with
  | FAtom a ->
    begin match kind a with
      | Sort s -> infer_sort cv_pb variances s
      | Meta _ -> infer_stack infos variances stk
      | _ -> assert false
    end
  | FEvar ((_,args),e) ->
    let variances = infer_stack infos variances stk in
    infer_list infos variances (List.map (mk_clos e) args)
  | FRel _ -> infer_stack infos variances stk
  | FInt _ -> infer_stack infos variances stk
  | FFloat _ -> infer_stack infos variances stk
  | FFlex Names.(RelKey _ | VarKey _ as fl) ->
    (* We could try to lazily unfold but then we have to analyse the
       universes in the bodies, not worth coding at least for now. *)
    begin match unfold_ref_with_args (fst infos) (snd infos) fl stk with
    | Some (hd,stk) -> infer_fterm cv_pb infos variances hd stk
    | None -> infer_stack infos variances stk
    end
  | FFlex (Names.ConstKey con as fl) ->
    begin
      let def = unfold_ref_with_args (fst infos) (snd infos) fl stk in
      try
        let infer_mode = get_infer_mode variances in
        let variances = if Option.has_some def then set_infer_mode false variances else variances in
        let variances = infer_constant (info_env (fst infos)) variances con in
        let variances = infer_stack infos variances stk in
        set_infer_mode infer_mode variances
      with BadVariance _ | NotInferring as e ->
      match def with
      | None -> raise e
      | Some (hd,stk) -> infer_fterm cv_pb infos variances hd stk
    end
  | FProj (_,c) ->
    let variances = infer_fterm CONV infos variances c [] in
    infer_stack infos variances stk
  | FLambda _ ->
    let (_,ty,bd) = destFLambda mk_clos hd in
    let variances = infer_fterm CONV infos variances ty [] in
    infer_fterm CONV infos variances bd []
  | FProd (_,dom,codom,e) ->
    let variances = infer_fterm CONV infos variances dom [] in
    infer_fterm cv_pb infos variances (mk_clos (Esubst.subs_lift e) codom) []
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
  | FFix ((_,(_,tys,cl)),e) | FCoFix ((_,(_,tys,cl)),e) ->
    let n = Array.length cl in
    let variances = infer_vect infos variances (Array.map (mk_clos e) tys) in
    let le = Esubst.subs_liftn n e in
    let variances = infer_vect infos variances (Array.map (mk_clos le) cl) in
    infer_stack infos variances stk
  | FArray (u,elemsdef,ty) ->
    let variances = infer_generic_instance_eq variances u in
    let variances = infer_fterm CONV infos variances ty [] in
    let elems, def = Parray.to_array elemsdef in
    let variances = infer_fterm CONV infos variances def [] in
    let variances = infer_vect infos variances elems in
    infer_stack infos variances stk

  | FCaseInvert (ci, u, pms, p, _, _, br, e) ->
    let mib = Environ.lookup_mind (fst ci.ci_ind) (info_env (fst infos)) in
    let (_, p, _, _, br) = Inductive.expand_case_specif mib (ci, u, pms, p, NoInvert, mkProp, br) in
    let infer c variances = infer_fterm CONV infos variances (mk_clos e c) [] in
    let variances = infer p variances in
    Array.fold_right infer br variances

  (* Removed by whnf *)
  | FLOCKED | FCaseT _ | FLetIn _ | FApp _ | FLIFT _ | FCLOS _ -> assert false
  | FIrrelevant -> assert false (* TODO: use create_conv_infos below and use it? *)

and infer_stack infos variances (stk:CClosure.stack) =
  match stk with
  | [] -> variances
  | z :: stk ->
    let open CClosure in
    let variances = match z with
      | Zapp v -> infer_vect infos variances v
      | Zproj _ -> variances
      | Zfix (fx,a) ->
        let variances = infer_fterm CONV infos variances fx [] in
        infer_stack infos variances a
      | ZcaseT (ci,u,pms,p,br,e) ->
        let dummy = mkProp in
        let case = (ci, u, pms, p, NoInvert, dummy, br) in
        let (_, p, _, _, br) = Inductive.expand_case (info_env (fst infos)) case in
        let variances = infer_fterm CONV infos variances (mk_clos e p) [] in
        infer_vect infos variances (Array.map (mk_clos e) br)
      | Zshift _ -> variances
      | Zupdate _ -> variances
      | Zprimitive (_,_,rargs,kargs) ->
        let variances = List.fold_left (fun variances c -> infer_fterm CONV infos variances c []) variances rargs in
        let variances = List.fold_left (fun variances (_,c) -> infer_fterm CONV infos variances c []) variances kargs in
        variances
    in
    infer_stack infos variances stk

and infer_vect infos variances v =
  Array.fold_left (fun variances c -> infer_fterm CONV infos variances c []) variances v

and infer_list infos variances v =
  List.fold_left (fun variances c -> infer_fterm CONV infos variances c []) variances v

let infer_term cv_pb env variances c =
  let open CClosure in
  let reds = CClosure.RedFlags.red_add_transparent betaiotazeta TransparentState.full in
  let infos = (create_clos_infos reds env, create_tab ()) in
  infer_fterm cv_pb infos variances (CClosure.inject c) []

let infer_arity_constructor is_arity env variances arcn =
  let infer_typ typ (env,variances) =
    match typ with
    | Context.Rel.Declaration.LocalAssum (_, typ') ->
      (Environ.push_rel typ env, infer_term CUMUL env variances typ')
    | Context.Rel.Declaration.LocalDef _ -> assert false
  in
  let typs, codom = Reduction.dest_prod env arcn in
  let env, variances = Context.Rel.fold_outside infer_typ typs ~init:(env, variances) in
  (* If we have Inductive foo@{i j} : ... -> Type@{i} := C : ... -> foo Type@{j}
     i is irrelevant, j is invariant. *)
  if not is_arity then infer_term CUMUL env variances codom else variances

let infer_inductive_core ~env_params ~env_ar_par ~arities ~ctors univs =
  let variances = Inf.start univs in
  let variances = List.fold_left (fun variances arity ->
      infer_arity_constructor true env_params variances arity)
      variances arities
  in
  let variances = List.fold_left
      (List.fold_left (infer_arity_constructor false env_ar_par))
      variances ctors
  in
  Inf.finish variances

let infer_inductive ~env_params ~env_ar_par ~arities ~ctors univs =
  try infer_inductive_core ~env_params ~env_ar_par ~arities ~ctors univs
  with
  | TrivialVariance -> Array.make (Array.length univs) Invariant
  | BadVariance (lev, expected, actual) ->
    Type_errors.error_bad_variance env_params ~lev ~expected ~actual
