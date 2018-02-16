(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Reduction
open Declarations
open Constr
open Univ
open Util

(** Throughout this module we modify a map [variances] from local
   universes to [Variance.t]. It starts as a trivial mapping to
   [Irrelevant] and every time we encounter a local universe we
   restrict it accordingly. *)

let infer_level_eq u variances =
  if LMap.mem u variances
  then LMap.set u Variance.Invariant variances
  else variances

let infer_level_leq u variances =
  match LMap.find u variances with
  | exception Not_found -> variances
  | varu -> LMap.set u (Variance.sup varu Variance.Covariant) variances

let infer_generic_instance_eq variances u =
  Array.fold_left (fun variances u -> infer_level_eq u variances)
    variances (Instance.to_array u)

let variance_pb cv_pb var =
  let open Variance in
  match cv_pb, var with
  | _, Irrelevant -> Irrelevant
  | _, Invariant -> Invariant
  | CONV, Covariant -> Invariant
  | CUMUL, Covariant -> Covariant

let infer_cumulative_ind_instance cv_pb cumi variances u =
  Array.fold_left2 (fun variances varu u ->
      match LMap.find u variances with
      | exception Not_found -> variances
      | varu' ->
        LMap.set u (Variance.sup varu' (variance_pb cv_pb varu)) variances)
    variances (ACumulativityInfo.variance cumi) (Instance.to_array u)

let infer_inductive_instance cv_pb env variances ind nargs u =
  let mind = Environ.lookup_mind (fst ind) env in
  match mind.mind_universes with
  | Monomorphic_ind _ -> assert (Instance.is_empty u); variances
  | Polymorphic_ind _ -> infer_generic_instance_eq variances u
  | Cumulative_ind cumi ->
    if not (Int.equal (inductive_cumulativity_arguments (mind,snd ind)) nargs)
    then infer_generic_instance_eq variances u
    else infer_cumulative_ind_instance cv_pb cumi variances u

let infer_constructor_instance_eq env variances ((mi,ind),ctor) nargs u =
  let mind = Environ.lookup_mind mi env in
  match mind.mind_universes with
  | Monomorphic_ind _ -> assert (Instance.is_empty u); variances
  | Polymorphic_ind _ -> infer_generic_instance_eq variances u
  | Cumulative_ind cumi ->
    if not (Int.equal (constructor_cumulativity_arguments (mind,ind,ctor)) nargs)
    then infer_generic_instance_eq variances u
    else infer_cumulative_ind_instance CONV cumi variances u

let infer_sort cv_pb variances s =
  match cv_pb with
  | CONV ->
    LSet.fold infer_level_eq (Universe.levels (Sorts.univ_of_sort s)) variances
  | CUMUL ->
    LSet.fold infer_level_leq (Universe.levels (Sorts.univ_of_sort s)) variances

let infer_table_key infos variances c =
  let open Names in
  match c with
  | ConstKey (_, u) ->
    infer_generic_instance_eq variances u
  | VarKey _ | RelKey _ -> variances

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
    infer_vect infos variances (Array.map (mk_clos e) args)
  | FRel _ -> infer_stack infos variances stk
  | FInt _ -> infer_stack infos variances stk
  | FFlex fl ->
    let variances = infer_table_key infos variances fl in
    infer_stack infos variances stk
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
      if Instance.is_empty u then variances
      else
        let nargs = stack_args_size stk in
        infer_inductive_instance cv_pb (info_env (fst infos)) variances ind nargs u
    in
    infer_stack infos variances stk
  | FConstruct (ctor,u) ->
    let variances =
      if Instance.is_empty u then variances
      else
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

  (* Removed by whnf *)
  | FLOCKED | FCaseT _ | FLetIn _ | FApp _ | FLIFT _ | FCLOS _ -> assert false

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
      | ZcaseT (ci,p,br,e) ->
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

let infer_term cv_pb env variances c =
  let open CClosure in
  let infos = (create_clos_infos all env, create_tab ()) in
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

let infer_inductive env mie =
  let open Entries in
  let { mind_entry_params = params;
        mind_entry_inds = entries; } = mie
  in
  let univs =
    match mie.mind_entry_universes with
    | Monomorphic_ind_entry _
    | Polymorphic_ind_entry _ as univs -> univs
    | Cumulative_ind_entry (nas, cumi) ->
      let uctx = CumulativityInfo.univ_context cumi in
      let uarray = Instance.to_array @@ UContext.instance uctx in
      let env = Environ.push_context uctx env in
      let variances =
        Array.fold_left (fun variances u -> LMap.add u Variance.Irrelevant variances)
          LMap.empty uarray
      in
      let env = Typeops.check_context env params in
      let variances = List.fold_left (fun variances entry ->
          let variances = infer_arity_constructor true
              env variances entry.mind_entry_arity
          in
          List.fold_left (infer_arity_constructor false env)
            variances entry.mind_entry_lc)
          variances
          entries
      in
      let variances = Array.map (fun u -> LMap.find u variances) uarray in
      Cumulative_ind_entry (nas, CumulativityInfo.make (uctx, variances))
  in
  { mie with mind_entry_universes = univs }
