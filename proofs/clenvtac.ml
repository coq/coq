(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open Constr
open Termops
open Evd
open EConstr
open Refiner
open Logic
open Reduction
open Clenv

(* This function put casts around metavariables whose type could not be
 * inferred by the refiner, that is head of applications, predicates and
 * subject of Cases.
 * Does check that the casted type is closed. Anyway, the refiner would
 * fail in this case... *)

let clenv_cast_meta clenv =
  let rec crec u =
    match EConstr.kind clenv.evd u with
      | App _ | Case _ -> crec_hd u
      | Cast (c,_,_) when isMeta clenv.evd c -> u
      | Proj (p, c) -> mkProj (p, crec_hd c)
      | _  -> EConstr.map clenv.evd crec u

  and crec_hd u =
    match EConstr.kind clenv.evd (strip_outer_cast clenv.evd u) with
      | Meta mv ->
	  (try
            let b = Typing.meta_type clenv.evd mv in
	    assert (not (occur_meta clenv.evd b));
	    if occur_meta clenv.evd b then u
            else mkCast (mkMeta mv, DEFAULTcast, b)
	  with Not_found -> u)
      | App(f,args) -> mkApp (crec_hd f, Array.map crec args)
      | Case(ci,p,c,br) ->
	  mkCase (ci, crec_hd p, crec_hd c, Array.map crec br)
      | Proj (p, c) -> mkProj (p, crec_hd c)
      | _ -> u
  in
  crec

let clenv_value_cast_meta clenv =
    clenv_cast_meta clenv (clenv_value clenv)

let clenv_pose_dependent_evars ?(with_evars=false) clenv =
  let dep_mvs = clenv_dependent clenv in
  let env, sigma = clenv.env, clenv.evd in
  if not (List.is_empty dep_mvs) && not with_evars then
    raise
      (RefinerError (env, sigma, UnresolvedBindings (List.map (meta_name clenv.evd) dep_mvs)));
  clenv_pose_metas_as_evars clenv dep_mvs

let clenv_refine ?(with_evars=false) ?(with_classes=true) clenv =
  (* ppedrot: a Goal.enter here breaks things, because the tactic below may
     solve goals by side effects, while the compatibility layer keeps those
     useless goals. That deserves a FIXME. *)
  Proofview.V82.tactic begin fun gl ->
  let clenv, evars = clenv_pose_dependent_evars ~with_evars clenv in
  let evd' =
    if with_classes then
      let evd' =
        Typeclasses.resolve_typeclasses ~filter:Typeclasses.all_evars
          ~fail:(not with_evars) clenv.env clenv.evd
      in
      Typeclasses.make_unresolvables (fun x -> List.mem_f Evar.equal x evars) evd'
    else clenv.evd
  in
  let clenv = { clenv with evd = evd' } in
  tclTHEN
    (tclEVARS (Evd.clear_metas evd'))
    (refiner ~check:false EConstr.Unsafe.(to_constr (clenv_cast_meta clenv (clenv_value clenv)))) gl
  end

let clenv_pose_dependent_evars ?(with_evars=false) clenv =
  fst (clenv_pose_dependent_evars ~with_evars clenv)

open Unification

let dft = default_unify_flags

let res_pf ?with_evars ?(with_classes=true) ?(flags=dft ()) clenv =
  Proofview.Goal.enter begin fun gl ->
    let clenv = clenv_unique_resolver ~flags clenv gl in
    clenv_refine ?with_evars ~with_classes clenv
  end

(* [unifyTerms] et [unify] ne semble pas gérer les Meta, en
   particulier ne semblent pas vérifier que des instances différentes
   d'une même Meta sont compatibles. D'ailleurs le "fst" jette les metas
   provenant de w_Unify. (Utilisé seulement dans prolog.ml) *)

let fail_quick_core_unif_flags = {
  modulo_conv_on_closed_terms = Some TransparentState.full;
  use_metas_eagerly_in_conv_on_closed_terms = false;
  use_evars_eagerly_in_conv_on_closed_terms = false;
  modulo_delta = TransparentState.empty;
  modulo_delta_types = TransparentState.full;
  check_applied_meta_types = false;
  use_pattern_unification = false;
  use_meta_bound_pattern_unification = true; (* ? *)
  frozen_evars = Evar.Set.empty;
  restrict_conv_on_strict_subterms = false; (* ? *)
  modulo_betaiota = false;
  modulo_eta = true;
}

let fail_quick_unif_flags = {
  core_unify_flags = fail_quick_core_unif_flags;
  merge_unify_flags = fail_quick_core_unif_flags;
  subterm_unify_flags = fail_quick_core_unif_flags;
  allow_K_in_toplevel_higher_order_unification = false;
  resolve_evars = false
}

(* let unifyTerms m n = walking (fun wc -> fst (w_Unify CONV m n [] wc)) *)
let unify ?(flags=fail_quick_unif_flags) m =
  Proofview.Goal.enter begin fun gl ->
    let env = Tacmach.New.pf_env gl in
    let n = Tacmach.New.pf_concl gl in
    let evd = clear_metas (Tacmach.New.project gl) in
    try
      let evd' = w_unify env evd CONV ~flags m n in
	Proofview.Unsafe.tclEVARSADVANCE evd'
    with e when CErrors.noncritical e -> Proofview.tclZERO e
  end
