(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Util
open Names
open Term
open Termops
open Evd
open Refiner
open Logic
open Reduction
open Tacmach
open Clenv
open Proofview.Notations

(* This function put casts around metavariables whose type could not be
 * infered by the refiner, that is head of applications, predicates and
 * subject of Cases.
 * Does check that the casted type is closed. Anyway, the refiner would
 * fail in this case... *)

let clenv_cast_meta clenv =
  let rec crec u =
    match kind_of_term u with
      | App _ | Case _ -> crec_hd u
      | Cast (c,_,_) when isMeta c -> u
      | Proj (p, c) -> mkProj (p, crec_hd c)
      | _  -> map_constr crec u

  and crec_hd u =
    match kind_of_term (strip_outer_cast clenv.evd (EConstr.of_constr u)) with
      | Meta mv ->
	  (try
            let b = Typing.meta_type clenv.evd mv in
	    assert (not (occur_meta clenv.evd (EConstr.of_constr b)));
	    if occur_meta clenv.evd (EConstr.of_constr b) then u
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

let clenv_pose_dependent_evars with_evars clenv =
  let dep_mvs = clenv_dependent clenv in
  if not (List.is_empty dep_mvs) && not with_evars then
    raise
      (RefinerError (UnresolvedBindings (List.map (meta_name clenv.evd) dep_mvs)));
  clenv_pose_metas_as_evars clenv dep_mvs

(** Use our own fast path, more informative than from Typeclasses *)
let check_tc evd =
  let has_resolvable = ref false in
  let check _ evi =
    let res = Typeclasses.is_resolvable evi in
    if res then
      let () = has_resolvable := true in
      Typeclasses.is_class_evar evd evi
    else false
  in
  let has_typeclass = Evar.Map.exists check (Evd.undefined_map evd) in
  (has_typeclass, !has_resolvable)

let clenv_refine with_evars ?(with_classes=true) clenv =
  (** ppedrot: a Goal.enter here breaks things, because the tactic below may
      solve goals by side effects, while the compatibility layer keeps those
      useless goals. That deserves a FIXME. *)
  Proofview.V82.tactic begin fun gl ->
  let clenv = clenv_pose_dependent_evars with_evars clenv in
  let evd' =
    if with_classes then
      let (has_typeclass, has_resolvable) = check_tc clenv.evd in
      let evd' =
        if has_typeclass then
          Typeclasses.resolve_typeclasses ~fast_path:false ~filter:Typeclasses.all_evars
          ~fail:(not with_evars) clenv.env clenv.evd
        else clenv.evd
      in
      if has_resolvable then
        Typeclasses.mark_unresolvables ~filter:Typeclasses.all_goals evd'
      else evd'
    else clenv.evd
  in
  let clenv = { clenv with evd = evd' } in
  tclTHEN
    (tclEVARS (Evd.clear_metas evd'))
    (refine_no_check (clenv_cast_meta clenv (clenv_value clenv))) gl
  end

open Unification

let dft = default_unify_flags

let res_pf ?(with_evars=false) ?(with_classes=true) ?(flags=dft ()) clenv =
  Proofview.Goal.enter { enter = begin fun gl ->
    let clenv gl = clenv_unique_resolver ~flags clenv gl in
    clenv_refine with_evars ~with_classes (Tacmach.New.of_old clenv (Proofview.Goal.assume gl))
  end }

(* [unifyTerms] et [unify] ne semble pas gérer les Meta, en
   particulier ne semblent pas vérifier que des instances différentes
   d'une même Meta sont compatibles. D'ailleurs le "fst" jette les metas
   provenant de w_Unify. (Utilisé seulement dans prolog.ml) *)

let fail_quick_core_unif_flags = {
  modulo_conv_on_closed_terms = Some full_transparent_state;
  use_metas_eagerly_in_conv_on_closed_terms = false;
  use_evars_eagerly_in_conv_on_closed_terms = false;
  modulo_delta = empty_transparent_state;
  modulo_delta_types = full_transparent_state;
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
  Proofview.Goal.enter { enter = begin fun gl ->
    let env = Tacmach.New.pf_env gl in
    let n = Tacmach.New.pf_concl (Proofview.Goal.assume gl) in
    let evd = clear_metas (Tacmach.New.project gl) in
    try
      let evd' = w_unify env evd CONV ~flags (EConstr.of_constr m) (EConstr.of_constr n) in
	Proofview.Unsafe.tclEVARSADVANCE evd'
    with e when CErrors.noncritical e -> Proofview.tclZERO e
  end }
