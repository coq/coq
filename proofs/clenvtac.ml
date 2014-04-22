(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
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
      | _  -> map_constr crec u

  and crec_hd u =
    match kind_of_term (strip_outer_cast u) with
      | Meta mv ->
	  (try
            let b = Typing.meta_type clenv.evd mv in
	    assert (not (occur_meta b));
	    if occur_meta b then u
            else mkCast (mkMeta mv, DEFAULTcast, b)
	  with Not_found -> u)
      | App(f,args) -> mkApp (crec_hd f, Array.map crec args)
      | Case(ci,p,c,br) ->
	  mkCase (ci, crec_hd p, crec_hd c, Array.map crec br)
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

let clenv_refine with_evars ?(with_classes=true) clenv gls =
  let clenv = clenv_pose_dependent_evars with_evars clenv in
  let evd' =
    if with_classes then
      let evd' = Typeclasses.resolve_typeclasses ~filter:Typeclasses.all_evars
        ~fail:(not with_evars) clenv.env clenv.evd
      in Typeclasses.mark_unresolvables ~filter:Typeclasses.all_goals evd'
    else clenv.evd
  in
  let clenv = { clenv with evd = evd' } in
  tclTHEN
    (tclEVARS evd')
    (refine (clenv_cast_meta clenv (clenv_value clenv)))
    gls

open Unification

let dft = default_unify_flags

let res_pf clenv ?(with_evars=false) ?(flags=dft) gls =
  clenv_refine with_evars (clenv_unique_resolver ~flags clenv gls) gls

(* [unifyTerms] et [unify] ne semble pas gérer les Meta, en
   particulier ne semblent pas vérifier que des instances différentes
   d'une même Meta sont compatibles. D'ailleurs le "fst" jette les metas
   provenant de w_Unify. (Utilisé seulement dans prolog.ml) *)

let fail_quick_unif_flags = {
  modulo_conv_on_closed_terms = Some full_transparent_state;
  use_metas_eagerly_in_conv_on_closed_terms = false;
  modulo_delta = empty_transparent_state;
  modulo_delta_types = full_transparent_state;
  modulo_delta_in_merge = None;
  check_applied_meta_types = false;
  resolve_evars = false;
  use_pattern_unification = false;
  use_meta_bound_pattern_unification = true; (* ? *)
  frozen_evars = Evar.Set.empty;
  restrict_conv_on_strict_subterms = false; (* ? *)
  modulo_betaiota = false;
  modulo_eta = true;
  allow_K_in_toplevel_higher_order_unification = false
}

(* let unifyTerms m n = walking (fun wc -> fst (w_Unify CONV m n [] wc)) *)
let unifyTerms ?(flags=fail_quick_unif_flags) m n gls =
  let env = pf_env gls in
  let evd = create_goal_evar_defs (project gls) in
  let evd' = w_unify env evd CONV ~flags m n in
  tclIDTAC {it = gls.it; sigma =  evd'; }

let unify ?(flags=fail_quick_unif_flags) m gls =
  let n = pf_concl gls in unifyTerms ~flags m n gls
