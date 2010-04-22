(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Pp
open Util
open Names
open Nameops
open Term
open Termops
open Sign
open Environ
open Evd
open Evarutil
open Proof_type
open Refiner
open Logic
open Reduction
open Reductionops
open Tacmach
open Rawterm
open Pattern
open Tacexpr
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
  let dep_mvs = clenv_dependent false clenv in
  if dep_mvs <> [] & not with_evars then
    raise
      (RefinerError (UnresolvedBindings (List.map (meta_name clenv.evd) dep_mvs)));
  clenv_pose_metas_as_evars clenv dep_mvs

let clenv_refine with_evars ?(with_classes=true) clenv gls =
  let clenv = clenv_pose_dependent_evars with_evars clenv in
  let evd' =
    if with_classes then
      Typeclasses.resolve_typeclasses ~fail:(not with_evars)
	clenv.env clenv.evd
    else clenv.evd
  in
  let clenv = { clenv with evd = evd' } in
  tclTHEN
    (tclEVARS evd')
    (refine (clenv_cast_meta clenv (clenv_value clenv)))
    gls

let dft = Unification.default_unify_flags

let res_pf clenv ?(with_evars=false) ?(allow_K=false) ?(flags=dft) gls =
  clenv_refine with_evars
    (clenv_unique_resolver allow_K ~flags:flags clenv gls) gls

let elim_res_pf_THEN_i clenv tac gls =
  let clenv' = (clenv_unique_resolver true clenv gls) in
  tclTHENLASTn (clenv_refine false clenv') (tac clenv') gls

let e_res_pf clenv = res_pf clenv ~with_evars:true ~allow_K:false ~flags:dft


(* [unifyTerms] et [unify] ne semble pas gérer les Meta, en
   particulier ne semblent pas vérifier que des instances différentes
   d'une même Meta sont compatibles. D'ailleurs le "fst" jette les metas
   provenant de w_Unify. (Utilisé seulement dans prolog.ml) *)

open Unification

let fail_quick_unif_flags = {
  modulo_conv_on_closed_terms = Some full_transparent_state;
  use_metas_eagerly = false;
  modulo_delta = empty_transparent_state;
  resolve_evars = false;
  use_evars_pattern_unification = false;
}

(* let unifyTerms m n = walking (fun wc -> fst (w_Unify CONV m n [] wc)) *)
let unifyTerms ?(flags=fail_quick_unif_flags) m n gls =
  let env = pf_env gls in
  let evd = create_goal_evar_defs (project gls) in
  let evd' = w_unify false env CONV ~flags m n evd in
  tclIDTAC {it = gls.it; sigma =  evd'}

let unify ?(flags=fail_quick_unif_flags) m gls =
  let n = pf_concl gls in unifyTerms ~flags m n gls
