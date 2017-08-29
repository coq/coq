(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Util
open Names
open Term
open Termops
open Evd
open EConstr
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
          ~fail:(not with_evars) ~split:false clenv.env clenv.evd
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

let with_clause (c, t) kont =
  let open Proofview in
  let open Proofview.Notations in
  Proofview.Goal.enter begin fun gl ->
  let sigma, cl = Tacmach.New.pf_apply (fun env sigma c -> make_clenv_from_env env sigma c) gl (c, t) in
  Unsafe.tclEVARS sigma <*> kont cl end

let clenv_chain_last c cl =
  let open Proofview in
  Proofview.Goal.enter begin fun gl ->
  let sigma, cl = Tacmach.New.pf_apply clenv_chain_last gl c cl in
  Unsafe.tclEVARS sigma end

let clenv_unify_concl flags clenv =
  Ftactic.enter begin fun gl ->
  let env = Tacmach.New.pf_env gl in
  let sigma = Tacmach.New.project gl in
  let concl = Tacmach.New.pf_concl (Proofview.Goal.assume gl) in
  try let sigma, clenv = clenv_unify_concl env sigma flags concl clenv in
      Ftactic.return (sigma, clenv)
  with Evarconv.UnableToUnify (evd, reason) ->
    let ex = Pretype_errors.(PretypeError (env, evd,
        CannotUnify (concl, clenv_concl clenv, Some reason))) in
    Ftactic.lift (Proofview.tclZERO ex) end

let debug_print_goal =
  Proofview.Goal.enter begin fun gl ->
  let env = Tacmach.New.pf_env gl in
  let concl = Tacmach.New.pf_concl (Proofview.Goal.assume gl) in
  (Feedback.msg_debug Pp.(str"After clenv_refine_gen: " ++
                            print_constr_env env (Proofview.Goal.sigma gl) concl);
   Proofview.tclUNIT ())
  end

let holes_goals sigma holes =
  List.map (fun h -> fst (destEvar sigma h.hole_evar)) holes

let clenv_check_dep_holes with_evars sigma ?origsigma clenv =
  let holes = clenv_dep_holes clenv in
  if not with_evars then
    let holes' =
      match origsigma with
      | None -> holes
      | Some origsigma ->
         let origevars = Evar.Map.domain (Evd.undefined_map origsigma) in
         let filter h =
           not (Evarutil.reachable_from_evars sigma origevars (fst (destEvar sigma h.hole_evar))) in
         List.filter filter holes
    in
     if not (List.is_empty holes') then
       Proofview.tclZERO
         (Logic.RefinerError (Logic.UnresolvedBindings
                                (List.map (fun h -> h.hole_name) holes')))
     else Proofview.tclUNIT (holes_goals sigma holes)
  else Proofview.tclUNIT (holes_goals sigma holes)

let rec rename_evar_concl sigma ctxt t =
  match ctxt, kind sigma t with
  | decl :: decls, Prod (na, b, t) ->
     mkProd (Context.Rel.Declaration.get_name decl, b, rename_evar_concl sigma decls t)
  | decl :: decls, LetIn (na, b, t', t) ->
     mkLetIn (Context.Rel.Declaration.get_name decl, b, t', rename_evar_concl sigma decls t)
  | [], _ -> t
  | _ :: _, _ -> raise (Invalid_argument "rename_evar_concl")

let rename_term env sigma t =
  let evd = ref sigma in
  let rename_branches ci tys brs =
    let rename i ty =
      let ndecls = ci.ci_cstr_ndecls.(i) in
      let ctxt, tyctx = decompose_prod_n_assum sigma ndecls ty in
      let ctxt = List.rev ctxt in
      let hd, args = decompose_app sigma (Evarutil.whd_evar !evd brs.(i)) in
      match kind sigma hd with
      | Evar (ev, args) ->
         let evi = Evd.find_undefined !evd ev in
         let concl = EConstr.of_constr (evar_concl evi) in
         let concl' = rename_evar_concl sigma ctxt concl in
         evd := Evd.add !evd ev { evi with evar_concl = EConstr.Unsafe.to_constr concl' }
      | _ -> ()
    in Array.iteri rename tys
  in
  let rec aux env c =
    match kind sigma c with
    | Case (ci,p,c,brs) ->
       let ct = Retyping.get_type_of env sigma c in
       let ((i,u), args) =
         try Tacred.find_hnf_rectype env sigma ct
         with Not_found -> CErrors.anomaly (Pp.str "mk_casegoals") in
       let indspec = ((i, EConstr.EInstance.kind sigma u), args) in
       (* FIXME why is that not on econstrs ? *)
       let (lbrty,_) = Inductiveops.type_case_branches_with_names env sigma indspec (EConstr.Unsafe.to_constr p) (EConstr.Unsafe.to_constr c) in
       let () = rename_branches ci (Array.map EConstr.of_constr lbrty) brs in
       mkCase (ci,p,aux env c,Array.map (aux env) brs)
    | _ -> map_constr_with_full_binders sigma push_rel aux env c
  in
  let t' = aux env t in
  !evd, t'

let debug_print_shelf s =
  let open Proofview in
  let open Proofview.Notations in
  let print_goal env sigma gl =
    let evi = Evd.find sigma gl in
    let concl = evi.evar_concl in
    (Feedback.msg_debug Pp.(int (Evar.repr gl) ++ str" : " ++ print_constr_env env sigma (EConstr.of_constr concl)))
  in
  Proofview.shelf >>= fun shelf ->
  Proofview.tclENV >>= fun env ->
  Proofview.tclEVARMAP >>= fun sigma ->
    (Feedback.msg_debug (Pp.str s);
     Feedback.msg_debug (Pp.str "shelf:");
     List.iter (print_goal env sigma) shelf;
     Feedback.msg_debug (Pp.str "future goals:");
     List.iter (print_goal env sigma) (Evd.future_goals sigma);
     tclUNIT ())

let clenv_refine_gen ?(with_evars=false) ?(with_classes=true) ?(shelve_subgoals=true) ?origsigma
                     flags (sigma, clenv) =
  let open Proofview in
  let open Proofview.Notations in
  Proofview.Goal.enter begin fun gl ->
  let env = Tacmach.New.pf_env gl in
  let sigma, clenv =
    try
      let sigma = Evarconv.consider_remaining_unif_problems ~flags ~with_ho:true env sigma in
      sigma, clenv_advance sigma clenv
    with _ -> sigma, clenv in
  let sigma =
    if with_classes then
      let sigma = Typeclasses.resolve_typeclasses ~filter:Typeclasses.all_evars
        (* Don't split as this can result in typeclasses not failing due
           to initial holes not being marked as "mandatory". *)
        ~split:false ~fail:(not with_evars) env sigma
      in Typeclasses.mark_unresolvables ~filter:Typeclasses.all_goals sigma
    else sigma
  in
  let run sigma =
    (** Declare the future goals here, as they should become subgoals of this refine. *)
    let declare_goal sigma h =
      let ev, _ = destEvar sigma h.hole_evar in
      declare_future_goal ev sigma
    in
    let sigma = List.fold_left declare_goal sigma (clenv_holes clenv) in
    let v = EConstr.of_constr (nf_betaiota env (EConstr.Unsafe.to_constr (clenv_val clenv))) in
    (** This renaming hack should really stop at 8.6 *)
    if Flags.version_less_or_equal Flags.Current then
      rename_term env sigma v
    else sigma, v
  in
  let reduce_goal gl =
    let sigma = Proofview.Goal.sigma gl in
    let concl = Proofview.Goal.concl gl in
    let glev = Proofview.Goal.goal gl in
    (* For compatibility: beta iota reduction *)
    let concl = Reductionops.clos_norm_flags CClosure.betaiota env sigma concl in
    let evi = Evd.find sigma glev in
    let evi = Typeclasses.mark_unresolvable evi in
    let sigma = Evd.add sigma glev { evi with evar_concl = EConstr.Unsafe.to_constr concl } in
    Proofview.Unsafe.tclEVARS sigma
  in
  Proofview.Unsafe.tclEVARS sigma <*>
    clenv_check_dep_holes with_evars sigma ?origsigma clenv >>= (fun deps ->
  (Refine.refine ~typecheck:false run) <*>
  (if shelve_subgoals then shelve_goals deps else tclUNIT ()) <*>
    Proofview.Goal.nf_enter reduce_goal)
  end

open Unification

let dft = default_unify_flags

open Proofview.Notations

let clenv_refine_no_check
      ?(with_evars=false) ?(with_classes=true) ?(shelve_subgoals=true)
      ?(flags=dft ()) ?origsigma clenv =
  let flags = flags_of flags in
  Proofview.tclEVARMAP >>= fun sigma ->
  clenv_refine_gen ~with_evars ~with_classes ~shelve_subgoals ?origsigma
                   flags (sigma, clenv)

let clenv_refine2 ?(with_evars=false) ?(with_classes=true) ?(shelve_subgoals=true)
                  ?(flags=dft ()) ?origsigma clenv =
  let flags = flags_of flags in
  let tac = clenv_unify_concl flags clenv in
  Ftactic.run tac
   (clenv_refine_gen ~with_evars ~with_classes ~shelve_subgoals ?origsigma flags)

(** The dependent holes turned into subgoals are
    evars of the clause which are dependent in other hypotheses of the clause,
    whether or not they appear in the instantiated conclusion.
 *)

let clenv_refine_bindings
    ?(with_evars=false) ?(with_classes=true) ?(shelve_subgoals=true)
    ?(flags=dft ()) ~hyps_only ~delay_bindings b ?origsigma clenv =
  let open Proofview in
  let flags = flags_of flags in
  Proofview.Goal.enter begin fun gl ->
    let env = Proofview.Goal.env gl in
    let sigma = Proofview.Goal.sigma gl in
    let sigma, clenv, bindings =
      if delay_bindings then
        sigma, clenv, Some (None, false, b)
      else
        try let sigma, clenv = Clenv.solve_evar_clause env sigma ~hyps_only clenv b in
            sigma, clenv, None
        with e -> sigma, clenv, Some (Some e, hyps_only, b)
    in
    let tac = clenv_unify_concl flags clenv in
    (Unsafe.tclEVARS sigma) <*>
    (Ftactic.run tac
      (fun (sigma, clenv) ->
        try let sigma, clenv =
          match bindings with
          | Some (exn, hyps_only, b) ->
             (* Hack to make [exists 0] on [Σ x : nat, True] work, we
                use implicit bindings for a hole that's not dependent
                after unification, but reuse the typing information. *)
             Clenv.solve_evar_clause env sigma ~hyps_only clenv b
          | None -> sigma, clenv_recompute_deps sigma ~hyps_only:false clenv
        in
        clenv_refine_gen ~with_evars ~with_classes ~shelve_subgoals ?origsigma
                         flags (sigma, clenv)
        with e when Pretype_errors.precatchable_exception e -> Proofview.tclZERO e))
  end

let res_pf ?(with_evars=false) ?(with_classes=true) ?(flags=dft ()) clenv =
  Proofview.Goal.enter begin fun gl ->
    let clenv = clenv_unique_resolver ~flags clenv gl in
    clenv_refine with_evars ~with_classes clenv
  end

let clenv_solve_clause_constraints ?(flags=dft ()) ~with_ho clenv =
  let open Proofview in
  tclENV >>= fun env ->
  tclEVARMAP >>= fun sigma ->
    try
      let flags = flags_of flags in
      let sigma' =
        Evarconv.consider_remaining_unif_problems env ~flags ~with_ho sigma
      in Unsafe.tclEVARS sigma' <*> tclUNIT (clenv_advance sigma' clenv)
    with e -> tclZERO e

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
let unify ?(flags=fail_quick_unif_flags) ?(with_ho=true) m =
  Proofview.Goal.enter begin fun gl ->
    let env = Tacmach.New.pf_env gl in
    let n = Tacmach.New.pf_concl (Proofview.Goal.assume gl) in
    let sigma = Tacmach.New.project gl in
    try
      let sigma = Evarutil.add_unification_pb (CONV,env,m,n) sigma in
      let flags = Unification.flags_of flags in
      let sigma = Evarconv.consider_remaining_unif_problems ~flags ~with_ho env sigma in
	Proofview.Unsafe.tclEVARSADVANCE sigma
    with e when CErrors.noncritical e -> Proofview.tclZERO e
  end
