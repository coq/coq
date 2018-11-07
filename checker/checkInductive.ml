(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Sorts
open Pp
open Declarations
open Environ
open Names
open CErrors
open Univ
open Util
open Constr

let check_kind env ar u =
  match Constr.kind (snd (Reduction.dest_prod env ar)) with
  | Sort (Sorts.Type u') when Univ.Universe.equal u' (Univ.Universe.make u) -> ()
  | _ -> failwith "not the correct sort"

let check_polymorphic_arity env params par =
  let pl = par.template_param_levels in
  let rec check_p env pl params =
    let open Context.Rel.Declaration in
    match pl, params with
        Some u::pl, LocalAssum (na,ty)::params ->
          check_kind env ty u;
          check_p (push_rel (LocalAssum (na,ty)) env) pl params
      | None::pl,d::params -> check_p (push_rel d env) pl params
      | [], _ -> ()
      | _ -> failwith "check_poly: not the right number of params" in
  check_p env pl (List.rev params)

let conv_ctxt_prefix env (ctx1:rel_context) ctx2 =
  let rec chk env rctx1 rctx2 =
    let open Context.Rel.Declaration in
    match rctx1, rctx2 with
        (LocalAssum (_,ty1) as d1)::rctx1', LocalAssum (_,ty2)::rctx2' ->
          Reduction.conv env ty1 ty2;
          chk (push_rel d1 env) rctx1' rctx2'
      | (LocalDef (_,bd1,ty1) as d1)::rctx1', LocalDef (_,bd2,ty2)::rctx2' ->
          Reduction.conv env ty1 ty2;
          Reduction.conv env bd1 bd2;
          chk (push_rel d1 env) rctx1' rctx2'
      | [],_ -> ()
      | _ -> failwith "non convertible contexts" in
  chk env (List.rev ctx1) (List.rev ctx2)

(* check information related to inductive arity *)
let typecheck_arity env params inds =
  let nparamargs = Context.Rel.nhyps params in
  let nparamdecls = Context.Rel.length params in
  let check_arity arctxt = function
    | RegularArity mar ->
        let ar = mar.mind_user_arity in
        let _ = Typeops.infer_type env ar in
        Reduction.conv env (Term.it_mkProd_or_LetIn (Constr.mkSort mar.mind_sort) arctxt) ar;
        ar
    | TemplateArity par ->
      check_polymorphic_arity env params par;
      Term.it_mkProd_or_LetIn (Constr.mkSort(Sorts.Type par.template_level)) arctxt
  in
  let env_arities =
    Array.fold_left
      (fun env_ar ind ->
        let ar_ctxt = ind.mind_arity_ctxt in
        let _ = Typeops.check_context env ar_ctxt in
        conv_ctxt_prefix env params ar_ctxt;
        (* Arities (with params) are typed-checked here *)
        let arity = check_arity ar_ctxt ind.mind_arity in
        (* mind_nrealargs *)
        let nrealargs = Context.Rel.nhyps ar_ctxt - nparamargs in
        if ind.mind_nrealargs <> nrealargs then
             failwith "bad number of real inductive arguments";
        let nrealargs_ctxt = Context.Rel.length ar_ctxt - nparamdecls in
        if ind.mind_nrealdecls <> nrealargs_ctxt then
             failwith "bad length of real inductive arguments signature";
        (* We do not need to generate the universe of full_arity; if
           later, after the validation of the inductive definition,
           full_arity is used as argument or subject to cast, an
           upper universe will be generated *)
        let id = ind.mind_typename in
        let env_ar' = push_rel (Context.Rel.Declaration.LocalAssum (Name id, arity)) env_ar in
        env_ar')
      env
      inds in
  let env_ar_par = push_rel_context params env_arities in
  env_arities, env_ar_par

(* Check that the subtyping information inferred for inductive types in the block is correct. *)
(* This check produces a value of the unit type if successful or raises an anomaly if check fails. *)
let check_subtyping cumi paramsctxt env arities =
    let numparams = Context.Rel.nhyps paramsctxt in
  (** In [env] we already have [ Var(0) ... Var(n-1) |- cst ] available.
      We must produce the substitution σ : [ Var(i) -> Var (i + n) | 0 <= i < n]
      and push the constraints [ Var(n) ... Var(2n - 1) |- cst{σ} ], together
      with the cumulativity constraints [ cumul_cst ]. *)
  let uctx = ACumulativityInfo.univ_context cumi in
  let len = AUContext.size uctx in
  let inst = Instance.of_array @@ Array.init len (fun i -> Level.var (i + len)) in

  let other_context = ACumulativityInfo.univ_context cumi in
  let uctx_other = UContext.make (inst, AUContext.instantiate inst other_context) in
  let cumul_cst =
    Array.fold_left_i (fun i csts var ->
        match var with
        | Variance.Irrelevant -> csts
        | Variance.Covariant -> Constraint.add (Level.var i,Le,Level.var (i+len)) csts
        | Variance.Invariant -> Constraint.add (Level.var i,Eq,Level.var (i+len)) csts)
      Constraint.empty (ACumulativityInfo.variance cumi)
  in
  let env = Environ.push_context uctx_other env in
  let env = Environ.add_constraints cumul_cst env in
  let dosubst = Vars.subst_instance_constr inst in
    (* process individual inductive types: *)
    Array.iter (fun { mind_user_lc = lc; mind_arity = arity } ->
      match arity with
        | RegularArity { mind_user_arity = full_arity} ->
           Indtypes.check_subtyping_arity_constructor env dosubst full_arity numparams true;
           Array.iter (fun cnt -> Indtypes.check_subtyping_arity_constructor env dosubst cnt numparams false) lc
        | TemplateArity _ ->
          anomaly ~label:"check_subtyping"
            Pp.(str "template polymorphism and cumulative polymorphism are not compatible")
    ) arities

(* An inductive definition is a "unit" if it has only one constructor
   and that all arguments expected by this constructor are
   logical, this is the case for equality, conjunction of logical properties
*)
let is_unit constrsinfos =
  match constrsinfos with  (* One info = One constructor *)
   | [|constrinfos|] -> Univ.is_type0m_univ constrinfos
   | [||] -> (* type without constructors *) true
   | _ -> false

let small_unit constrsinfos =
  let issmall = Array.for_all Univ.is_small_univ constrsinfos
  and isunit = is_unit constrsinfos in
  issmall, isunit

let all_sorts = [InProp;InSet;InType]
let small_sorts = [InProp;InSet]
let logical_sorts = [InProp]

let allowed_sorts issmall isunit s =
  match Sorts.family s with
  (* Type: all elimination allowed *)
  | InType -> all_sorts

  (* Small Set is predicative: all elimination allowed *)
  | InSet when issmall -> all_sorts

  (* Large Set is necessarily impredicative: forbids large elimination *)
  | InSet -> small_sorts

  (* Unitary/empty Prop: elimination to all sorts are realizable *)
  (* unless the type is large. If it is large, forbids large elimination *)
  (* which otherwise allows simulating the inconsistent system Type:Type *)
  | InProp when isunit -> if issmall then all_sorts else small_sorts

  (* Other propositions: elimination only to Prop *)
  | InProp -> logical_sorts

let check_predicativity env s small level =
  match s, engagement env with
      Type u, _ ->
        (* let u' = fresh_local_univ () in *)
        (* let cst = *)
        (*   merge_constraints (enforce_leq u u' empty_constraint) *)
        (*     (universes env) in *)
        if not (UGraph.check_leq (universes env) level u) then
          failwith "impredicative Type inductive type"
    | Set, ImpredicativeSet -> ()
    | Set, _ ->
        if not small then failwith "impredicative Set inductive type"
    | Prop,_ -> ()

let sort_of_ind = function
  | RegularArity mar -> mar.mind_sort
  | TemplateArity par -> Type par.template_level

let compute_elim_sorts env_ar params arity lc =
  let inst = Context.Rel.to_extended_list Constr.mkRel 0 params in
  let env_params = push_rel_context params env_ar in
  let lc = Array.map
    (fun c ->
      Reduction.hnf_prod_applist env_params (Vars.lift (Context.Rel.length params) c) inst)
    lc in
  let s = sort_of_ind arity in
  let infos = Array.map (Indtypes.infos_and_sort env_params) lc in
  let (small,unit) = small_unit infos in
  (* We accept recursive unit types... *)
  (* compute the max of the sorts of the products of the constructor type *)
  let min = if Array.length lc > 1 then Universe.type0 else Universe.type0m in
  let level = Array.fold_left (fun max l -> Universe.sup max l) min infos in
  check_predicativity env_ar s small level;
  allowed_sorts small unit s

let typecheck_one_inductive env params mip =
  (* mind_typename and mind_consnames not checked *)
  (* mind_reloc_tbl, mind_nb_constant, mind_nb_args not checked (VM) *)
  (* mind_arity_ctxt, mind_arity, mind_nrealargs DONE (typecheck_arity) *)
  (* mind_user_lc *)
  let _ = Array.map (Typeops.infer_type env) mip.mind_user_lc in
  (* mind_nf_lc *)
  let _ = Array.map (Typeops.infer_type env) mip.mind_nf_lc in
  Array.iter2 (Reduction.conv env) mip.mind_nf_lc mip.mind_user_lc;
  (* mind_consnrealdecls *)
  let check_cons_args c n =
    let ctx,_ = Term.decompose_prod_assum c in
    if n <> Context.Rel.length ctx - Context.Rel.length params then
      failwith "bad number of real constructor arguments" in
  Array.iter2 check_cons_args mip.mind_nf_lc mip.mind_consnrealdecls;
  (* mind_kelim: checked by positivity criterion ? *)
  let sorts =
    compute_elim_sorts env params mip.mind_arity mip.mind_nf_lc in
  let reject_sort s = not (List.mem_f Sorts.family_equal s sorts) in
  if List.exists reject_sort mip.mind_kelim then
    failwith "elimination not allowed";
  (* mind_recargs: checked by positivity criterion *)
  ()

let check_inductive env kn mib =
  Flags.if_verbose Feedback.msg_notice (str "  checking mutind block: " ++ MutInd.print kn);
  (* check mind_constraints: should be consistent with env *)
  let env0 =
    match mib.mind_universes with
    | Monomorphic_ind _ -> env
    | Polymorphic_ind auctx ->
      let uctx = Univ.AUContext.repr auctx in
      Environ.push_context uctx env
    | Cumulative_ind cumi ->
      let uctx = Univ.AUContext.repr (Univ.ACumulativityInfo.univ_context cumi) in
      Environ.push_context uctx env
  in
  (** Locally set the oracle for further typechecking *)
  let env0 = Environ.set_oracle env0 mib.mind_typing_flags.conv_oracle in
  (* check mind_record : TODO ? check #constructor = 1 ? *)
  (* check mind_finite : always OK *)
  (* check mind_ntypes *)
  if Array.length mib.mind_packets <> mib.mind_ntypes then
    user_err Pp.(str "not the right number of packets");
  (* check mind_params_ctxt *)
  let params = mib.mind_params_ctxt in
  let _ = Typeops.check_context env0 params in
  (* check mind_nparams *)
  if Context.Rel.nhyps params <> mib.mind_nparams then
    user_err Pp.(str "number the right number of parameters");
  (* mind_packets *)
  (*  - check arities *)
  let env_ar, env_ar_par = typecheck_arity env0 params mib.mind_packets in
  (*  - check constructor types *)
  Array.iter (typecheck_one_inductive env_ar params) mib.mind_packets;
  (* check the inferred subtyping relation *)
  let () =
    match mib.mind_universes with
    | Monomorphic_ind _ | Polymorphic_ind _ -> ()
    | Cumulative_ind acumi ->
      check_subtyping acumi params env_ar mib.mind_packets
  in
  (* check mind_nparams_rec: positivity condition *)
  let packets = Array.map (fun p -> (p.mind_typename, Array.to_list p.mind_consnames, p.mind_user_lc, (p.mind_arity_ctxt,p.mind_arity))) mib.mind_packets in
  let _ = Indtypes.check_positivity ~chkpos:true kn env_ar_par mib.mind_params_ctxt mib.mind_finite packets in
  (* check mind_equiv... *)
  (* Now we can add the inductive *)
  add_mind kn mib env
