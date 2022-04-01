(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open Names
open Indfun_common
module RelDecl = Context.Rel.Declaration

let observe_tac s =
  New.observe_tac ~header:(Pp.str "observation") (fun _ _ -> Pp.str s)

(*
   Construct a fixpoint as a Glob_term
   and not as a constr
*)
let rec abstract_glob_constr c = function
  | [] -> c
  | Constrexpr.CLocalDef (x, b, t) :: bl ->
    Constrexpr_ops.mkLetInC (x, b, t, abstract_glob_constr c bl)
  | Constrexpr.CLocalAssum (idl, k, t) :: bl ->
    List.fold_right
      (fun x b -> Constrexpr_ops.mkLambdaC ([x], k, t, b))
      idl
      (abstract_glob_constr c bl)
  | Constrexpr.CLocalPattern _ :: bl -> assert false

let interp_casted_constr_with_implicits env sigma impls c =
  Constrintern.intern_gen Pretyping.WithoutTypeConstraint env sigma ~impls c

let build_newrecursive lnameargsardef =
  let env0 = Global.env () in
  let sigma = Evd.from_env env0 in
  let rec_sign, rec_impls =
    List.fold_left
      (fun (env, impls) {Vernacexpr.fname = {CAst.v = recname}; binders; rtype} ->
        let arityc = Constrexpr_ops.mkCProdN binders rtype in
        let arity, _ctx = Constrintern.interp_type env0 sigma arityc in
        let evd = Evd.from_env env0 in
        let evd, (_, (_, impls')) =
          Constrintern.interp_context_evars ~program_mode:false env evd binders
        in
        let impl =
          Constrintern.compute_internalization_data env0 evd recname
            Constrintern.Recursive arity impls'
        in
        let open Context.Named.Declaration in
        let r = Sorts.Relevant in
        (* TODO relevance *)
        ( EConstr.push_named
            (LocalAssum (Context.make_annot recname r, arity))
            env
        , Id.Map.add recname impl impls ))
      (env0, Constrintern.empty_internalization_env)
      lnameargsardef
  in
  let recdef =
    (* Declare local notations *)
    let f {Vernacexpr.binders; body_def} =
      match body_def with
      | Some body_def ->
        let def = abstract_glob_constr body_def binders in
        interp_casted_constr_with_implicits rec_sign sigma rec_impls def
      | None ->
        CErrors.user_err
          (Pp.str "Body of Function must be given.")
    in
    Vernacstate.System.protect (List.map f) lnameargsardef
  in
  (recdef, rec_impls)

(* Checks whether or not the mutual bloc is recursive *)
let is_rec names =
  let open Glob_term in
  let names = List.fold_right Id.Set.add names Id.Set.empty in
  let check_id id names = Id.Set.mem id names in
  let rec lookup names gt =
    match DAst.get gt with
    | GVar id -> check_id id names
    | GRef _ | GEvar _ | GPatVar _ | GSort _ | GHole _ | GInt _ | GFloat _ ->
      false
    | GCast (b, _, _) -> lookup names b
    | GRec _ -> CErrors.user_err (Pp.str "GRec not handled")
    | GIf (b, _, lhs, rhs) ->
      lookup names b || lookup names lhs || lookup names rhs
    | GProd (na, _, t, b) | GLambda (na, _, t, b) ->
      lookup names t
      || lookup (Nameops.Name.fold_right Id.Set.remove na names) b
    | GLetIn (na, b, t, c) ->
      lookup names b
      || Option.cata (lookup names) true t
      || lookup (Nameops.Name.fold_right Id.Set.remove na names) c
    | GLetTuple (nal, _, t, b) ->
      lookup names t
      || lookup
           (List.fold_left
              (fun acc na -> Nameops.Name.fold_right Id.Set.remove na acc)
              names nal)
           b
    | GApp (c, args) | GProj (_, args, c) -> List.exists (lookup names) (c :: args)
    | GArray (_u, t, def, ty) ->
      Array.exists (lookup names) t || lookup names def || lookup names ty
    | GCases (_, _, el, brl) ->
      List.exists (fun (e, _) -> lookup names e) el
      || List.exists (lookup_br names) brl
  and lookup_br names {CAst.v = idl, _, rt} =
    let new_names = List.fold_right Id.Set.remove idl names in
    lookup new_names rt
  in
  lookup names

let rec rebuild_bl aux bl typ =
  let open Constrexpr in
  match (bl, typ) with
  | [], _ -> (List.rev aux, typ)
  | CLocalAssum (nal, bk, _) :: bl', typ -> rebuild_nal aux bk bl' nal typ
  | CLocalDef (na, _, _) :: bl', {CAst.v = CLetIn (_, nat, ty, typ')} ->
    rebuild_bl (Constrexpr.CLocalDef (na, nat, ty) :: aux) bl' typ'
  | _ -> assert false

and rebuild_nal aux bk bl' nal typ =
  let open Constrexpr in
  match (nal, typ) with
  | _, {CAst.v = CProdN ([], typ)} -> rebuild_nal aux bk bl' nal typ
  | [], _ -> rebuild_bl aux bl' typ
  | ( na :: nal
    , {CAst.v = CProdN (CLocalAssum (na' :: nal', bk', nal't) :: rest, typ')} )
    ->
    if Name.equal na.CAst.v na'.CAst.v || Name.is_anonymous na'.CAst.v then
      let assum = CLocalAssum ([na], bk, nal't) in
      let new_rest =
        if nal' = [] then rest else CLocalAssum (nal', bk', nal't) :: rest
      in
      rebuild_nal (assum :: aux) bk bl' nal
        (CAst.make @@ CProdN (new_rest, typ'))
    else
      let assum = CLocalAssum ([na'], bk, nal't) in
      let new_rest =
        if nal' = [] then rest else CLocalAssum (nal', bk', nal't) :: rest
      in
      rebuild_nal (assum :: aux) bk bl' (na :: nal)
        (CAst.make @@ CProdN (new_rest, typ'))
  | _ -> assert false

let rebuild_bl aux bl typ = rebuild_bl aux bl typ

let recompute_binder_list fixpoint_exprl =
  let fixl =
    List.map
      (fun fix ->
        Vernacexpr.
          { fix with
            rec_order =
              ComFixpoint.adjust_rec_order ~structonly:false fix.binders
                fix.rec_order })
      fixpoint_exprl
  in
  let (_, _, _, typel), _, ctx, _ =
    ComFixpoint.interp_fixpoint ~check_recursivity:false ~cofix:false fixl
  in
  let constr_expr_typel =
    with_full_print
      (List.map (fun c ->
           Constrextern.extern_constr (Global.env ()) (Evd.from_ctx ctx)
             (EConstr.of_constr c)))
      typel
  in
  let fixpoint_exprl_with_new_bl =
    List.map2
      (fun ({Vernacexpr.binders} as fp) fix_typ ->
        let binders, rtype = rebuild_bl [] binders fix_typ in
        {fp with Vernacexpr.binders; rtype})
      fixpoint_exprl constr_expr_typel
  in
  fixpoint_exprl_with_new_bl

let rec local_binders_length = function
  (* Assume that no `{ ... } contexts occur *)
  | [] -> 0
  | Constrexpr.CLocalDef _ :: bl -> 1 + local_binders_length bl
  | Constrexpr.CLocalAssum (idl, _, _) :: bl ->
    List.length idl + local_binders_length bl
  | Constrexpr.CLocalPattern _ :: bl -> assert false

let prepare_body {Vernacexpr.binders} rt =
  let n = local_binders_length binders in
  (*   Pp.msgnl (str "nb lambda to chop : " ++ str (string_of_int n) ++ fnl () ++Printer.pr_glob_constr rt); *)
  let fun_args, rt' = chop_rlambda_n n rt in
  (fun_args, rt')

let build_functional_principle env (sigma : Evd.evar_map) old_princ_type sorts funs
    _i proof_tac hook =
  (* First we get the type of the old graph principle *)
  let mutr_nparams =
    (Tactics.compute_elim_sig sigma (EConstr.of_constr old_princ_type))
      .Tactics.nparams
  in
  let new_principle_type =
    Functional_principles_types.compute_new_princ_type_from_rel (Global.env ())
      (Array.map Constr.mkConstU funs)
      sorts old_princ_type
  in
  let sigma, _ =
    Typing.type_of ~refresh:true env sigma
      (EConstr.of_constr new_principle_type)
  in
  let map (c, u) = EConstr.mkConstU (c, EConstr.EInstance.make u) in
  let ftac = proof_tac (Array.map map funs) mutr_nparams in
  let uctx = Evd.evar_universe_context sigma in
  let typ = EConstr.of_constr new_principle_type in
  let body, typ, univs, _safe, _uctx =
    Declare.build_by_tactic env ~uctx ~poly:false ~typ ftac
  in
  (* uctx was ignored before *)
  let hook = Declare.Hook.make (hook new_principle_type) in
  (body, typ, univs, hook, sigma)

let change_property_sort evd toSort princ princName =
  let open Context.Rel.Declaration in
  let princ = EConstr.of_constr princ in
  let princ_info = Tactics.compute_elim_sig evd princ in
  let change_sort_in_predicate decl =
    LocalAssum
      ( get_annot decl
      , let args, ty =
          Term.decompose_prod (EConstr.Unsafe.to_constr (get_type decl))
        in
        let s = Constr.destSort ty in
        Global.add_constraints
          (UnivSubst.enforce_leq_sort
             toSort s Univ.Constraints.empty);
        Term.compose_prod args (Constr.mkSort toSort) )
  in
  let evd, princName_as_constr =
    Evd.fresh_global (Global.env ()) evd
      (Option.get (Constrintern.locate_reference (Libnames.qualid_of_ident princName)))
  in
  let init =
    let nargs =
      princ_info.Tactics.nparams + List.length princ_info.Tactics.predicates
    in
    Constr.mkApp
      ( EConstr.Unsafe.to_constr princName_as_constr
      , Array.init nargs (fun i -> Constr.mkRel (nargs - i)) )
  in
  ( evd
  , Term.it_mkLambda_or_LetIn
      (Term.it_mkLambda_or_LetIn init
         (List.map change_sort_in_predicate princ_info.Tactics.predicates))
      (List.map
         (fun d -> Termops.map_rel_decl EConstr.Unsafe.to_constr d)
         princ_info.Tactics.params) )

let generate_functional_principle (evd : Evd.evar_map ref) old_princ_type sorts
    new_princ_name funs i proof_tac =
  try
    let f = funs.(i) in
    let sigma, type_sort = Evd.fresh_sort_in_family !evd Sorts.InType in
    evd := sigma;
    let new_sorts =
      match sorts with
      | None -> Array.make (Array.length funs) type_sort
      | Some a -> a
    in
    let base_new_princ_name, new_princ_name =
      match new_princ_name with
      | Some id -> (id, id)
      | None ->
        let id_of_f = Label.to_id (Constant.label (fst f)) in
        (id_of_f, Indrec.make_elimination_ident id_of_f (Sorts.family type_sort))
    in
    let names = ref [new_princ_name] in
    let hook new_principle_type _ =
      if Option.is_empty sorts then (
        (*     let id_of_f = Label.to_id (con_label f) in *)
        let register_with_sort fam_sort =
          let evd' = Evd.from_env (Global.env ()) in
          let evd', s = Evd.fresh_sort_in_family evd' fam_sort in
          let name =
            Indrec.make_elimination_ident base_new_princ_name fam_sort
          in
          let evd', value =
            change_property_sort evd' s new_principle_type new_princ_name
          in
          let evd' =
            fst
              (Typing.type_of ~refresh:true (Global.env ()) evd'
                 (EConstr.of_constr value))
          in
          (* Pp.msgnl (str "new principle := " ++ pr_lconstr value); *)
          let univs = Evd.univ_entry ~poly:false evd' in
          let ce = Declare.definition_entry ~univs value in
          ignore
            (Declare.declare_constant ~name
               ~kind:Decls.(IsDefinition Scheme)
               (Declare.DefinitionEntry ce));
          Declare.definition_message name;
          names := name :: !names
        in
        register_with_sort Sorts.InProp;
        register_with_sort Sorts.InSet )
    in
    let body, types, univs, hook, sigma0 =
      build_functional_principle (Global.env ()) !evd old_princ_type new_sorts funs i proof_tac
        hook
    in
    evd := sigma0;
    (* Pr  1278 :
       Don't forget to close the goal if an error is raised !!!!
    *)
    let uctx = Evd.evar_universe_context sigma in
    let entry = Declare.definition_entry ~univs ?types body in
    let (_ : Names.GlobRef.t) =
      Declare.declare_entry ~name:new_princ_name ~hook
        ~kind:Decls.(IsProof Theorem)
        ~impargs:[] ~uctx entry
    in
    ()
  with e when CErrors.noncritical e -> raise (Defining_principle e)

let generate_principle (evd : Evd.evar_map ref) pconstants on_error is_general
    do_built fix_rec_l recdefs
    (continue_proof :
         int
      -> Names.Constant.t array
      -> EConstr.constr array
      -> int
      -> unit Proofview.tactic) : unit =
  let names =
    List.map (function {Vernacexpr.fname = {CAst.v = name}} -> name) fix_rec_l
  in
  let fun_bodies = List.map2 prepare_body fix_rec_l recdefs in
  let funs_args = List.map fst fun_bodies in
  let funs_types =
    List.map (function {Vernacexpr.rtype} -> rtype) fix_rec_l
  in
  try
    (* We then register the Inductive graphs of the functions  *)
    Glob_term_to_relation.build_inductive !evd pconstants funs_args funs_types
      recdefs;
    if do_built then begin
      (*i The next call to mk_rel_id is valid since we have just construct the graph
         Ensures by : do_built
        i*)
      let f_R_mut = Libnames.qualid_of_ident @@ mk_rel_id (List.nth names 0) in
      let ind_kn =
        fst
          (locate_with_msg
             Pp.(Libnames.pr_qualid f_R_mut ++ str ": Not an inductive type!")
             locate_ind f_R_mut)
      in
      let fname_kn {Vernacexpr.fname} =
        let f_ref = Libnames.qualid_of_ident ?loc:fname.CAst.loc fname.CAst.v in
        locate_with_msg
          Pp.(Libnames.pr_qualid f_ref ++ str ": Not an inductive type!")
          locate_constant f_ref
      in
      let funs_kn = Array.of_list (List.map fname_kn fix_rec_l) in
      let _ =
        List.map_i
          (fun i _x ->
            let env = Global.env () in
            let princ = Indrec.lookup_eliminator env (ind_kn, i) Sorts.InProp in
            let evd = ref (Evd.from_env env) in
            let evd', uprinc = Evd.fresh_global env !evd princ in
            let _ = evd := evd' in
            let sigma, princ_type =
              Typing.type_of ~refresh:true env !evd uprinc
            in
            evd := sigma;
            let princ_type = EConstr.Unsafe.to_constr princ_type in
            generate_functional_principle evd princ_type None None
              (Array.of_list pconstants) (* funs_kn *)
              i
              (continue_proof 0 [|funs_kn.(i)|]))
          0 fix_rec_l
      in
      Array.iter (add_Function is_general) funs_kn;
      ()
    end
  with e when CErrors.noncritical e -> on_error names e

let register_struct is_rec fixpoint_exprl =
  let open EConstr in
  match fixpoint_exprl with
  | [{Vernacexpr.fname; univs; binders; rtype; body_def}] when not is_rec ->
    let body =
      match body_def with
      | Some body -> body
      | None ->
        CErrors.user_err
          Pp.(str "Body of Function must be given.")
    in
    ComDefinition.do_definition ~name:fname.CAst.v ~poly:false
      ~kind:Decls.Definition univs binders None body (Some rtype);
    let evd, rev_pconstants =
      List.fold_left
        (fun (evd, l) {Vernacexpr.fname} ->
          let evd, c =
            Evd.fresh_global (Global.env ()) evd
              (Option.get (Constrintern.locate_reference
                 (Libnames.qualid_of_ident fname.CAst.v)))
          in
          let cst, u = destConst evd c in
          let u = EInstance.kind evd u in
          (evd, (cst, u) :: l))
        (Evd.from_env (Global.env ()), [])
        fixpoint_exprl
    in
    (None, evd, List.rev rev_pconstants)
  | _ ->
    ComFixpoint.do_fixpoint ~poly:false fixpoint_exprl;
    let evd, rev_pconstants =
      List.fold_left
        (fun (evd, l) {Vernacexpr.fname} ->
          let evd, c =
            Evd.fresh_global (Global.env ()) evd
              (Option.get (Constrintern.locate_reference
                 (Libnames.qualid_of_ident fname.CAst.v)))
          in
          let cst, u = destConst evd c in
          let u = EInstance.kind evd u in
          (evd, (cst, u) :: l))
        (Evd.from_env (Global.env ()), [])
        fixpoint_exprl
    in
    (None, evd, List.rev rev_pconstants)

let generate_correction_proof_wf f_ref tcc_lemma_ref is_mes functional_ref
    eq_ref rec_arg_num rec_arg_type relation (_ : int)
    (_ : Names.Constant.t array) (_ : EConstr.constr array) (_ : int) :
    unit Proofview.tactic =
  Functional_principles_proofs.prove_principle_for_gen
    (f_ref, functional_ref, eq_ref)
    tcc_lemma_ref is_mes rec_arg_num rec_arg_type relation

(* [generate_type g_to_f f graph i] build the completeness (resp. correctness) lemma type if [g_to_f = true]
   (resp. g_to_f = false) where [graph]  is the graph of [f] and is the [i]th function in the block.

   [generate_type true f i] returns
   \[\forall (x_1:t_1)\ldots(x_n:t_n), let fv := f x_1\ldots x_n in, forall res,
   graph\ x_1\ldots x_n\ res \rightarrow res = fv \] decomposed as the context and the conclusion

   [generate_type false f i] returns
   \[\forall (x_1:t_1)\ldots(x_n:t_n), let fv := f x_1\ldots x_n in, forall res,
   res = fv \rightarrow graph\ x_1\ldots x_n\ res\] decomposed as the context and the conclusion
*)

let generate_type evd g_to_f f graph =
  let open Context.Rel.Declaration in
  let open EConstr in
  let open EConstr.Vars in
  (*i we deduce the number of arguments of the function and its returned type from the graph i*)
  let evd', graph =
    Evd.fresh_global (Global.env ()) !evd
      (GlobRef.IndRef (fst (destInd !evd graph)))
  in
  evd := evd';
  let sigma, graph_arity = Typing.type_of (Global.env ()) !evd graph in
  evd := sigma;
  let ctxt, _ = decompose_prod_assum !evd graph_arity in
  let fun_ctxt, res_type =
    match ctxt with
    | [] | [_] -> CErrors.anomaly (Pp.str "Not a valid context.")
    | decl :: fun_ctxt -> (fun_ctxt, RelDecl.get_type decl)
  in
  let rec args_from_decl i accu = function
    | [] -> accu
    | LocalDef _ :: l -> args_from_decl (succ i) accu l
    | _ :: l ->
      let t = mkRel i in
      args_from_decl (succ i) (t :: accu) l
  in
  (*i We need to name the vars [res] and [fv] i*)
  let filter decl =
    match RelDecl.get_name decl with Name id -> Some id | Anonymous -> None
  in
  let named_ctxt = Id.Set.of_list (List.map_filter filter fun_ctxt) in
  let res_id =
    Namegen.next_ident_away_in_goal (Global.env ()) (Id.of_string "_res") named_ctxt
  in
  let fv_id =
    Namegen.next_ident_away_in_goal (Global.env ()) (Id.of_string "fv")
      (Id.Set.add res_id named_ctxt)
  in
  (*i we can then type the argument to be applied to the function [f] i*)
  let args_as_rels = Array.of_list (args_from_decl 1 [] fun_ctxt) in
  (*i
    the hypothesis [res = fv] can then be computed
    We will need to lift it by one in order to use it as a conclusion
    i*)
  let make_eq = make_eq () in
  let res_eq_f_of_args =
    mkApp (make_eq, [|lift 2 res_type; mkRel 1; mkRel 2|])
  in
  (*i
    The hypothesis [graph\ x_1\ldots x_n\ res] can then be computed
    We will need to lift it by one in order to use it as a conclusion
    i*)
  let args_and_res_as_rels = Array.of_list (args_from_decl 3 [] fun_ctxt) in
  let args_and_res_as_rels = Array.append args_and_res_as_rels [|mkRel 1|] in
  let graph_applied = mkApp (graph, args_and_res_as_rels) in
  (*i The [pre_context]  is the defined to be the context corresponding to
    \[\forall (x_1:t_1)\ldots(x_n:t_n), let fv := f x_1\ldots x_n in, forall res,  \]
    i*)
  let pre_ctxt =
    LocalAssum (Context.make_annot (Name res_id) Sorts.Relevant, lift 1 res_type)
    :: LocalDef
         ( Context.make_annot (Name fv_id) Sorts.Relevant
         , mkApp (f, args_as_rels)
         , res_type )
    :: fun_ctxt
  in
  (*i and we can return the solution depending on which lemma type we are defining i*)
  if g_to_f then
    ( LocalAssum (Context.make_annot Anonymous Sorts.Relevant, graph_applied)
      :: pre_ctxt
    , lift 1 res_eq_f_of_args
    , graph )
  else
    ( LocalAssum (Context.make_annot Anonymous Sorts.Relevant, res_eq_f_of_args)
      :: pre_ctxt
    , lift 1 graph_applied
    , graph )

(**
   [find_induction_principle f] searches and returns the [body] and the [type] of [f_rect]

   WARNING: while convertible, [type_of body] and [type] can be non equal
*)
let find_induction_principle evd f =
  let f_as_constant, _u =
    match EConstr.kind !evd f with
    | Constr.Const c' -> c'
    | _ -> CErrors.user_err Pp.(str "Must be used with a function")
  in
  match find_Function_infos f_as_constant with
  | None -> raise Not_found
  | Some infos -> (
    match infos.rect_lemma with
    | None -> raise Not_found
    | Some rect_lemma ->
      let evd', rect_lemma =
        Evd.fresh_global (Global.env ()) !evd (GlobRef.ConstRef rect_lemma)
      in
      let evd', typ =
        Typing.type_of ~refresh:true (Global.env ()) evd' rect_lemma
      in
      evd := evd';
      (rect_lemma, typ) )

(* [prove_fun_correct funs_constr graphs_constr schemes lemmas_types_infos i ]
   is the tactic used to prove correctness lemma.

   [funs_constr], [graphs_constr] [schemes] [lemmas_types_infos] are the mutually recursive functions
   (resp. graphs of the functions and principles and correctness lemma types) to prove correct.

   [i] is the indice of the function to prove correct

   The lemma to prove if suppose to have been generated by [generate_type] (in $\zeta$ normal form that is
   it looks like~:
   [\forall (x_1:t_1)\ldots(x_n:t_n), forall res,
   res = f x_1\ldots x_n in, \rightarrow graph\ x_1\ldots x_n\ res]


   The sketch of the proof is the following one~:
   \begin{enumerate}
   \item intros until $x_n$
   \item $functional\ induction\ (f.(i)\ x_1\ldots x_n)$ using schemes.(i)
   \item for each generated branch intro [res] and [hres :res = f x_1\ldots x_n], rewrite [hres] and the
   apply the corresponding constructor of the corresponding graph inductive.
   \end{enumerate}

*)

let rec generate_fresh_id x avoid i =
  if i == 0 then []
  else
    let id = Namegen.next_ident_away_in_goal (Global.env ()) x (Id.Set.of_list avoid) in
    id :: generate_fresh_id x (id :: avoid) (pred i)

let prove_fun_correct evd graphs_constr schemes lemmas_types_infos i :
    unit Proofview.tactic =
  let open Constr in
  let open EConstr in
  let open Context.Rel.Declaration in
  let open Tacmach in
  let open Tactics in
  let open Tacticals in
  Proofview.Goal.enter (fun g ->
      (* first of all we recreate the lemmas types to be used as predicates of the induction principle
         that is~:
         \[fun (x_1:t_1)\ldots(x_n:t_n)=> fun  fv => fun res => res = fv \rightarrow graph\ x_1\ldots x_n\ res\]
      *)
      (* we the get the definition of the graphs block *)
      let graph_ind, u = destInd evd graphs_constr.(i) in
      let kn = fst graph_ind in
      let mib, _ = Global.lookup_inductive graph_ind in
      (* and the principle to use in this lemma in $\zeta$ normal form *)
      let f_principle, princ_type = schemes.(i) in
      let princ_type = Reductionops.nf_zeta (Global.env ()) evd princ_type in
      let princ_infos = Tactics.compute_elim_sig evd princ_type in
      (* The number of args of the function is then easily computable *)
      let nb_fun_args =
        Termops.nb_prod (Proofview.Goal.sigma g) (Proofview.Goal.concl g) - 2
      in
      let args_names = generate_fresh_id (Id.of_string "x") [] nb_fun_args in
      let ids = args_names @ pf_ids_of_hyps g in
      (* Since we cannot ensure that the functional principle is defined in the
         environment and due to the bug #1174, we will need to pose the principle
         using a name
      *)
      let principle_id =
        Namegen.next_ident_away_in_goal (Global.env ()) (Id.of_string "princ")
          (Id.Set.of_list ids)
      in
      let ids = principle_id :: ids in
      (* We get the branches of the principle *)
      let branches = List.rev princ_infos.Tactics.branches in
      (* and built the intro pattern for each of them *)
      let intro_pats =
        List.map
          (fun decl ->
            List.map
              (fun id ->
                CAst.make @@ Tactypes.IntroNaming (Namegen.IntroIdentifier id))
              (generate_fresh_id (Id.of_string "y") ids
                 (List.length
                    (fst (decompose_prod_assum evd (RelDecl.get_type decl))))))
          branches
      in
      (* before building the full intro pattern for the principle *)
      let eq_ind = make_eq () in
      let eq_construct = mkConstructUi (destInd evd eq_ind, 1) in
      (* The next to referencies will be used to find out which constructor to apply in each branch *)
      let ind_number = ref 0 and min_constr_number = ref 0 in
      (* The tactic to prove the ith branch of the principle *)
      let prove_branch i pat =
        (* We get the identifiers of this branch *)
        let pre_args =
          List.fold_right
            (fun {CAst.v = pat} acc ->
              match pat with
              | Tactypes.IntroNaming (Namegen.IntroIdentifier id) -> id :: acc
              | _ -> CErrors.anomaly (Pp.str "Not an identifier."))
            pat []
        in
        (* and get the real args of the branch by unfolding the defined constant *)
        (*
         We can then recompute the arguments of the constructor.
         For each [hid] introduced by this branch, if [hid] has type
         $forall res, res=fv -> graph.(j)\ x_1\ x_n res$ the corresponding arguments of the constructor are
         [ fv (hid fv (refl_equal fv)) ].
         If [hid] has another type the corresponding argument of the constructor is [hid]
      *)
        let constructor_args g =
          List.fold_right
            (fun hid acc ->
              let type_of_hid = pf_get_hyp_typ hid g in
              let sigma = Proofview.Goal.sigma g in
              match EConstr.kind sigma type_of_hid with
              | Prod (_, _, t') -> (
                match EConstr.kind sigma t' with
                | Prod (_, t'', t''') -> (
                  match (EConstr.kind sigma t'', EConstr.kind sigma t''') with
                  | App (eq, args), App (graph', _)
                    when EConstr.eq_constr sigma eq eq_ind
                         && Array.exists
                              (EConstr.eq_constr_nounivs sigma graph')
                              graphs_constr ->
                    args.(2)
                    :: mkApp
                         ( mkVar hid
                         , [| args.(2)
                            ; mkApp (eq_construct, [|args.(0); args.(2)|]) |] )
                    :: acc
                  | _ -> mkVar hid :: acc )
                | _ -> mkVar hid :: acc )
              | _ -> mkVar hid :: acc)
            pre_args []
        in
        (* in fact we must also add the parameters to the constructor args *)
        let constructor_args g =
          let params_id =
            fst (List.chop princ_infos.Tactics.nparams args_names)
          in
          List.map mkVar params_id @ constructor_args g
        in
        (* We then get the constructor corresponding to this branch and
           modifies the references has needed i.e.
           if the constructor is the last one of the current inductive then
           add one the number of the inductive to take and add the number of constructor of the previous
           graph to the minimal constructor number
        *)
        let constructor =
          let constructor_num = i - !min_constr_number in
          let length =
            Array.length
              mib.Declarations.mind_packets.(!ind_number)
                .Declarations.mind_consnames
          in
          if constructor_num <= length then ((kn, !ind_number), constructor_num)
          else begin
            incr ind_number;
            min_constr_number := !min_constr_number + length;
            ((kn, !ind_number), 1)
          end
        in
        (* we can then build the final proof term *)
        let app_constructor g =
          applist (mkConstructU (constructor, u), constructor_args g)
        in
        (* an apply the tactic *)
        let res, hres =
          match
            generate_fresh_id (Id.of_string "z") ids (* @this_branche_ids *) 2
          with
          | [res; hres] -> (res, hres)
          | _ -> assert false
        in
        (* observe (str "constructor := " ++ Printer.pr_lconstr_env (pf_env g) app_constructor); *)
        tclTHENLIST
          [ observe_tac "h_intro_patterns "
              (match pat with [] -> tclIDTAC | _ -> intro_patterns false pat)
          ; (* unfolding of all the defined variables introduced by this branch *)
            (* observe_tac "unfolding" pre_tac; *)
            (* $zeta$ normalizing of the conclusion *)
            reduce
              (Genredexpr.Cbv
                 { Redops.all_flags with
                   Genredexpr.rDelta = false
                 ; Genredexpr.rConst = [] })
              Locusops.onConcl
          ; observe_tac "toto " (Proofview.tclUNIT ())
          ; (* introducing the result of the graph and the equality hypothesis *)
            observe_tac "introducing" (tclMAP Simple.intro [res; hres])
          ; (* replacing [res] with its value *)
            observe_tac "rewriting res value" (Equality.rewriteLR (mkVar hres))
          ; (* Conclusion *)
            observe_tac "exact"
              (Proofview.Goal.enter (fun g -> exact_check (app_constructor g)))
          ]
      in
      (* end of branche proof *)
      let lemmas =
        Array.map
          (fun (_, (ctxt, concl)) ->
            match ctxt with
            | [] | [_] | [_; _] -> CErrors.anomaly (Pp.str "bad context.")
            | hres :: res :: decl :: ctxt ->
              let res =
                EConstr.it_mkLambda_or_LetIn
                  (EConstr.it_mkProd_or_LetIn concl [hres; res])
                  ( LocalAssum (RelDecl.get_annot decl, RelDecl.get_type decl)
                  :: ctxt )
              in
              res)
          lemmas_types_infos
      in
      let param_names = fst (List.chop princ_infos.nparams args_names) in
      let params = List.map mkVar param_names in
      let lemmas =
        Array.to_list (Array.map (fun c -> applist (c, params)) lemmas)
      in
      (* The bindings of the principle
         that is the params of the principle and the different lemma types
      *)
      let bindings =
        let params_bindings, avoid =
          List.fold_left2
            (fun (bindings, avoid) decl p ->
              let id =
                Namegen.next_ident_away
                  (Nameops.Name.get_id (RelDecl.get_name decl))
                  (Id.Set.of_list avoid)
              in
              (p :: bindings, id :: avoid))
            ([], pf_ids_of_hyps g)
            princ_infos.params (List.rev params)
        in
        let lemmas_bindings =
          List.rev
            (fst
               (List.fold_left2
                  (fun (bindings, avoid) decl p ->
                    let id =
                      Namegen.next_ident_away
                        (Nameops.Name.get_id (RelDecl.get_name decl))
                        (Id.Set.of_list avoid)
                    in
                    ( Reductionops.nf_zeta (Proofview.Goal.env g)
                        (Proofview.Goal.sigma g) p
                      :: bindings
                    , id :: avoid ))
                  ([], avoid) princ_infos.predicates lemmas))
        in
        params_bindings @ lemmas_bindings
      in
      tclTHENLIST
        [ observe_tac "principle"
            (assert_by (Name principle_id) princ_type (exact_check f_principle))
        ; observe_tac "intro args_names" (tclMAP Simple.intro args_names)
        ; (* observe_tac "titi" (pose_proof (Name (Id.of_string "__")) (Reductionops.nf_beta Evd.empty  ((mkApp (mkVar principle_id,Array.of_list bindings))))); *)
          observe_tac "idtac" tclIDTAC
        ; tclTHENS
            (observe_tac "functional_induction"
               (Proofview.Goal.enter (fun gl ->
                    let term =
                      mkApp (mkVar principle_id, Array.of_list bindings)
                    in
                    tclTYPEOFTHEN ~refresh:true term (fun _ _ -> apply term))))
            (List.map_i
               (fun i pat ->
                 observe_tac
                   ("proving branch " ^ string_of_int i)
                   (prove_branch i pat))
               1 intro_pats) ])

(* [prove_fun_complete funs graphs schemes lemmas_types_infos i]
   is the tactic used to prove completeness lemma.

   [funcs], [graphs] [schemes] [lemmas_types_infos] are the mutually recursive functions
   (resp. definitions of the graphs of the functions, principles and correctness lemma types) to prove correct.

   [i] is the indice of the function to prove complete

   The lemma to prove if suppose to have been generated by [generate_type] (in $\zeta$ normal form that is
   it looks like~:
   [\forall (x_1:t_1)\ldots(x_n:t_n), forall res,
   graph\ x_1\ldots x_n\ res, \rightarrow  res = f x_1\ldots x_n in]


   The sketch of the proof is the following one~:
   \begin{enumerate}
   \item intros until $H:graph\ x_1\ldots x_n\ res$
   \item $elim\ H$ using schemes.(i)
   \item for each generated branch, intro  the news hyptohesis, for each such hyptohesis [h], if [h] has
   type [x=?] with [x] a variable, then subst [x],
   if [h] has type [t=?] with [t] not a variable then rewrite [t] in the subterms, else
   if [h] is a match then destruct it, else do just introduce it,
   after all intros, the conclusion should be a reflexive equality.
   \end{enumerate}

*)

let thin = Tactics.clear

(* [intros_with_rewrite] do the intros in each branch and treat each new hypothesis
       (unfolding, substituting, destructing cases \ldots)
*)
let tauto =
  let open Ltac_plugin in
  let dp = List.map Id.of_string ["Tauto"; "Init"; "Coq"] in
  let mp = ModPath.MPfile (DirPath.make dp) in
  let kn = KerName.make mp (Label.make "tauto") in
  Proofview.tclBIND (Proofview.tclUNIT ()) (fun () ->
      let body = Tacenv.interp_ltac kn in
      Tacinterp.eval_tactic body)

(* [generalize_dependent_of x hyp g]
   generalize every hypothesis which depends of [x] but [hyp]
*)
let generalize_dependent_of x hyp =
  let open Context.Named.Declaration in
  let open Tacticals in
  Proofview.Goal.enter (fun g ->
      tclMAP
        (function
          | LocalAssum ({Context.binder_name = id}, t)
            when (not (Id.equal id hyp))
                 && Termops.occur_var (Proofview.Goal.env g)
                      (Proofview.Goal.sigma g) x t ->
            tclTHEN (Tactics.generalize [EConstr.mkVar id]) (thin [id])
          | _ -> Proofview.tclUNIT ())
        (Proofview.Goal.hyps g))

let rec intros_with_rewrite () =
  observe_tac "intros_with_rewrite" (intros_with_rewrite_aux ())

and intros_with_rewrite_aux () : unit Proofview.tactic =
  let open Constr in
  let open EConstr in
  let open Tacmach in
  let open Tactics in
  let open Tacticals in
  Proofview.Goal.enter (fun g ->
      let eq_ind = make_eq () in
      let sigma = Proofview.Goal.sigma g in
      match EConstr.kind sigma (Proofview.Goal.concl g) with
      | Prod (_, t, t') -> (
        match EConstr.kind sigma t with
        | App (eq, args) when EConstr.eq_constr sigma eq eq_ind ->
          if
            Reductionops.is_conv (Proofview.Goal.env g) (Proofview.Goal.sigma g)
              args.(1) args.(2)
          then
            let id = pf_get_new_id (Id.of_string "y") g in
            tclTHENLIST [Simple.intro id; thin [id]; intros_with_rewrite ()]
          else if
            isVar sigma args.(1)
            && Environ.evaluable_named
                 (destVar sigma args.(1))
                 (Proofview.Goal.env g)
          then
            tclTHENLIST
              [ unfold_in_concl
                  [ ( Locus.AllOccurrences
                    , Tacred.EvalVarRef (destVar sigma args.(1)) ) ]
              ; tclMAP
                  (fun id ->
                    tclTRY
                      (unfold_in_hyp
                         [ ( Locus.AllOccurrences
                           , Tacred.EvalVarRef (destVar sigma args.(1)) ) ]
                         (destVar sigma args.(1), Locus.InHyp)))
                  (pf_ids_of_hyps g)
              ; intros_with_rewrite () ]
          else if
            isVar sigma args.(2)
            && Environ.evaluable_named
                 (destVar sigma args.(2))
                 (Proofview.Goal.env g)
          then
            tclTHENLIST
              [ unfold_in_concl
                  [ ( Locus.AllOccurrences
                    , Tacred.EvalVarRef (destVar sigma args.(2)) ) ]
              ; tclMAP
                  (fun id ->
                    tclTRY
                      (unfold_in_hyp
                         [ ( Locus.AllOccurrences
                           , Tacred.EvalVarRef (destVar sigma args.(2)) ) ]
                         (destVar sigma args.(2), Locus.InHyp)))
                  (pf_ids_of_hyps g)
              ; intros_with_rewrite () ]
          else if isVar sigma args.(1) then
            let id = pf_get_new_id (Id.of_string "y") g in
            tclTHENLIST
              [ Simple.intro id
              ; generalize_dependent_of (destVar sigma args.(1)) id
              ; tclTRY (Equality.rewriteLR (mkVar id))
              ; intros_with_rewrite () ]
          else if isVar sigma args.(2) then
            let id = pf_get_new_id (Id.of_string "y") g in
            tclTHENLIST
              [ Simple.intro id
              ; generalize_dependent_of (destVar sigma args.(2)) id
              ; tclTRY (Equality.rewriteRL (mkVar id))
              ; intros_with_rewrite () ]
          else
            let id = pf_get_new_id (Id.of_string "y") g in
            tclTHENLIST
              [ Simple.intro id
              ; tclTRY (Equality.rewriteLR (mkVar id))
              ; intros_with_rewrite () ]
        | Ind _
          when EConstr.eq_constr sigma t
                 (EConstr.of_constr
                    ( UnivGen.constr_of_monomorphic_global (Global.env ())
                    @@ Coqlib.lib_ref "core.False.type" )) ->
          tauto
        | Case (_, _, _, _, _, v, _) ->
          tclTHENLIST [simplest_case v; intros_with_rewrite ()]
        | LetIn _ ->
          tclTHENLIST
            [ reduce
                (Genredexpr.Cbv {Redops.all_flags with Genredexpr.rDelta = false})
                Locusops.onConcl
            ; intros_with_rewrite () ]
        | _ ->
          let id = pf_get_new_id (Id.of_string "y") g in
          tclTHENLIST [Simple.intro id; intros_with_rewrite ()] )
      | LetIn _ ->
        tclTHENLIST
          [ reduce
              (Genredexpr.Cbv {Redops.all_flags with Genredexpr.rDelta = false})
              Locusops.onConcl
          ; intros_with_rewrite () ]
      | _ -> Proofview.tclUNIT ())

let rec reflexivity_with_destruct_cases () =
  let open Constr in
  let open EConstr in
  let open Tacmach in
  let open Tactics in
  let open Tacticals in
  Proofview.Goal.enter (fun g ->
      let destruct_case () =
        try
          match
            EConstr.kind (Proofview.Goal.sigma g)
              (snd (destApp (Proofview.Goal.sigma g) (Proofview.Goal.concl g))).(
              2)
          with
          | Case (_, _, _, _, _, v, _) ->
            tclTHENLIST
              [ simplest_case v
              ; intros
              ; observe_tac "reflexivity_with_destruct_cases"
                  (reflexivity_with_destruct_cases ()) ]
          | _ -> reflexivity
        with e when CErrors.noncritical e -> reflexivity
      in
      let eq_ind = make_eq () in
      let my_inj_flags =
        Some
          { Equality.keep_proof_equalities = false
          ; injection_pattern_l2r_order = false
            (* probably does not matter; except maybe with dependent hyps *)
          }
      in
      let discr_inject =
        onAllHypsAndConcl (fun sc ->
            match sc with
            | None -> Proofview.tclUNIT ()
            | Some id ->
              Proofview.Goal.enter (fun g ->
                  match
                    EConstr.kind (Proofview.Goal.sigma g) (pf_get_hyp_typ id g)
                  with
                  | App (eq, [|_; t1; t2|])
                    when EConstr.eq_constr (Proofview.Goal.sigma g) eq eq_ind ->
                    if
                      Equality.discriminable (Proofview.Goal.env g)
                        (Proofview.Goal.sigma g) t1 t2
                    then Equality.discrHyp id
                    else if
                      Equality.injectable (Proofview.Goal.env g)
                        (Proofview.Goal.sigma g) ~keep_proofs:None t1 t2
                    then
                      tclTHENLIST
                        [ Equality.injHyp my_inj_flags ~injection_in_context:false None id
                        ; thin [id]
                        ; intros_with_rewrite () ]
                    else Proofview.tclUNIT ()
                  | _ -> Proofview.tclUNIT ()))
      in
      tclFIRST
        [ observe_tac "reflexivity_with_destruct_cases : reflexivity" reflexivity
        ; observe_tac "reflexivity_with_destruct_cases : destruct_case"
            (destruct_case ())
        ; (* We reach this point ONLY if
             the same value is matched (at least) two times
             along binding path.
             In this case, either we have a discriminable hypothesis and we are done,
             either at least an injectable one and we do the injection before continuing
          *)
          observe_tac "reflexivity_with_destruct_cases : others"
            (tclTHEN (tclPROGRESS discr_inject)
               (reflexivity_with_destruct_cases ())) ])

let prove_fun_complete funcs graphs schemes lemmas_types_infos i :
    unit Proofview.tactic =
  let open EConstr in
  let open Tacmach in
  let open Tactics in
  let open Tacticals in
  Proofview.Goal.enter (fun g ->
      (* We compute the types of the different mutually recursive lemmas
         in $\zeta$ normal form
      *)
      let lemmas =
        Array.map
          (fun (_, (ctxt, concl)) ->
            Reductionops.nf_zeta (Proofview.Goal.env g) (Proofview.Goal.sigma g)
              (EConstr.it_mkLambda_or_LetIn concl ctxt))
          lemmas_types_infos
      in
      (* We get the constant and the principle corresponding to this lemma *)
      let f = funcs.(i) in
      let graph_principle =
        Reductionops.nf_zeta (Proofview.Goal.env g) (Proofview.Goal.sigma g)
          (EConstr.of_constr schemes.(i))
      in
      tclTYPEOFTHEN graph_principle (fun sigma princ_type ->
          let princ_infos = Tactics.compute_elim_sig sigma princ_type in
          (* Then we get the number of argument of the function
             and compute a fresh name for each of them
          *)
          let nb_fun_args =
            Termops.nb_prod sigma (Proofview.Goal.concl g) - 2
          in
          let args_names =
            generate_fresh_id (Id.of_string "x") [] nb_fun_args
          in
          let ids = args_names @ pf_ids_of_hyps g in
          (* and fresh names for res H and the principle (cf bug bug #1174) *)
          let res, hres, graph_principle_id =
            match generate_fresh_id (Id.of_string "z") ids 3 with
            | [res; hres; graph_principle_id] -> (res, hres, graph_principle_id)
            | _ -> assert false
          in
          let ids = res :: hres :: graph_principle_id :: ids in
          (* we also compute fresh names for each hyptohesis of each branch
             of the principle *)
          let branches = List.rev princ_infos.branches in
          let intro_pats =
            List.map
              (fun decl ->
                List.map
                  (fun id -> id)
                  (generate_fresh_id (Id.of_string "y") ids
                     (Termops.nb_prod (Proofview.Goal.sigma g)
                        (RelDecl.get_type decl))))
              branches
          in
          (* We will need to change the function by its body
             using [f_equation] if it is recursive (that is the graph is infinite
             or unfold if the graph is finite
          *)
          let rewrite_tac j ids : unit Proofview.tactic =
            let graph_def = graphs.(j) in
            let infos =
              match
                find_Function_infos
                  (fst (destConst (Proofview.Goal.sigma g) funcs.(j)))
              with
              | None -> CErrors.user_err Pp.(str "No graph found")
              | Some infos -> infos
            in
            if
              infos.is_general
              || Rtree.is_infinite Declareops.eq_recarg
                   graph_def.Declarations.mind_recargs
            then
              let eq_lemma =
                try Option.get infos.equation_lemma
                with Option.IsNone ->
                  CErrors.anomaly (Pp.str "Cannot find equation lemma.")
              in
              tclTHENLIST
                [ tclMAP Simple.intro ids
                ; Equality.rewriteLR (mkConst eq_lemma)
                ; (* Don't forget to $\zeta$ normlize the term since the principles
                     have been $\zeta$-normalized *)
                  reduce
                    (Genredexpr.Cbv
                       {Redops.all_flags with Genredexpr.rDelta = false})
                    Locusops.onConcl
                ; generalize (List.map mkVar ids)
                ; thin ids ]
            else
              unfold_in_concl
                [ ( Locus.AllOccurrences
                  , Tacred.EvalConstRef
                      (fst (destConst (Proofview.Goal.sigma g) f)) ) ]
          in
          (* The proof of each branche itself *)
          let ind_number = ref 0 in
          let min_constr_number = ref 0 in
          let prove_branch i this_branche_ids =
            (* we fist compute the inductive corresponding to the branch *)
            let this_ind_number =
              let constructor_num = i - !min_constr_number in
              let length =
                Array.length graphs.(!ind_number).Declarations.mind_consnames
              in
              if constructor_num <= length then !ind_number
              else begin
                incr ind_number;
                min_constr_number := !min_constr_number + length;
                !ind_number
              end
            in
            tclTHENLIST
              [ (* we expand the definition of the function *)
                observe_tac "rewrite_tac"
                  (rewrite_tac this_ind_number this_branche_ids)
              ; (* introduce hypothesis with some rewrite *)
                observe_tac "intros_with_rewrite (all)" (intros_with_rewrite ())
              ; (* The proof is (almost) complete *)
                observe_tac "reflexivity" (reflexivity_with_destruct_cases ())
              ]
          in
          let params_names = fst (List.chop princ_infos.nparams args_names) in
          let open EConstr in
          let params = List.map mkVar params_names in
          tclTHENLIST
            [ tclMAP Simple.intro (args_names @ [res; hres])
            ; observe_tac "h_generalize"
                (generalize
                   [ mkApp
                       ( applist (graph_principle, params)
                       , Array.map (fun c -> applist (c, params)) lemmas ) ])
            ; Simple.intro graph_principle_id
            ; observe_tac ""
                (tclTHENS
                   (observe_tac "elim"
                      (elim false None
                         (mkVar hres, Tactypes.NoBindings)
                         (Some (mkVar graph_principle_id, Tactypes.NoBindings))))
                   (List.map_i
                      (fun i pat ->
                        observe_tac "prove_branch" (prove_branch i pat))
                      1 intro_pats)) ]))

exception No_graph_found

let get_funs_constant mp =
  let open Constr in
  let exception Not_Rec in
  let get_funs_constant const e : (Names.Constant.t * int) array =
    match Constr.kind (Term.strip_lam e) with
    | Fix (_, (na, _, _)) ->
      Array.mapi
        (fun i na ->
          match na.Context.binder_name with
          | Name id ->
            let const = Constant.make2 mp (Label.of_id id) in
            (const, i)
          | Anonymous -> CErrors.anomaly (Pp.str "Anonymous fix."))
        na
    | _ -> [|(const, 0)|]
  in
  function
  | const ->
    let find_constant_body const =
      match Global.body_of_constant Library.indirect_accessor const with
      | Some (body, _, _) ->
        let body =
          Tacred.cbv_norm_flags
            (CClosure.RedFlags.mkflags [CClosure.RedFlags.fZETA])
            (Global.env ())
            (Evd.from_env (Global.env ()))
            (EConstr.of_constr body)
        in
        let body = EConstr.Unsafe.to_constr body in
        body
      | None ->
        CErrors.user_err Pp.(str "Cannot define a principle over an axiom ")
    in
    let f = find_constant_body const in
    let l_const = get_funs_constant const f in
    (*
       We need to check that all the functions found are in the same block
       to prevent Reset strange thing
    *)
    let l_bodies =
      List.map find_constant_body (Array.to_list (Array.map fst l_const))
    in
    let l_params, _l_fixes =
      List.split (List.map Term.decompose_lam l_bodies)
    in
    (* all the parameters must be equal*)
    let _check_params =
      let first_params = List.hd l_params in
      List.iter
        (fun params ->
          if
            not
              (List.equal
                 (fun (n1, c1) (n2, c2) ->
                   Context.eq_annot Name.equal n1 n2 && Constr.equal c1 c2)
                 first_params params)
          then CErrors.user_err Pp.(str "Not a mutal recursive block"))
        l_params
    in
    (* The bodies has to be very similar *)
    let _check_bodies =
      try
        let extract_info is_first body =
          match Constr.kind body with
          | Fix ((idxs, _), (na, ta, ca)) -> (idxs, na, ta, ca)
          | _ ->
            if is_first && Int.equal (List.length l_bodies) 1 then raise Not_Rec
            else CErrors.user_err Pp.(str "Not a mutal recursive block")
        in
        let first_infos = extract_info true (List.hd l_bodies) in
        let check body =
          (* Hope this is correct *)
          let eq_infos (ia1, na1, ta1, ca1) (ia2, na2, ta2, ca2) =
            Array.equal Int.equal ia1 ia2
            && Array.equal (Context.eq_annot Name.equal) na1 na2
            && Array.equal Constr.equal ta1 ta2
            && Array.equal Constr.equal ca1 ca2
          in
          if not (eq_infos first_infos (extract_info false body)) then
            CErrors.user_err Pp.(str "Not a mutal recursive block")
        in
        List.iter check l_bodies
      with Not_Rec -> ()
    in
    l_const

let make_scheme evd (fas : (Constr.pconstant * Sorts.family) list) : _ list =
  let exception Found_type of int in
  let env = Global.env () in
  let funs = List.map fst fas in
  let first_fun = List.hd funs in
  let funs_mp = KerName.modpath (Constant.canonical (fst first_fun)) in
  let first_fun_kn =
    match find_Function_infos (fst first_fun) with
    | None -> raise No_graph_found
    | Some finfos -> fst finfos.graph_ind
  in
  let this_block_funs_indexes = get_funs_constant funs_mp (fst first_fun) in
  let this_block_funs =
    Array.map (fun (c, _) -> (c, snd first_fun)) this_block_funs_indexes
  in
  let prop_sort = Sorts.InProp in
  let funs_indexes =
    let this_block_funs_indexes = Array.to_list this_block_funs_indexes in
    let eq c1 c2 = Environ.QConstant.equal env c1 c2 in
    List.map
      (function cst -> List.assoc_f eq (fst cst) this_block_funs_indexes)
      funs
  in
  let ind_list =
    List.map
      (fun idx ->
        let ind = (first_fun_kn, idx) in
        ((ind, snd first_fun), true, prop_sort))
      funs_indexes
  in
  let sigma, schemes = Indrec.build_mutual_induction_scheme env !evd ind_list in
  let _ = evd := sigma in
  let l_schemes =
    List.map
      ( EConstr.of_constr
      %> Retyping.get_type_of env sigma
      %> EConstr.Unsafe.to_constr )
      schemes
  in
  let i = ref (-1) in
  let sorts =
    List.rev_map
      (fun (_, x) ->
        let sigma, fs = Evd.fresh_sort_in_family !evd x in
        evd := sigma;
        fs)
      fas
  in
  (* We create the first principle by tactic *)
  let first_type, other_princ_types =
    match l_schemes with
    | s :: l_schemes -> (s, l_schemes)
    | _ -> CErrors.anomaly (Pp.str "")
  in
  let opaque =
    let finfos =
      match find_Function_infos (fst first_fun) with
      | None -> raise Not_found
      | Some finfos -> finfos
    in
    match finfos.equation_lemma with
    | None -> Vernacexpr.Transparent (* non recursive definition *)
    | Some equation ->
      if Declareops.is_opaque (Global.lookup_constant equation) then
        Vernacexpr.Opaque
      else Vernacexpr.Transparent
  in
  let body, typ, univs, _hook, sigma0 =
    try
      build_functional_principle (Global.env ()) !evd first_type (Array.of_list sorts)
        this_block_funs 0
        (Functional_principles_proofs.prove_princ_for_struct evd false 0
           (Array.of_list (List.map fst funs)))
        (fun _ _ -> ())
    with e when CErrors.noncritical e -> raise (Defining_principle e)
  in
  evd := sigma0;
  incr i;
  (* The others are just deduced *)
  if List.is_empty other_princ_types then [(body, typ, univs, opaque)]
  else
    let other_fun_princ_types =
      let funs = Array.map Constr.mkConstU this_block_funs in
      let sorts = Array.of_list sorts in
      List.map
        (Functional_principles_types.compute_new_princ_type_from_rel (Global.env ()) funs sorts)
        other_princ_types
    in
    let first_princ_body = body in
    let ctxt, fix = Term.decompose_lam_assum first_princ_body in
    (* the principle has for forall ...., fix .*)
    let (idxs, _), ((_, ta, _) as decl) = Constr.destFix fix in
    let other_result =
      List.map (* we can now compute the other principles *)
        (fun scheme_type ->
          incr i;
          observe (Printer.pr_lconstr_env env sigma scheme_type);
          let type_concl = Term.strip_prod_assum scheme_type in
          let applied_f =
            List.hd (List.rev (snd (Constr.decompose_app type_concl)))
          in
          let f = fst (Constr.decompose_app applied_f) in
          try
            (* we search the number of the function in the fix block (name of the function) *)
            Array.iteri
              (fun j t ->
                let t = Term.strip_prod_assum t in
                let applied_g =
                  List.hd (List.rev (snd (Constr.decompose_app t)))
                in
                let g = fst (Constr.decompose_app applied_g) in
                if Constr.equal f g then raise (Found_type j);
                observe
                  Pp.(
                    Printer.pr_lconstr_env env sigma f
                    ++ str " <> "
                    ++ Printer.pr_lconstr_env env sigma g))
              ta;
            (* If we reach this point, the two principle are not mutually recursive
               We fall back to the previous method
            *)
            let body, typ, univs, _hook, sigma0 =
              build_functional_principle (Global.env ()) !evd
                (List.nth other_princ_types (!i - 1))
                (Array.of_list sorts) this_block_funs !i
                (Functional_principles_proofs.prove_princ_for_struct evd false
                   !i
                   (Array.of_list (List.map fst funs)))
                (fun _ _ -> ())
            in
            evd := sigma0;
            (body, typ, univs, opaque)
          with Found_type i ->
            let princ_body =
              Termops.it_mkLambda_or_LetIn (Constr.mkFix ((idxs, i), decl)) ctxt
            in
            (princ_body, Some scheme_type, univs, opaque))
        other_fun_princ_types
    in
    (body, typ, univs, opaque) :: other_result

(* [derive_correctness funs graphs] create correctness and completeness
   lemmas for each function in [funs] w.r.t. [graphs]
*)

let derive_correctness (funs : Constr.pconstant list) (graphs : inductive list)
    =
  let open EConstr in
  assert (funs <> []);
  assert (graphs <> []);
  let funs = Array.of_list funs and graphs = Array.of_list graphs in
  let map (c, u) = mkConstU (c, EInstance.make u) in
  let funs_constr = Array.map map funs in
  (* XXX STATE Why do we need this... why is the toplevel protection not enough *)
  funind_purify
    (fun () ->
      let env = Global.env () in
      let evd = ref (Evd.from_env env) in
      let graphs_constr = Array.map mkInd graphs in
      let lemmas_types_infos =
        Util.Array.map2_i
          (fun i f_constr graph ->
            let type_of_lemma_ctxt, type_of_lemma_concl, graph =
              generate_type evd false f_constr graph
            in
            let type_info = (type_of_lemma_ctxt, type_of_lemma_concl) in
            graphs_constr.(i) <- graph;
            let type_of_lemma =
              EConstr.it_mkProd_or_LetIn type_of_lemma_concl type_of_lemma_ctxt
            in
            let sigma, _ = Typing.type_of (Global.env ()) !evd type_of_lemma in
            evd := sigma;
            let type_of_lemma =
              Reductionops.nf_zeta (Global.env ()) !evd type_of_lemma
            in
            observe
              Pp.(
                str "type_of_lemma := "
                ++ Printer.pr_leconstr_env (Global.env ()) !evd type_of_lemma);
            (type_of_lemma, type_info))
          funs_constr graphs_constr
      in
      let schemes =
        (* The functional induction schemes are computed and not saved if there is more that one function
           if the block contains only one function we can safely reuse [f_rect]
        *)
        try
          if not (Int.equal (Array.length funs_constr) 1) then raise Not_found;
          [|find_induction_principle evd funs_constr.(0)|]
        with Not_found ->
          Array.of_list
            (List.map
               (fun (body, typ, _opaque, _univs) ->
                 (EConstr.of_constr body, EConstr.of_constr (Option.get typ)))
               (make_scheme evd
                  (Array.map_to_list (fun const -> (const, Sorts.InType)) funs)))
      in
      let proving_tac =
        prove_fun_correct !evd graphs_constr schemes lemmas_types_infos
      in
      Array.iteri
        (fun i f_as_constant ->
          let f_id = Label.to_id (Constant.label (fst f_as_constant)) in
          (*i The next call to mk_correct_id is valid since we are constructing the lemma
              Ensures by: obvious
            i*)
          let lem_id = mk_correct_id f_id in
          let typ, _ = lemmas_types_infos.(i) in
          let info = Declare.Info.make () in
          let cinfo = Declare.CInfo.make ~name:lem_id ~typ () in
          let lemma = Declare.Proof.start ~cinfo ~info !evd in
          let lemma = fst @@ Declare.Proof.by (proving_tac i) lemma in
          let (_ : _ list) =
            Declare.Proof.save_regular ~proof:lemma
              ~opaque:Vernacexpr.Transparent ~idopt:None
          in
          let finfo =
            match find_Function_infos (fst f_as_constant) with
            | None -> raise Not_found
            | Some finfo -> finfo
          in
          (* let lem_cst = fst (destConst (Constrintern.global_reference lem_id)) in *)
          let _, lem_cst_constr =
            Evd.fresh_global (Global.env ()) !evd
              (Option.get (Constrintern.locate_reference (Libnames.qualid_of_ident lem_id)))
          in
          let lem_cst, _ = EConstr.destConst !evd lem_cst_constr in
          update_Function {finfo with correctness_lemma = Some lem_cst})
        funs;
      let lemmas_types_infos =
        Util.Array.map2_i
          (fun i f_constr graph ->
            let type_of_lemma_ctxt, type_of_lemma_concl, graph =
              generate_type evd true f_constr graph
            in
            let type_info = (type_of_lemma_ctxt, type_of_lemma_concl) in
            graphs_constr.(i) <- graph;
            let type_of_lemma =
              EConstr.it_mkProd_or_LetIn type_of_lemma_concl type_of_lemma_ctxt
            in
            let type_of_lemma = Reductionops.nf_zeta env !evd type_of_lemma in
            observe
              Pp.(
                str "type_of_lemma := "
                ++ Printer.pr_leconstr_env env !evd type_of_lemma);
            (type_of_lemma, type_info))
          funs_constr graphs_constr
      in
      let ((kn, _) as graph_ind), u = destInd !evd graphs_constr.(0) in
      let mib, _mip = Global.lookup_inductive graph_ind in
      let sigma, scheme =
        Indrec.build_mutual_induction_scheme (Global.env ()) !evd
          (Array.to_list
             (Array.mapi
                (fun i _ ->
                  (((kn, i), EInstance.kind !evd u), true, Sorts.InType))
                mib.Declarations.mind_packets))
      in
      let schemes = Array.of_list scheme in
      let proving_tac =
        prove_fun_complete funs_constr mib.Declarations.mind_packets schemes
          lemmas_types_infos
      in
      Array.iteri
        (fun i f_as_constant ->
          let f_id = Label.to_id (Constant.label (fst f_as_constant)) in
          (*i The next call to mk_complete_id is valid since we are constructing the lemma
              Ensures by: obvious
            i*)
          let lem_id = mk_complete_id f_id in
          let info = Declare.Info.make () in
          let cinfo =
            Declare.CInfo.make ~name:lem_id ~typ:(fst lemmas_types_infos.(i)) ()
          in
          let lemma = Declare.Proof.start ~cinfo sigma ~info in
          let lemma =
            fst
              (Declare.Proof.by
                 (observe_tac
                    ("prove completeness (" ^ Id.to_string f_id ^ ")")
                    (proving_tac i))
                 lemma)
          in
          let (_ : _ list) =
            Declare.Proof.save_regular ~proof:lemma
              ~opaque:Vernacexpr.Transparent ~idopt:None
          in
          let finfo =
            match find_Function_infos (fst f_as_constant) with
            | None -> raise Not_found
            | Some finfo -> finfo
          in
          let _, lem_cst_constr =
            Evd.fresh_global (Global.env ()) !evd
              (Option.get (Constrintern.locate_reference (Libnames.qualid_of_ident lem_id)))
          in
          let lem_cst, _ = destConst !evd lem_cst_constr in
          update_Function {finfo with completeness_lemma = Some lem_cst})
        funs)
    ()

let warn_funind_cannot_build_inversion =
  CWarnings.create ~name:"funind-cannot-build-inversion" ~category:"funind"
    Pp.(
      fun e' ->
        strbrk "Cannot build inversion information"
        ++ if do_observe () then fnl () ++ CErrors.print e' else mt ())

let derive_inversion fix_names =
  try
    let evd' = Evd.from_env (Global.env ()) in
    (* we first transform the fix_names identifier into their corresponding constant *)
    let evd', fix_names_as_constant =
      List.fold_right
        (fun id (evd, l) ->
          let evd, c =
            Evd.fresh_global (Global.env ()) evd
              (Option.get (Constrintern.locate_reference (Libnames.qualid_of_ident id)))
          in
          let cst, u = EConstr.destConst evd c in
          (evd, (cst, EConstr.EInstance.kind evd u) :: l))
        fix_names (evd', [])
    in
    (*
       Then we check that the graphs have been defined
       If one of the graphs haven't been defined
       we do nothing
    *)
    List.iter
      (fun c -> ignore (find_Function_infos (fst c)))
      fix_names_as_constant;
    try
      let _evd', lind =
        List.fold_right
          (fun id (evd, l) ->
            let evd, id =
              Evd.fresh_global (Global.env ()) evd
                (Option.get (Constrintern.locate_reference
                   (Libnames.qualid_of_ident (mk_rel_id id))))
            in
            (evd, fst (EConstr.destInd evd id) :: l))
          fix_names (evd', [])
      in
      derive_correctness fix_names_as_constant lind
    with e when CErrors.noncritical e -> warn_funind_cannot_build_inversion e
  with e when CErrors.noncritical e -> warn_funind_cannot_build_inversion e

let register_wf interactive_proof ?(is_mes = false) fname rec_impls wf_rel_expr
    wf_arg using_lemmas args ret_type body pre_hook =
  let type_of_f = Constrexpr_ops.mkCProdN args ret_type in
  let rec_arg_num =
    let names =
      List.map
        CAst.(with_val (fun x -> x))
        (Constrexpr_ops.names_of_local_assums args)
    in
    List.index Name.equal (Name wf_arg) names
  in
  let unbounded_eq =
    let f_app_args =
      CAst.make
      @@ Constrexpr.CAppExpl
           ( (Libnames.qualid_of_ident fname, None)
           , List.map
               (function
                 | {CAst.v = Anonymous} -> assert false
                 | {CAst.v = Name e} -> Constrexpr_ops.mkIdentC e)
               (Constrexpr_ops.names_of_local_assums args) )
    in
    CAst.make
    @@ Constrexpr.CApp
         ( Constrexpr_ops.mkRefC (Libnames.qualid_of_string "Logic.eq")
         , [(f_app_args, None); (body, None)] )
  in
  let eq = Constrexpr_ops.mkCProdN args unbounded_eq in
  let hook ((f_ref, _) as fconst) tcc_lemma_ref (functional_ref, _) (eq_ref, _)
      rec_arg_num rec_arg_type _nb_args relation =
    try
      pre_hook [fconst]
        (generate_correction_proof_wf f_ref tcc_lemma_ref is_mes functional_ref
           eq_ref rec_arg_num rec_arg_type relation);
      derive_inversion [fname]
    with e when CErrors.noncritical e -> (* No proof done *)
                                         ()
  in
  Recdef.recursive_definition ~interactive_proof ~is_mes fname rec_impls
    type_of_f wf_rel_expr rec_arg_num eq hook using_lemmas

let register_mes interactive_proof fname rec_impls wf_mes_expr wf_rel_expr_opt
    wf_arg using_lemmas args ret_type body =
  let wf_arg_type, wf_arg =
    match wf_arg with
    | None -> (
      match args with
      | [Constrexpr.CLocalAssum ([{CAst.v = Name x}], _k, t)] -> (t, x)
      | _ -> CErrors.user_err (Pp.str "Recursive argument must be specified") )
    | Some wf_args -> (
      try
        match
          List.find
            (function
              | Constrexpr.CLocalAssum (l, _k, t) ->
                List.exists
                  (function
                    | {CAst.v = Name id} -> Id.equal id wf_args | _ -> false)
                  l
              | _ -> false)
            args
        with
        | Constrexpr.CLocalAssum (_, _k, t) -> (t, wf_args)
        | _ -> assert false
      with Not_found -> assert false )
  in
  let wf_rel_from_mes, is_mes =
    match wf_rel_expr_opt with
    | None ->
      let ltof =
        let make_dir l = DirPath.make (List.rev_map Id.of_string l) in
        Libnames.qualid_of_path
          (Libnames.make_path
             (make_dir ["Arith"; "Wf_nat"])
             (Id.of_string "ltof"))
      in
      let fun_from_mes =
        let applied_mes =
          Constrexpr_ops.mkAppC (wf_mes_expr, [Constrexpr_ops.mkIdentC wf_arg])
        in
        Constrexpr_ops.mkLambdaC
          ( [CAst.make @@ Name wf_arg]
          , Constrexpr_ops.default_binder_kind
          , wf_arg_type
          , applied_mes )
      in
      let wf_rel_from_mes =
        Constrexpr_ops.mkAppC
          (Constrexpr_ops.mkRefC ltof, [wf_arg_type; fun_from_mes])
      in
      (wf_rel_from_mes, true)
    | Some wf_rel_expr ->
      let wf_rel_with_mes =
        let a = Names.Id.of_string "___a" in
        let b = Names.Id.of_string "___b" in
        Constrexpr_ops.mkLambdaC
          ( [CAst.make @@ Name a; CAst.make @@ Name b]
          , Constrexpr.Default Glob_term.Explicit
          , wf_arg_type
          , Constrexpr_ops.mkAppC
              ( wf_rel_expr
              , [ Constrexpr_ops.mkAppC
                    (wf_mes_expr, [Constrexpr_ops.mkIdentC a])
                ; Constrexpr_ops.mkAppC
                    (wf_mes_expr, [Constrexpr_ops.mkIdentC b]) ] ) )
      in
      (wf_rel_with_mes, false)
  in
  register_wf interactive_proof ~is_mes fname rec_impls wf_rel_from_mes wf_arg
    using_lemmas args ret_type body

let do_generate_principle_aux pconstants on_error register_built
    interactive_proof fixpoint_exprl : Declare.Proof.t option =
  List.iter
    (fun {Vernacexpr.notations} ->
      if not (List.is_empty notations) then
        CErrors.user_err (Pp.str "Function does not support notations for now"))
    fixpoint_exprl;
  let lemma, _is_struct =
    match fixpoint_exprl with
    | [ ( { Vernacexpr.rec_order =
              Some {CAst.v = Constrexpr.CWfRec (wf_x, wf_rel)} } as
        fixpoint_expr ) ] ->
      let ( {Vernacexpr.fname; univs = _; binders; rtype; body_def} as
          fixpoint_expr ) =
        match recompute_binder_list [fixpoint_expr] with
        | [e] -> e
        | _ -> assert false
      in
      let fixpoint_exprl = [fixpoint_expr] in
      let body =
        match body_def with
        | Some body -> body
        | None ->
          CErrors.user_err
            (Pp.str "Body of Function must be given.")
      in
      let recdefs, rec_impls = build_newrecursive fixpoint_exprl in
      let using_lemmas = [] in
      let pre_hook pconstants =
        generate_principle
          (ref (Evd.from_env (Global.env ())))
          pconstants on_error true register_built fixpoint_exprl recdefs
      in
      if register_built then
        ( register_wf interactive_proof fname.CAst.v rec_impls wf_rel
            wf_x.CAst.v using_lemmas binders rtype body pre_hook
        , false )
      else (None, false)
    | [ ( { Vernacexpr.rec_order =
              Some {CAst.v = Constrexpr.CMeasureRec (wf_x, wf_mes, wf_rel_opt)}
          } as fixpoint_expr ) ] ->
      let ( {Vernacexpr.fname; univs = _; binders; rtype; body_def} as
          fixpoint_expr ) =
        match recompute_binder_list [fixpoint_expr] with
        | [e] -> e
        | _ -> assert false
      in
      let fixpoint_exprl = [fixpoint_expr] in
      let recdefs, rec_impls = build_newrecursive fixpoint_exprl in
      let using_lemmas = [] in
      let body =
        match body_def with
        | Some body -> body
        | None ->
          CErrors.user_err
            Pp.(str "Body of Function must be given.")
      in
      let pre_hook pconstants =
        generate_principle
          (ref (Evd.from_env (Global.env ())))
          pconstants on_error true register_built fixpoint_exprl recdefs
      in
      if register_built then
        ( register_mes interactive_proof fname.CAst.v rec_impls wf_mes wf_rel_opt
            (Option.map (fun x -> x.CAst.v) wf_x)
            using_lemmas binders rtype body pre_hook
        , true )
      else (None, true)
    | _ ->
      List.iter
        (function
          | {Vernacexpr.rec_order} -> (
            match rec_order with
            | Some {CAst.v = Constrexpr.CMeasureRec _ | Constrexpr.CWfRec _} ->
              CErrors.user_err
                (Pp.str
                   "Cannot use mutual definition with well-founded recursion \
                    or measure")
            | _ -> () ))
        fixpoint_exprl;
      let fixpoint_exprl = recompute_binder_list fixpoint_exprl in
      let fix_names =
        List.map (function {Vernacexpr.fname} -> fname.CAst.v) fixpoint_exprl
      in
      (* ok all the expressions are structural *)
      let recdefs, _rec_impls = build_newrecursive fixpoint_exprl in
      let is_rec = List.exists (is_rec fix_names) recdefs in
      let lemma, evd, pconstants =
        if register_built then register_struct is_rec fixpoint_exprl
        else (None, Evd.from_env (Global.env ()), pconstants)
      in
      let evd = ref evd in
      generate_principle (ref !evd) pconstants on_error false register_built
        fixpoint_exprl recdefs
        (Functional_principles_proofs.prove_princ_for_struct evd
           interactive_proof);
      if register_built then derive_inversion fix_names;
      (lemma, true)
  in
  lemma

let warn_cannot_define_graph =
  CWarnings.create ~name:"funind-cannot-define-graph" ~category:"funind"
    (fun (names, error) ->
      Pp.(strbrk "Cannot define graph(s) for " ++ hv 1 names ++ error))

let warn_cannot_define_principle =
  CWarnings.create ~name:"funind-cannot-define-principle" ~category:"funind"
    (fun (names, error) ->
      Pp.(
        strbrk "Cannot define induction principle(s) for " ++ hv 1 names ++ error))

let warning_error names e =
  let e_explain e =
    match e with
    | ToShow e -> Pp.(spc () ++ CErrors.print e)
    | _ -> if do_observe () then Pp.(spc () ++ CErrors.print e) else Pp.mt ()
  in
  match e with
  | Building_graph e ->
    let names =
      Pp.(prlist_with_sep (fun _ -> str "," ++ spc ()) Ppconstr.pr_id names)
    in
    warn_cannot_define_graph (names, e_explain e)
  | Defining_principle e ->
    let names =
      Pp.(prlist_with_sep (fun _ -> str "," ++ spc ()) Ppconstr.pr_id names)
    in
    warn_cannot_define_principle (names, e_explain e)
  | _ -> raise e

let error_error names e =
  let e_explain e =
    match e with
    | ToShow e -> Pp.(spc () ++ CErrors.print e)
    | _ -> if do_observe () then Pp.(spc () ++ CErrors.print e) else Pp.mt ()
  in
  match e with
  | Building_graph e ->
    CErrors.user_err
      Pp.(
        str "Cannot define graph(s) for "
        ++ hv 1
             (prlist_with_sep (fun _ -> str "," ++ spc ()) Ppconstr.pr_id names)
        ++ e_explain e)
  | _ -> raise e

(* [chop_n_arrow n t] chops the [n] first arrows in [t]
   Acts on Constrexpr.constr_expr
*)
let rec chop_n_arrow n t =
  let exception Stop of Constrexpr.constr_expr in
  let open Constrexpr in
  if n <= 0 then t
    (* If we have already removed all the arrows then return the type *)
  else
    (* If not we check the form of [t] *)
    match t.CAst.v with
    | Constrexpr.CProdN (nal_ta', t') -> (
      try
        (* If we have a forall, two results are possible :
            either we need to discard more than the number of arrows contained
            in this product declaration then we just recall [chop_n_arrow] on
            the remaining number of arrow to chop and [t'] we discard it and
            recall [chop_n_arrow], either this product contains more arrows
            than the number we need to chop and then we return the new type
        *)
        let new_n =
          let rec aux (n : int) = function
            | [] -> n
            | CLocalAssum (nal, k, t'') :: nal_ta' ->
              let nal_l = List.length nal in
              if n >= nal_l then aux (n - nal_l) nal_ta'
              else
                let new_t' =
                  CAst.make
                  @@ Constrexpr.CProdN
                       ( CLocalAssum (snd (List.chop n nal), k, t'') :: nal_ta'
                       , t' )
                in
                raise (Stop new_t')
            | _ -> CErrors.anomaly (Pp.str "Not enough products.")
          in
          aux n nal_ta'
        in
        chop_n_arrow new_n t'
      with Stop t -> t )
    | _ -> CErrors.anomaly (Pp.str "Not enough products.")

let rec add_args id new_args =
  let open Libnames in
  let open Constrexpr in
  CAst.map (function
    | CRef (qid, _) as b ->
      if qualid_is_ident qid && Id.equal (qualid_basename qid) id then
        CAppExpl ((qid, None), new_args)
      else b
    | CFix _ | CCoFix _ -> CErrors.anomaly ~label:"add_args " (Pp.str "todo.")
    | CProdN (nal, b1) ->
      CProdN
        ( List.map
            (function
              | CLocalAssum (nal, k, b2) ->
                CLocalAssum (nal, k, add_args id new_args b2)
              | CLocalDef (na, b1, t) ->
                CLocalDef
                  ( na
                  , add_args id new_args b1
                  , Option.map (add_args id new_args) t )
              | CLocalPattern _ ->
                CErrors.user_err (Pp.str "pattern with quote not allowed here."))
            nal
        , add_args id new_args b1 )
    | CLambdaN (nal, b1) ->
      CLambdaN
        ( List.map
            (function
              | CLocalAssum (nal, k, b2) ->
                CLocalAssum (nal, k, add_args id new_args b2)
              | CLocalDef (na, b1, t) ->
                CLocalDef
                  ( na
                  , add_args id new_args b1
                  , Option.map (add_args id new_args) t )
              | CLocalPattern _ ->
                CErrors.user_err (Pp.str "pattern with quote not allowed here."))
            nal
        , add_args id new_args b1 )
    | CLetIn (na, b1, t, b2) ->
      CLetIn
        ( na
        , add_args id new_args b1
        , Option.map (add_args id new_args) t
        , add_args id new_args b2 )
    | CAppExpl ((qid, us), exprl) ->
      if qualid_is_ident qid && Id.equal (qualid_basename qid) id then
        CAppExpl
          ((qid, us), new_args @ List.map (add_args id new_args) exprl)
      else CAppExpl ((qid, us), List.map (add_args id new_args) exprl)
    | CApp (b, bl) ->
      CApp
        ( add_args id new_args b
        , List.map (fun (e, o) -> (add_args id new_args e, o)) bl )
    | CProj (expl, f, bl, b) ->
      CProj
        (expl, f
        , List.map (fun (e, o) -> (add_args id new_args e, o)) bl
        , add_args id new_args b)
    | CCases (sty, b_option, cel, cal) ->
      CCases
        ( sty
        , Option.map (add_args id new_args) b_option
        , List.map
            (fun (b, na, b_option) -> (add_args id new_args b, na, b_option))
            cel
        , List.map
            CAst.(map (fun (cpl, e) -> (cpl, add_args id new_args e)))
            cal )
    | CLetTuple (nal, (na, b_option), b1, b2) ->
      CLetTuple
        ( nal
        , (na, Option.map (add_args id new_args) b_option)
        , add_args id new_args b1
        , add_args id new_args b2 )
    | CIf (b1, (na, b_option), b2, b3) ->
      CIf
        ( add_args id new_args b1
        , (na, Option.map (add_args id new_args) b_option)
        , add_args id new_args b2
        , add_args id new_args b3 )
    | (CHole _ | CPatVar _ | CEvar _ | CPrim _ | CSort _) as b -> b
    | CCast (b1, k, b2) ->
      CCast (add_args id new_args b1, k, add_args id new_args b2)
    | CRecord pars ->
      CRecord (List.map (fun (e, o) -> (e, add_args id new_args o)) pars)
    | CNotation _ -> CErrors.anomaly ~label:"add_args " (Pp.str "CNotation.")
    | CGeneralization _ ->
      CErrors.anomaly ~label:"add_args " (Pp.str "CGeneralization.")
    | CDelimiters _ ->
      CErrors.anomaly ~label:"add_args " (Pp.str "CDelimiters.")
    | CArray _ -> CErrors.anomaly ~label:"add_args " (Pp.str "CArray."))

let rec get_args b t :
    Constrexpr.local_binder_expr list
    * Constrexpr.constr_expr
    * Constrexpr.constr_expr =
  let open Constrexpr in
  match b.CAst.v with
  | Constrexpr.CLambdaN ((CLocalAssum (nal, k, ta) as d) :: rest, b') ->
    let n = List.length nal in
    let nal_tas, b'', t'' =
      get_args
        (CAst.make ?loc:b.CAst.loc @@ Constrexpr.CLambdaN (rest, b'))
        (chop_n_arrow n t)
    in
    (d :: nal_tas, b'', t'')
  | Constrexpr.CLambdaN ([], b) -> ([], b, t)
  | _ -> ([], b, t)

let make_graph (f_ref : GlobRef.t) =
  let open Constrexpr in
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let c, c_body =
    match f_ref with
    | GlobRef.ConstRef c ->
      if Environ.mem_constant c (Global.env ()) then (c, Global.lookup_constant c) else
        CErrors.user_err
          Pp.(
            str "Cannot find "
            ++ Printer.pr_leconstr_env env sigma (EConstr.mkConst c))
    | _ -> CErrors.user_err Pp.(str "Not a function reference")
  in
  match Global.body_of_constant_body Library.indirect_accessor c_body with
  | None -> CErrors.user_err (Pp.str "Cannot build a graph over an axiom!")
  | Some (body, _, _) ->
    let env = Global.env () in
    let extern_body, extern_type =
      with_full_print
        (fun () ->
          ( Constrextern.extern_constr env sigma (EConstr.of_constr body)
          , Constrextern.extern_type env sigma
              (EConstr.of_constr (*FIXME*) c_body.Declarations.const_type) ))
        ()
    in
    let nal_tas, b, t = get_args extern_body extern_type in
    let expr_list =
      match b.CAst.v with
      | Constrexpr.CFix (l_id, fixexprl) ->
        let l =
          List.map
            (fun (id, recexp, bl, t, b) ->
              let {CAst.loc; v = rec_id} =
                match Option.get recexp with
                | {CAst.v = CStructRec id} -> id
                | {CAst.v = CWfRec (id, _)} -> id
                | {CAst.v = CMeasureRec (oid, _, _)} -> Option.get oid
              in
              let new_args =
                List.flatten
                  (List.map
                     (function
                       | Constrexpr.CLocalDef (na, _, _) -> []
                       | Constrexpr.CLocalAssum (nal, _, _) ->
                         List.map
                           (fun {CAst.loc; v = n} ->
                             CAst.make ?loc
                             @@ CRef
                                  ( Libnames.qualid_of_ident ?loc
                                    @@ Nameops.Name.get_id n
                                  , None ))
                           nal
                       | Constrexpr.CLocalPattern _ -> assert false)
                     nal_tas)
              in
              let b' = add_args id.CAst.v new_args b in
              { Vernacexpr.fname = id
              ; univs = None
              ; rec_order = Some (CAst.make (CStructRec (CAst.make rec_id)))
              ; binders = nal_tas @ bl
              ; rtype = t
              ; body_def = Some b'
              ; notations = [] })
            fixexprl
        in
        l
      | _ ->
        let fname = CAst.make (Label.to_id (Constant.label c)) in
        [ { Vernacexpr.fname
          ; univs = None
          ; rec_order = None
          ; binders = nal_tas
          ; rtype = t
          ; body_def = Some b
          ; notations = [] } ]
    in
    let mp = Constant.modpath c in
    let pstate =
      do_generate_principle_aux [(c, Univ.Instance.empty)] error_error false
        false expr_list
    in
    assert (Option.is_empty pstate);
    (* We register the infos *)
    List.iter
      (fun {Vernacexpr.fname = {CAst.v = id}} ->
        add_Function false (Constant.make2 mp (Label.of_id id)))
      expr_list

(* *************** statically typed entrypoints ************************* *)

let do_generate_principle_interactive fixl : Declare.Proof.t =
  match do_generate_principle_aux [] warning_error true true fixl with
  | Some lemma -> lemma
  | None ->
    CErrors.anomaly (Pp.str "indfun: leaving no open proof in interactive mode")

let do_generate_principle fixl : unit =
  match do_generate_principle_aux [] warning_error true false fixl with
  | Some _lemma ->
    CErrors.anomaly
      (Pp.str "indfun: leaving a goal open in non-interactive mode")
  | None -> ()

let build_scheme fas =
  let evd = ref (Evd.from_env (Global.env ())) in
  let pconstants =
    List.map
      (fun (_, f, sort) ->
        let f_as_constant =
          try Smartlocate.global_with_alias f
          with Not_found ->
            CErrors.user_err
              Pp.(str "Cannot find " ++ Libnames.pr_qualid f ++ str ".")
        in
        let evd', f = Evd.fresh_global (Global.env ()) !evd f_as_constant in
        let _ = evd := evd' in
        let sigma, _ = Typing.type_of ~refresh:true (Global.env ()) !evd f in
        evd := sigma;
        let c, u =
          try EConstr.destConst !evd f
          with Constr.DestKO ->
            CErrors.user_err
              Pp.(
                Printer.pr_econstr_env (Global.env ()) !evd f
                ++ spc ()
                ++ str "should be the named of a globally defined function")
        in
        ((c, EConstr.EInstance.kind !evd u), sort))
      fas
  in
  let bodies_types = make_scheme evd pconstants in
  List.iter2
    (fun (princ_id, _, _) (body, types, univs, opaque) ->
      let (_ : Constant.t) =
        let opaque = if opaque = Vernacexpr.Opaque then true else false in
        let def_entry = Declare.definition_entry ~univs ~opaque ?types body in
        Declare.declare_constant ~name:princ_id
          ~kind:Decls.(IsProof Theorem)
          (Declare.DefinitionEntry def_entry)
      in
      Declare.definition_message princ_id)
    fas bodies_types

let build_case_scheme fa =
  let env = Global.env () and sigma = Evd.from_env (Global.env ()) in
  (*   let id_to_constr id =  *)
  (*     Constrintern.global_reference  id *)
  (*   in  *)
  let funs =
    let _, f, _ = fa in
    try
      let open GlobRef in
      match Smartlocate.global_with_alias f with
      | ConstRef c -> c
      | IndRef _ | ConstructRef _ | VarRef _ -> assert false
    with Not_found ->
      CErrors.user_err
        Pp.(str "Cannot find " ++ Libnames.pr_qualid f ++ str ".")
  in
  let sigma, (_, u) = Evd.fresh_constant_instance env sigma funs in
  let first_fun = funs in
  let funs_mp = Constant.modpath first_fun in
  let first_fun_kn =
    match find_Function_infos first_fun with
    | None -> raise No_graph_found
    | Some finfos -> fst finfos.graph_ind
  in
  let this_block_funs_indexes = get_funs_constant funs_mp first_fun in
  let this_block_funs =
    Array.map (fun (c, _) -> (c, u)) this_block_funs_indexes
  in
  let prop_sort = Sorts.InProp in
  let funs_indexes =
    let this_block_funs_indexes = Array.to_list this_block_funs_indexes in
    let eq c1 c2 = Environ.QConstant.equal env c1 c2 in
    List.assoc_f eq funs this_block_funs_indexes
  in
  let ind, sf =
    let ind = (first_fun_kn, funs_indexes) in
    ((ind, Univ.Instance.empty) (*FIXME*), prop_sort)
  in
  let sigma, scheme, scheme_type =
    Indrec.build_case_analysis_scheme_default env sigma ind sf
  in
  let sorts = (fun (_, _, x) -> fst @@ UnivGen.fresh_sort_in_family x) fa in
  let princ_name = (fun (x, _, _) -> x) fa in
  let (_ : unit) =
    (* Pp.msgnl (str "Generating " ++ Ppconstr.pr_id princ_name ++str " with " ++
                pr_lconstr scheme_type ++ str " and " ++ (fun a -> prlist_with_sep spc (fun c -> pr_lconstr (mkConst c)) (Array.to_list a)) this_block_funs
             );
    *)
    generate_functional_principle
      (ref (Evd.from_env (Global.env ())))
      scheme_type
      (Some [|sorts|])
      (Some princ_name) this_block_funs 0
      (Functional_principles_proofs.prove_princ_for_struct
         (ref (Evd.from_env (Global.env ())))
         false 0 [|funs|])
  in
  ()
