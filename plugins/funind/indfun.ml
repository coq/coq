open CErrors
open Sorts
open Util
open Names
open Constr
open EConstr
open Pp
open Indfun_common
open Libnames
open Globnames
open Glob_term
open Declarations
open Tactypes
open Decl_kinds

module RelDecl = Context.Rel.Declaration

let is_rec_info sigma scheme_info =
  let test_branche min acc decl =
    acc || (
      let new_branche =
	it_mkProd_or_LetIn mkProp (fst (decompose_prod_assum sigma (RelDecl.get_type decl))) in
      let free_rels_in_br = Termops.free_rels sigma new_branche in
      let max = min + scheme_info.Tactics.npredicates in
      Int.Set.exists (fun i -> i >= min && i< max) free_rels_in_br
    )
  in
  List.fold_left_i test_branche 1 false (List.rev scheme_info.Tactics.branches)

let choose_dest_or_ind scheme_info args =
  Proofview.tclBIND Proofview.tclEVARMAP (fun sigma ->
  Tactics.induction_destruct (is_rec_info sigma scheme_info) false args)

let functional_induction with_clean c princl pat =
  let res =
    fun g ->
    let sigma = Tacmach.project g in
    let f,args = decompose_app sigma c in
    let princ,bindings, princ_type,g' =
      match princl with
      | None -> (* No principle is given let's find the good one *)
	 begin
	   match EConstr.kind sigma f with
	   | Const (c',u) ->
	      let princ_option =
		let finfo = (* we first try to find out a graph on f *)
		  try find_Function_infos c'
		  with Not_found ->
		    user_err  (str "Cannot find induction information on "++
                                       Printer.pr_leconstr_env (Tacmach.pf_env g) sigma (mkConst c') )
		in
		match Tacticals.elimination_sort_of_goal g with
		| InProp -> finfo.prop_lemma
		| InSet -> finfo.rec_lemma
		| InType -> finfo.rect_lemma
	      in
	      let princ,g' =  (* then we get the principle *)
		try
		  let g',princ =
		    Tacmach.pf_eapply (Evd.fresh_global) g  (Globnames.ConstRef (Option.get princ_option )) in
		  princ,g'
		with Option.IsNone ->
		  (*i If there is not default lemma defined then,
			  we cross our finger and try to find a lemma named f_ind
			  (or f_rec, f_rect) i*)
		  let princ_name =
		    Indrec.make_elimination_ident
		      (Label.to_id (Constant.label c'))
		      (Tacticals.elimination_sort_of_goal g)
		  in
		  try
		    let princ_ref = const_of_id princ_name in
		    let (a,b) = Tacmach.pf_eapply (Evd.fresh_global) g princ_ref in
		    (b,a)
		    (* mkConst(const_of_id princ_name ),g (\* FIXME *\) *)
		  with Not_found -> (* This one is neither defined ! *)
		    user_err  (str "Cannot find induction principle for "
                                     ++ Printer.pr_leconstr_env (Tacmach.pf_env g) sigma (mkConst c') )
	      in
              (princ,NoBindings,Tacmach.pf_unsafe_type_of g' princ,g')
	   | _ -> raise (UserError(None,str "functional induction must be used with a function" ))
	 end
      | Some ((princ,binding)) ->
	 princ,binding,Tacmach.pf_unsafe_type_of g princ,g
    in
    let sigma = Tacmach.project g' in
    let princ_infos = Tactics.compute_elim_sig (Tacmach.project g') princ_type in
    let args_as_induction_constr =
      let c_list =
	if princ_infos.Tactics.farg_in_concl
	then [c] else []
      in
      if List.length args + List.length c_list = 0
      then user_err Pp.(str "Cannot recognize a valid functional scheme" );
      let encoded_pat_as_patlist =
        List.make (List.length args + List.length c_list - 1) None @ [pat]
      in
      List.map2
        (fun c pat ->
          ((None,
            Tactics.ElimOnConstr (fun env sigma -> (sigma,(c,NoBindings)))),
           (None,pat),
           None))
        (args@c_list)
        encoded_pat_as_patlist
    in
    let princ' = Some (princ,bindings) in
    let princ_vars =
      List.fold_right
	(fun a acc -> try Id.Set.add (destVar sigma a) acc with DestKO -> acc)
	args
	Id.Set.empty
    in
    let old_idl = List.fold_right Id.Set.add (Tacmach.pf_ids_of_hyps g) Id.Set.empty in
    let old_idl = Id.Set.diff old_idl princ_vars in
    let subst_and_reduce g =
      if with_clean
      then
	let idl =
	  List.filter (fun id -> not (Id.Set.mem id old_idl))
	    (Tacmach.pf_ids_of_hyps g)
	in
	let flag =
	  Genredexpr.Cbv
	    {Redops.all_flags
	     with Genredexpr.rDelta = false;
	    }
	in
	Tacticals.tclTHEN
	  (Tacticals.tclMAP (fun id -> Tacticals.tclTRY (Proofview.V82.of_tactic (Equality.subst_gen (do_rewrite_dependent ()) [id]))) idl )
	  (Proofview.V82.of_tactic (Tactics.reduce flag Locusops.allHypsAndConcl))
	  g
      else Tacticals.tclIDTAC g
    in
    Tacticals.tclTHEN
      (Proofview.V82.of_tactic (choose_dest_or_ind
	 princ_infos
	 (args_as_induction_constr,princ')))
      subst_and_reduce
      g'
  in res

let rec abstract_glob_constr c = function
  | [] -> c
  | Constrexpr.CLocalDef (x,b,t)::bl -> Constrexpr_ops.mkLetInC(x,b,t,abstract_glob_constr c bl)
  | Constrexpr.CLocalAssum (idl,k,t)::bl ->
      List.fold_right (fun x b -> Constrexpr_ops.mkLambdaC([x],k,t,b)) idl
        (abstract_glob_constr c bl)
  | Constrexpr.CLocalPattern _::bl -> assert false

let interp_casted_constr_with_implicits env sigma impls c  =
  Constrintern.intern_gen Pretyping.WithoutTypeConstraint env sigma ~impls c

(*
   Construct a fixpoint as a Glob_term
   and not as a constr
*)

let build_newrecursive
    lnameargsardef  =
  let env0 = Global.env() in
  let sigma = Evd.from_env env0 in
  let (rec_sign,rec_impls) =
    List.fold_left
      (fun (env,impls) (({CAst.v=recname},_),bl,arityc,_) ->
        let arityc = Constrexpr_ops.mkCProdN bl arityc in
        let arity,ctx = Constrintern.interp_type env0 sigma arityc in
        let evd = Evd.from_env env0 in
        let evd, (_, (_, impls')) = Constrintern.interp_context_evars env evd bl in
        let impl = Constrintern.compute_internalization_data env0 evd Constrintern.Recursive arity impls' in
        let open Context.Named.Declaration in
        (EConstr.push_named (LocalAssum (recname,arity)) env, Id.Map.add recname impl impls))
      (env0,Constrintern.empty_internalization_env) lnameargsardef in
  let recdef =
    (* Declare local notations *)
    let f (_,bl,_,def) =
      let def = abstract_glob_constr def bl in
      interp_casted_constr_with_implicits
        rec_sign sigma rec_impls def
    in
    States.with_state_protection (List.map f) lnameargsardef
  in
  recdef,rec_impls

let build_newrecursive l = 
  let l' = List.map 
    (fun ((fixna,_,bll,ar,body_opt),lnot) -> 
       match body_opt with 
	 | Some body -> 
	     (fixna,bll,ar,body)
	 | None -> user_err ~hdr:"Function" (str "Body of Function must be given")
    ) l
  in
  build_newrecursive l'

let error msg = user_err Pp.(str msg)

(* Checks whether or not the mutual bloc is recursive *)
let is_rec names =
  let names = List.fold_right Id.Set.add names Id.Set.empty in
  let check_id id names =  Id.Set.mem id names in
  let rec lookup names gt = match DAst.get gt with
    | GVar(id) -> check_id id names
    | GRef _ | GEvar _ | GPatVar _ | GSort _ |  GHole _ | GInt _ -> false
    | GCast(b,_) -> lookup names b
    | GRec _ -> error "GRec not handled"
    | GIf(b,_,lhs,rhs) ->
	(lookup names b) || (lookup names lhs) || (lookup names rhs)
    | GProd(na,_,t,b) | GLambda(na,_,t,b) ->
	lookup names t || lookup (Nameops.Name.fold_right Id.Set.remove na names) b
    | GLetIn(na,b,t,c) ->
	lookup names b || Option.cata (lookup names) true t || lookup (Nameops.Name.fold_right Id.Set.remove na names) c
    | GLetTuple(nal,_,t,b) -> lookup names t ||
	lookup
	  (List.fold_left
	     (fun acc na -> Nameops.Name.fold_right Id.Set.remove na acc)
	     names
	     nal
	  )
	  b
    | GApp(f,args) -> List.exists (lookup names) (f::args)
    | GCases(_,_,el,brl) ->
	List.exists (fun (e,_) -> lookup names e) el ||
	  List.exists (lookup_br names) brl
  and lookup_br names {CAst.v=(idl,_,rt)} =
    let new_names = List.fold_right Id.Set.remove idl names in
    lookup new_names rt
  in
  lookup names

let rec local_binders_length = function
  (* Assume that no `{ ... } contexts occur *)
  | [] -> 0
  | Constrexpr.CLocalDef _::bl -> 1 + local_binders_length bl
  | Constrexpr.CLocalAssum (idl,_,_)::bl -> List.length idl + local_binders_length bl
  | Constrexpr.CLocalPattern _::bl -> assert false

let prepare_body ((name,_,args,types,_),_) rt =
  let n = local_binders_length args in
(*   Pp.msgnl (str "nb lambda to chop : " ++ str (string_of_int n) ++ fnl () ++Printer.pr_glob_constr rt); *)
  let fun_args,rt' = chop_rlambda_n n rt in
  (fun_args,rt')

let process_vernac_interp_error e =
  fst (ExplainErr.process_vernac_interp_error (e, Exninfo.null))

let warn_funind_cannot_build_inversion =
  CWarnings.create ~name:"funind-cannot-build-inversion" ~category:"funind"
    (fun e' -> strbrk "Cannot build inversion information" ++
                 if do_observe () then (fnl() ++ CErrors.print e') else mt ())

let derive_inversion fix_names =
  try
    let evd' = Evd.from_env (Global.env ()) in 
    (* we first transform the fix_names identifier into their corresponding constant *)
    let evd',fix_names_as_constant =
      List.fold_right
	(fun id (evd,l) ->
	 let evd,c =
	   Evd.fresh_global
	     (Global.env ()) evd (Constrintern.locate_reference (Libnames.qualid_of_ident id)) in 
        let (cst, u) = destConst evd c in
	 evd, (cst, EInstance.kind evd u) :: l
	)
	fix_names
	(evd',[])
    in
    (*
       Then we check that the graphs have been defined
       If one of the graphs haven't been defined
       we do nothing
    *)
    List.iter (fun c -> ignore (find_Function_infos (fst c))) fix_names_as_constant ;
    try
      let evd', lind =
	List.fold_right
	  (fun id (evd,l) ->
	   let evd,id = 
	     Evd.fresh_global
	       (Global.env ()) evd
	       (Constrintern.locate_reference (Libnames.qualid_of_ident (mk_rel_id id)))
	   in 
           evd,(fst (destInd evd id))::l
	  )
	  fix_names
	  (evd',[])
      in
      Invfun.derive_correctness
	Functional_principles_types.make_scheme
	fix_names_as_constant
	lind;
      with e when CErrors.noncritical e ->
      let e' = process_vernac_interp_error e in
      warn_funind_cannot_build_inversion e'
  with e when CErrors.noncritical e ->
    let e' = process_vernac_interp_error e in
    warn_funind_cannot_build_inversion e'

let warn_cannot_define_graph =
  CWarnings.create ~name:"funind-cannot-define-graph" ~category:"funind"
    (fun (names,error) -> strbrk "Cannot define graph(s) for " ++
      h 1 names ++ error)

let warn_cannot_define_principle =
  CWarnings.create ~name:"funind-cannot-define-principle" ~category:"funind"
  (fun (names,error) -> strbrk "Cannot define induction principle(s) for "++
      h 1 names ++ error)

let warning_error names e =
  let e = process_vernac_interp_error e in
  let e_explain e =
    match e with
      | ToShow e -> 
	let e = process_vernac_interp_error e in
	spc () ++ CErrors.print e
      | _ -> 
	if do_observe () 
	then 
	  let e = process_vernac_interp_error e in 
	  (spc () ++ CErrors.print e)
	else mt ()
  in
  match e with
    | Building_graph e ->
       let names = prlist_with_sep (fun _ -> str","++spc ()) Ppconstr.pr_id names in
       warn_cannot_define_graph (names,e_explain e)
    | Defining_principle e ->
       let names = prlist_with_sep (fun _ -> str","++spc ()) Ppconstr.pr_id names in
       warn_cannot_define_principle (names,e_explain e)
    | _ -> raise e

let error_error names e =
  let e = process_vernac_interp_error e in
  let e_explain e =
    match e with
      | ToShow e -> spc () ++ CErrors.print e
      | _ -> if do_observe () then (spc () ++ CErrors.print e) else mt ()
  in
  match e with
    | Building_graph e ->
	user_err 
	  (str "Cannot define graph(s) for " ++
	     h 1 (prlist_with_sep (fun _ -> str","++spc ()) Ppconstr.pr_id names) ++
	     e_explain e)
    | _ -> raise e

let generate_principle (evd:Evd.evar_map ref) pconstants on_error
    is_general do_built (fix_rec_l:(Vernacexpr.fixpoint_expr * Vernacexpr.decl_notation list) list) recdefs  interactive_proof
    (continue_proof : int -> Names.Constant.t array -> EConstr.constr array -> int ->
      Tacmach.tactic) : unit =
  let names = List.map (function (({CAst.v=name},_),_,_,_,_),_ -> name) fix_rec_l in
  let fun_bodies = List.map2 prepare_body fix_rec_l recdefs in
  let funs_args = List.map fst fun_bodies in
  let funs_types =  List.map (function ((_,_,_,types,_),_) -> types) fix_rec_l in
  try
    (* We then register the Inductive graphs of the functions  *)
    Glob_term_to_relation.build_inductive !evd pconstants funs_args funs_types recdefs;
    if do_built
    then
      begin
	(*i The next call to mk_rel_id is valid since we have just construct the graph
	   Ensures by : do_built
	i*)
        let f_R_mut = qualid_of_ident @@ mk_rel_id (List.nth names 0) in
	let ind_kn =
	  fst (locate_with_msg
                 (pr_qualid f_R_mut++str ": Not an inductive type!")
		 locate_ind
		 f_R_mut)
	in
	let fname_kn (((fname,_),_,_,_,_),_) =
   let f_ref = qualid_of_ident ?loc:fname.CAst.loc fname.CAst.v in
          locate_with_msg
            (pr_qualid f_ref++str ": Not an inductive type!")
	    locate_constant
	    f_ref
	in
	let funs_kn = Array.of_list (List.map fname_kn fix_rec_l) in
	let _ =
	  List.map_i
	    (fun i x ->
	     let princ = Indrec.lookup_eliminator (ind_kn,i) (InProp) in
	     let env = Global.env () in
	     let evd = ref (Evd.from_env env) in
	     let evd',uprinc = Evd.fresh_global env !evd princ in
             let _ = evd := evd' in 
             let sigma, princ_type = Typing.type_of ~refresh:true env !evd uprinc in
             evd := sigma;
	     let princ_type = EConstr.Unsafe.to_constr princ_type in
    	     Functional_principles_types.generate_functional_principle
	       evd
		 interactive_proof
		 princ_type
		 None
		 None
		 (Array.of_list pconstants)
		 (* funs_kn *)
		 i
		 (continue_proof  0 [|funs_kn.(i)|])
	    )
	    0
	    fix_rec_l
	in
	Array.iter (add_Function is_general) funs_kn;
	()
      end
  with e when CErrors.noncritical e ->
    on_error names e

let register_struct is_rec (fixpoint_exprl:(Vernacexpr.fixpoint_expr * Vernacexpr.decl_notation list) list) =
  match fixpoint_exprl with
    | [(({CAst.v=fname},pl),_,bl,ret_type,body),_] when not is_rec ->
      let body = match body with | Some body -> body | None -> user_err ~hdr:"Function" (str "Body of Function must be given") in 
      ComDefinition.do_definition
        ~program_mode:false
	fname
        (Decl_kinds.Global,false,Decl_kinds.Definition) pl
        bl None body (Some ret_type);
       let evd,rev_pconstants =
	 List.fold_left
           (fun (evd,l) ((({CAst.v=fname},_),_,_,_,_),_) ->
	    let evd,c =
	      Evd.fresh_global
		(Global.env ()) evd (Constrintern.locate_reference (Libnames.qualid_of_ident fname)) in
            let (cst, u) = destConst evd c in
            let u = EInstance.kind evd u in
            evd,((cst, u) :: l)
	   )
	   (Evd.from_env (Global.env ()),[])
	   fixpoint_exprl
       in
       evd,List.rev rev_pconstants
    | _ ->
       ComFixpoint.do_fixpoint Global false fixpoint_exprl;
       let evd,rev_pconstants =
	 List.fold_left
           (fun (evd,l) ((({CAst.v=fname},_),_,_,_,_),_) ->
	    let evd,c =
	      Evd.fresh_global
		(Global.env ()) evd (Constrintern.locate_reference (Libnames.qualid_of_ident fname)) in
            let (cst, u) = destConst evd c in
            let u = EInstance.kind evd u in
            evd,((cst, u) :: l)
	   )
	   (Evd.from_env (Global.env ()),[])
	   fixpoint_exprl
       in
       evd,List.rev rev_pconstants
	   

let generate_correction_proof_wf f_ref tcc_lemma_ref
    is_mes functional_ref eq_ref rec_arg_num rec_arg_type nb_args relation
    (_: int) (_:Names.Constant.t array) (_:EConstr.constr array) (_:int) : Tacmach.tactic =
  Functional_principles_proofs.prove_principle_for_gen
    (f_ref,functional_ref,eq_ref)
    tcc_lemma_ref is_mes  rec_arg_num rec_arg_type relation


let register_wf ?(is_mes=false) fname rec_impls wf_rel_expr wf_arg using_lemmas args ret_type body
    pre_hook
    =
  let type_of_f = Constrexpr_ops.mkCProdN args ret_type in
  let rec_arg_num =
    let names =
      List.map
        CAst.(with_val (fun x -> x))
	(Constrexpr_ops.names_of_local_assums args)
    in
    match wf_arg with
      | None ->
	if Int.equal (List.length names) 1 then 1
	else error "Recursive argument must be specified"
      | Some wf_arg ->
	  List.index Name.equal (Name wf_arg) names
  in
  let unbounded_eq =
    let f_app_args =
      CAst.make @@ Constrexpr.CAppExpl(
         (None,qualid_of_ident fname,None) ,
	 (List.map
	    (function
               | {CAst.v=Anonymous} -> assert false
               | {CAst.v=Name e} -> (Constrexpr_ops.mkIdentC e)
	    )
	    (Constrexpr_ops.names_of_local_assums args)
	 )
	)
    in
    CAst.make @@ Constrexpr.CApp ((None,Constrexpr_ops.mkRefC (qualid_of_string "Logic.eq")),
		    [(f_app_args,None);(body,None)])
  in
  let eq = Constrexpr_ops.mkCProdN args unbounded_eq in
  let hook ((f_ref,_) as fconst) tcc_lemma_ref (functional_ref,_) (eq_ref,_) rec_arg_num rec_arg_type
      nb_args relation =
    try
      pre_hook [fconst]
	(generate_correction_proof_wf f_ref tcc_lemma_ref is_mes
	   functional_ref eq_ref rec_arg_num rec_arg_type nb_args relation
	);
      derive_inversion [fname]
    with e when CErrors.noncritical e ->
      (* No proof done *)
      ()
  in
  Recdef.recursive_definition
    is_mes fname rec_impls
    type_of_f
    wf_rel_expr
    rec_arg_num
    eq
    hook
    using_lemmas


let register_mes fname rec_impls wf_mes_expr wf_rel_expr_opt wf_arg using_lemmas args ret_type body =
  let wf_arg_type,wf_arg =
    match wf_arg with
      | None ->
	  begin
	    match args with
              | [Constrexpr.CLocalAssum ([{CAst.v=Name x}],k,t)] -> t,x
	      | _ -> error "Recursive argument must be specified"
	  end
      | Some wf_args ->
	  try
	    match
	      List.find
		(function
		   | Constrexpr.CLocalAssum(l,k,t) ->
		       List.exists
                         (function {CAst.v=Name id} -> Id.equal id wf_args | _ -> false)
			 l
		   | _ -> false
		)
		args
	    with
	      | Constrexpr.CLocalAssum(_,k,t)  ->	    t,wf_args
	      | _ -> assert false
	  with Not_found -> assert false
  in
  let wf_rel_from_mes,is_mes = 
    match wf_rel_expr_opt with 
      | None ->
	  let ltof =
	    let make_dir l = DirPath.make (List.rev_map Id.of_string l) in
            Libnames.qualid_of_path
              (Libnames.make_path (make_dir ["Arith";"Wf_nat"]) (Id.of_string "ltof"))
          in
	  let fun_from_mes =
	    let applied_mes =
	      Constrexpr_ops.mkAppC(wf_mes_expr,[Constrexpr_ops.mkIdentC wf_arg])    in
            Constrexpr_ops.mkLambdaC ([CAst.make @@ Name wf_arg],Constrexpr_ops.default_binder_kind,wf_arg_type,applied_mes)
	  in
	  let wf_rel_from_mes =
	    Constrexpr_ops.mkAppC(Constrexpr_ops.mkRefC  ltof,[wf_arg_type;fun_from_mes])
	  in
	  wf_rel_from_mes,true
      | Some wf_rel_expr -> 
	  let wf_rel_with_mes = 
	    let a = Names.Id.of_string "___a" in 
	    let b = Names.Id.of_string "___b" in 
	    Constrexpr_ops.mkLambdaC(
              [CAst.make @@ Name a; CAst.make @@ Name b],
	      Constrexpr.Default Explicit,
	      wf_arg_type,
	      Constrexpr_ops.mkAppC(wf_rel_expr,
			       [
				Constrexpr_ops.mkAppC(wf_mes_expr,[Constrexpr_ops.mkIdentC a]);
				Constrexpr_ops.mkAppC(wf_mes_expr,[Constrexpr_ops.mkIdentC b])
			       ])
			      )
	  in
	  wf_rel_with_mes,false
  in			       
  register_wf ~is_mes:is_mes fname rec_impls wf_rel_from_mes (Some wf_arg)
    using_lemmas args ret_type body

let map_option f = function 
  | None -> None 
  | Some v -> Some (f v)

open Constrexpr

let rec rebuild_bl aux bl typ =
	match bl,typ with
	  | [], _ -> List.rev aux,typ
	  | (CLocalAssum(nal,bk,_))::bl',typ ->
	     rebuild_nal aux bk bl' nal  typ
	  | (CLocalDef(na,_,_))::bl',{ CAst.v = CLetIn(_,nat,ty,typ') } ->
	    rebuild_bl (Constrexpr.CLocalDef(na,nat,ty)::aux)
	      bl' typ'
	  | _ -> assert false
and rebuild_nal aux bk bl' nal typ =
	match nal,typ with 
	  | _,{ CAst.v = CProdN([],typ) } -> rebuild_nal aux bk bl' nal typ
	  | [], _ -> rebuild_bl aux bl' typ
          | na::nal,{ CAst.v = CProdN(CLocalAssum(na'::nal',bk',nal't)::rest,typ') } ->
             if Name.equal (na.CAst.v) (na'.CAst.v) || Name.is_anonymous (na'.CAst.v)
	     then
	       let assum = CLocalAssum([na],bk,nal't) in
               let new_rest = if nal' = [] then rest else (CLocalAssum(nal',bk',nal't)::rest) in
	       rebuild_nal
		 (assum::aux)
		 bk
		 bl'
		 nal
		 (CAst.make @@ CProdN(new_rest,typ'))
	     else
	       let assum = CLocalAssum([na'],bk,nal't) in
               let new_rest = if nal' = [] then rest else (CLocalAssum(nal',bk',nal't)::rest) in
	       rebuild_nal
		 (assum::aux)
		 bk
		 bl'
		 (na::nal)
		 (CAst.make @@ CProdN(new_rest,typ'))
	  | _ ->
	     assert false

let rebuild_bl aux bl typ = rebuild_bl aux bl typ

let recompute_binder_list (fixpoint_exprl : (Vernacexpr.fixpoint_expr * Vernacexpr.decl_notation list) list) = 
  let fixl,ntns = ComFixpoint.extract_fixpoint_components false fixpoint_exprl in
  let ((_,_,typel),_,ctx,_) = ComFixpoint.interp_fixpoint ~cofix:false fixl ntns in
  let constr_expr_typel = 
    with_full_print (List.map (fun c -> Constrextern.extern_constr false (Global.env ()) (Evd.from_ctx ctx) (EConstr.of_constr c))) typel in
  let fixpoint_exprl_with_new_bl = 
    List.map2 (fun ((lna,(rec_arg_opt,rec_order),bl,ret_typ,opt_body),notation_list) fix_typ -> 
     
      let new_bl',new_ret_type = rebuild_bl [] bl fix_typ in 
      (((lna,(rec_arg_opt,rec_order),new_bl',new_ret_type,opt_body),notation_list):(Vernacexpr.fixpoint_expr * Vernacexpr.decl_notation list))
    )
      fixpoint_exprl constr_expr_typel 
  in 
  fixpoint_exprl_with_new_bl
  

let do_generate_principle pconstants on_error register_built interactive_proof
    (fixpoint_exprl:(Vernacexpr.fixpoint_expr * Vernacexpr.decl_notation list) list) :unit =
  List.iter (fun (_,l) -> if not (List.is_empty l) then error "Function does not support notations for now") fixpoint_exprl;
  let _is_struct =
    match fixpoint_exprl with
      | [((_,(wf_x,Constrexpr.CWfRec wf_rel),_,_,_),_) as fixpoint_expr] ->
          let (((({CAst.v=name},pl),_,args,types,body)),_)  as fixpoint_expr =
	    match recompute_binder_list [fixpoint_expr] with 
	      | [e] -> e
	      | _ -> assert false
	  in 
	  let fixpoint_exprl = [fixpoint_expr] in 
	  let body = match body with | Some body -> body | None -> user_err ~hdr:"Function" (str "Body of Function must be given") in 
	  let recdefs,rec_impls = build_newrecursive fixpoint_exprl in
	  let using_lemmas = [] in 
	  let pre_hook pconstants =
	    generate_principle
	      (ref (Evd.from_env (Global.env ())))
	      pconstants
	      on_error
	      true
	      register_built
	      fixpoint_exprl
	      recdefs
	      true
	  in
	  if register_built
          then register_wf name rec_impls wf_rel (map_option (fun x -> x.CAst.v) wf_x) using_lemmas args types body pre_hook;
	  false
      |[((_,(wf_x,Constrexpr.CMeasureRec(wf_mes,wf_rel_opt)),_,_,_),_) as fixpoint_expr] ->
          let (((({CAst.v=name},_),_,args,types,body)),_)  as fixpoint_expr =
	    match recompute_binder_list [fixpoint_expr] with 
	      | [e] -> e
	      | _ -> assert false
	  in 
	  let fixpoint_exprl = [fixpoint_expr] in 
	  let recdefs,rec_impls = build_newrecursive fixpoint_exprl in
	  let using_lemmas = [] in
	  let body = match body with | Some body -> body | None -> user_err ~hdr:"Function" (str "Body of Function must be given") in 
	  let pre_hook pconstants =
	    generate_principle
	      (ref (Evd.from_env (Global.env ())))
	      pconstants
	      on_error
	      true
	      register_built
	      fixpoint_exprl
	      recdefs
	      true
	  in
	  if register_built
          then register_mes name rec_impls wf_mes wf_rel_opt (map_option (fun x -> x.CAst.v) wf_x) using_lemmas args types body pre_hook;
	  true
      | _ ->
	  List.iter (function ((_na,(_,ord),_args,_body,_type),_not) ->
		       match ord with 
			 | Constrexpr.CMeasureRec _ | Constrexpr.CWfRec _ ->
			     error
			       ("Cannot use mutual definition with well-founded recursion or measure")
			 | _ -> ()
		    )
	    fixpoint_exprl;
	let fixpoint_exprl = recompute_binder_list fixpoint_exprl in 
	let fix_names =
          List.map (function ((({CAst.v=name},_),_,_,_,_),_) -> name) fixpoint_exprl
	in
	(* ok all the expressions are structural *)
  	let recdefs,rec_impls = build_newrecursive fixpoint_exprl in
	let is_rec = List.exists (is_rec fix_names) recdefs in
	let evd,pconstants =
	  if register_built
	  then register_struct is_rec fixpoint_exprl
	  else (Evd.from_env (Global.env ()),pconstants)
	in
	let evd = ref evd in 
	generate_principle
	  (ref !evd)
	  pconstants
	  on_error
	  false
	  register_built
	  fixpoint_exprl
	  recdefs
	  interactive_proof
	  (Functional_principles_proofs.prove_princ_for_struct evd interactive_proof);
	if register_built then begin derive_inversion fix_names; end;
	true; 
  in
  ()

let rec add_args id new_args = CAst.map (function
  | CRef (qid,_) as b ->
    if qualid_is_ident qid && Id.equal (qualid_basename qid) id then
      CAppExpl((None,qid,None),new_args)
    else b
  | CFix  _  | CCoFix _ -> anomaly ~label:"add_args " (Pp.str "todo.")
  | CProdN(nal,b1) ->
        CProdN(List.map (function  CLocalAssum (nal,k,b2) -> CLocalAssum (nal,k,add_args id new_args b2)
                                 | CLocalDef (na,b1,t) -> CLocalDef (na,add_args id new_args b1,Option.map (add_args id new_args) t)
                                 | CLocalPattern _ -> user_err (Pp.str "pattern with quote not allowed here.")) nal,
	     add_args id new_args  b1)
  | CLambdaN(nal,b1) ->
      CLambdaN(List.map (function  CLocalAssum (nal,k,b2) -> CLocalAssum (nal,k,add_args id new_args b2)
                                 | CLocalDef (na,b1,t) -> CLocalDef (na,add_args id new_args b1,Option.map (add_args id new_args) t)
                                 | CLocalPattern _ -> user_err (Pp.str "pattern with quote not allowed here.")) nal,
	       add_args id new_args  b1)
  | CLetIn(na,b1,t,b2) ->
      CLetIn(na,add_args id new_args b1,Option.map (add_args id new_args) t,add_args id new_args b2)
  | CAppExpl((pf,qid,us),exprl) ->
    if qualid_is_ident qid && Id.equal (qualid_basename qid) id then
      CAppExpl((pf,qid,us),new_args@(List.map (add_args id new_args) exprl))
    else CAppExpl((pf,qid,us),List.map (add_args id new_args) exprl)
  | CApp((pf,b),bl) ->
      CApp((pf,add_args id new_args b),
	   List.map (fun (e,o) -> add_args id new_args e,o) bl)
  | CCases(sty,b_option,cel,cal) ->
      CCases(sty,Option.map (add_args id new_args) b_option,
	     List.map (fun (b,na,b_option) ->
			 add_args id new_args b,
			 na, b_option) cel,
             List.map CAst.(map (fun (cpl,e) -> (cpl,add_args id new_args e))) cal
	    )
  | CLetTuple(nal,(na,b_option),b1,b2) ->
      CLetTuple(nal,(na,Option.map (add_args id new_args) b_option),
		add_args id new_args b1,
		add_args id new_args b2
	       )

  | CIf(b1,(na,b_option),b2,b3) ->
      CIf(add_args id new_args b1,
	  (na,Option.map (add_args id new_args) b_option),
	  add_args id new_args b2,
	  add_args id new_args b3
	 )
  | CHole _
  | CPatVar _
  | CEvar _
  | CPrim _
  | CSort _ as b -> b
  | CCast(b1,b2)  ->
      CCast(add_args id new_args b1,
            Glob_ops.map_cast_type (add_args id new_args) b2)
  | CRecord pars ->
      CRecord (List.map (fun (e,o) -> e, add_args id new_args o) pars)
  | CNotation _ -> anomaly ~label:"add_args " (Pp.str "CNotation.")
  | CGeneralization _ -> anomaly ~label:"add_args " (Pp.str "CGeneralization.")
  | CDelimiters _ -> anomaly ~label:"add_args " (Pp.str "CDelimiters.")
  )
exception Stop of  Constrexpr.constr_expr


(* [chop_n_arrow n t] chops the [n] first arrows in [t]
   Acts on Constrexpr.constr_expr
*)
let rec chop_n_arrow n t =
  if n <= 0
  then t (* If we have already removed all the arrows then return the type *)
  else (* If not we check the form of [t] *)
    match t.CAst.v with
      | Constrexpr.CProdN(nal_ta',t') -> (* If we have a forall, two results are possible :
					     either we need to discard more than the number of arrows contained
					     in this product declaration then we just recall [chop_n_arrow] on
					     the remaining number of arrow to chop and [t'] we discard it and
					     recall [chop_n_arrow], either this product contains more arrows
					     than the number we need to chop and then we return the new type
					  *)
	  begin
	    try
	      let new_n =
		let rec aux (n:int) = function
		    [] -> n
                | CLocalAssum(nal,k,t'')::nal_ta' ->
		    let nal_l = List.length nal in
		    if n >= nal_l
		    then
		      aux (n - nal_l) nal_ta'
		    else
		      let new_t' = CAst.make @@
			Constrexpr.CProdN(
                                        CLocalAssum((snd (List.chop n nal)),k,t'')::nal_ta',t')
		      in
		      raise (Stop new_t')
                | _ -> anomaly (Pp.str "Not enough products.")
		in
		aux n nal_ta'
	    in
	      chop_n_arrow new_n t'
	    with Stop t -> t
	  end
      | _ -> anomaly (Pp.str "Not enough products.")


let rec get_args b t : Constrexpr.local_binder_expr list *
    Constrexpr.constr_expr * Constrexpr.constr_expr =
  match b.CAst.v with
    | Constrexpr.CLambdaN (CLocalAssum(nal,k,ta) as d::rest, b') ->
	begin
          let n = List.length nal in
          let nal_tas,b'',t'' = get_args (CAst.make ?loc:b.CAst.loc @@ Constrexpr.CLambdaN (rest,b')) (chop_n_arrow n t) in
          d :: nal_tas, b'',t''
	end
    | Constrexpr.CLambdaN ([], b) -> [],b,t
    | _ -> [],b,t


let make_graph (f_ref : GlobRef.t) =
  let c,c_body =
    match f_ref with
    | ConstRef c ->
      begin try c,Global.lookup_constant c
        with Not_found ->
          let sigma, env = Pfedit.get_current_context () in
          raise (UserError (None,str "Cannot find " ++ Printer.pr_leconstr_env env sigma (mkConst c)) )
      end
    | _ -> raise (UserError (None, str "Not a function reference") )
  in
  (match Global.body_of_constant_body c_body with
     | None -> error "Cannot build a graph over an axiom!"
     | Some (body, _) ->
	 let env = Global.env () in
	 let sigma = Evd.from_env env in
	 let extern_body,extern_type =
	   with_full_print (fun () ->
		(Constrextern.extern_constr false env sigma (EConstr.of_constr body),
		 Constrextern.extern_type false env sigma
                   (EConstr.of_constr (*FIXME*) c_body.const_type)
		)
	     )
	     ()
	 in
	 let (nal_tas,b,t)  = get_args extern_body extern_type in
	 let expr_list =
	   match b.CAst.v with
	     | Constrexpr.CFix(l_id,fixexprl) ->
		 let l =
		   List.map
		     (fun (id,(n,recexp),bl,t,b) ->
                        let { CAst.loc; v=rec_id } = Option.get n in
			let new_args =
			  List.flatten
			    (List.map
			       (function
				  | Constrexpr.CLocalDef (na,_,_)-> []
				  | Constrexpr.CLocalAssum (nal,_,_) ->
				      List.map
                                        (fun {CAst.loc;v=n} -> CAst.make ?loc @@
                                           CRef(Libnames.qualid_of_ident ?loc @@ Nameops.Name.get_id n,None))
					nal
                                  | Constrexpr.CLocalPattern _ -> assert false
			       )
			       nal_tas
			    )
			in
                        let b' = add_args id.CAst.v new_args b in
                        ((((id,None), ( Some CAst.(make rec_id),CStructRec),nal_tas@bl,t,Some b'),[]):(Vernacexpr.fixpoint_expr * Vernacexpr.decl_notation list))
		     )
		     fixexprl
		 in
		 l
	     | _ ->
		let id = Label.to_id (Constant.label c) in
                 [((CAst.make id,None),(None,Constrexpr.CStructRec),nal_tas,t,Some b),[]]
	 in
         let mp = Constant.modpath c in
	 do_generate_principle [c,Univ.Instance.empty] error_error  false false expr_list;
	 (* We register the infos *)
	 List.iter
           (fun ((({CAst.v=id},_),_,_,_,_),_) -> add_Function false (Constant.make2 mp (Label.of_id id)))
	   expr_list)

let do_generate_principle = do_generate_principle [] warning_error true


