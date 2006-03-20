open Printer
open Util
open Term
open Termops 
open Names 
open Declarations
open Pp
open Entries
open Hiddentac
open Evd
open Tacmach
open Proof_type
open Tacticals
open Tactics
open Indfun_common


(* let msgnl = Pp.msgnl *)

let observe strm =  
  if Tacinterp.get_debug () <> Tactic_debug.DebugOff 
  then Pp.msgnl strm 
  else ()

let observe_tac s tac g = 
  if Tacinterp.get_debug () <> Tactic_debug.DebugOff 
  then Recdef.do_observe_tac s tac g
  else tac g



let tclTRYD tac =
  if  !Options.debug  ||  Tacinterp.get_debug () <> Tactic_debug.DebugOff
  then tclTRY tac
  else tac


type rewrite_dir =
  | LR
  | RL

let rew_all ?(rev_order=false) lr : tactic =
  let rew =
    match lr with
      | LR -> Equality.rewriteLR
      | RL ->  Equality.rewriteRL
  in
  let order =
    if rev_order then List.rev else fun x -> x
  in
  fun g ->
    onHyps
      pf_hyps
      (fun l -> tclMAP (fun (id,_,_) ->  tclTRY (rew (mkVar id))) (order l))
      g

      
let test_var args arg_num =
  isVar args.(arg_num)
   


let rewrite_until_var arg_num : tactic =
  let constr_eq =  (Coqlib.build_coq_eq_data ()).Coqlib.eq in
  let replace_if_unify arg (pat,cl,id,lhs)  : tactic =
    fun g ->
      try
	let (evd,matched) =
	  Unification.w_unify_to_subterm
	    (pf_env g) ~mod_delta:false (pat,arg) cl.Clenv.env
	in
	let cl' = {cl with Clenv.env = evd } in
	let c2 = Clenv.clenv_nf_meta cl' lhs in
	(Equality.replace matched c2) g
      with _ -> tclFAIL 0 (str "") g
  in
  let rewrite_on_step equalities : tactic =
    fun g ->
      match kind_of_term (pf_concl g) with
	| App(_,args) when (not (test_var args arg_num)) ->
(* 	    tclFIRST (List.map (fun a -> observe_tac (str "replace_if_unify") (replace_if_unify args.(arg_num) a)) equalities) g *)
	    tclFIRST (List.map (replace_if_unify args.(arg_num)) equalities) g
	| _ ->
	    raise (Util.UserError("", (str "No more rewrite" ++
					 pr_lconstr_env (pf_env g) (pf_concl g))))
  in
  fun g ->
    let equalities =
      List.filter
	(
	  fun (_,_,id_t) ->
	    match kind_of_term id_t with
	      | App(f,_) -> eq_constr f constr_eq
	      | _ -> false
	)
	(pf_hyps g)
    in
    let f (id,_,ctype)  =
      let c = mkVar id in
      let eqclause = Clenv.make_clenv_binding g (c,ctype) Rawterm.NoBindings in
      let clause_type = Clenv.clenv_type eqclause in
      let f,args = decompose_app (clause_type) in
      let rec split_last_two = function
	| [c1;c2] -> (c1, c2)
	| x::y::z ->
	    split_last_two (y::z)
	| _ ->
	    error ("The term provided is not an equivalence")
      in
      let (c1,c2) = split_last_two args in
      (c2,eqclause,id,c1)
    in
    let matching_hyps = List.map f equalities in
    tclTRY (tclREPEAT (tclPROGRESS (rewrite_on_step matching_hyps))) g



let make_refl_eq type_of_t t  =
  let refl_equal_term = Lazy.force refl_equal in
  mkApp(refl_equal_term,[|type_of_t;t|])

let case_eq  tac body term g =
(*   msgnl (str "case_eq on " ++ pr_lconstr_env (pf_env g) term); *)
  let type_of_term = pf_type_of g term in
  let term_eq =
    make_refl_eq type_of_term term
  in
  let ba_fun ba  : tactic =
    fun g ->
      tclTHENSEQ
	[intro_patterns [](* ba.branchnames *);
	 fun g ->
	   let (_,_,new_term_value_eq)  = pf_last_hyp g in
	   let new_term_value =
	     match kind_of_term new_term_value_eq with
	       | App(f,[| _;_;args2 |]) -> args2
	     | _ ->
		 Pp.msgnl (pr_gls g ++ fnl () ++ str "last hyp is" ++
			     pr_lconstr_env (pf_env g) new_term_value_eq
			  );
		 assert false
	   in
	   let fun_body =
	     mkLambda(Anonymous,type_of_term,replace_term term (mkRel 1) body)
	   in
	   let new_body = mkApp(fun_body,[| new_term_value |]) in
	   tac (pf_nf_betaiota g new_body) g
	]
	g
  in
    (
      tclTHENSEQ
	[
	  h_generalize [term_eq];
	  pattern_option [[-1],term] None;
	  case_then_using Genarg.IntroAnonymous (ba_fun) None ([],[]) term
	]
    )
    g



let my_reflexivity : tactic =
  let test_eq =
    lazy (eq_constr (Coqlib.build_coq_eq ()))
  in
  let build_reflexivity  =
    lazy (fun ty t -> mkApp((Coqlib.build_coq_eq_data ()).Coqlib.refl,[|ty;t|]))
  in
  fun g ->
    begin
    match kind_of_term (pf_concl g) with
      | App(eq,[|ty;t1;t2|]) when (Lazy.force test_eq) eq ->
	    if not (Termops.occur_existential t1)
	    then tclTHEN (h_change None (mkApp(eq,[|ty;t1;t1|]))  onConcl ) (apply ((Lazy.force build_reflexivity) ty t1))
	    else if not (Termops.occur_existential t2)
	    then   tclTHEN (h_change None (mkApp(eq,[|ty;t2;t2|])) onConcl ) (apply ((Lazy.force build_reflexivity) ty t2))
	    else tclFAIL 0 (str "")
	      
      | _ -> tclFAIL 0 (str "")
    end g

let eauto g = 
  tclFIRST 
    [
      Eauto.e_assumption
      ;
      h_exact  (Coqlib.build_coq_I ());
      tclTHEN 
	(rew_all LR) 
	(Eauto. gen_eauto false (false,5) [] (Some [])) 
    ]
    g

  

let conclude fixes g =
(*   let clear_fixes =  *)
(*     let l = Idmap.fold (fun _ (_,_,id,_) acc -> id::acc) fixes [] in  *)
(*     h_clear false l  *)
(*   in   *)
  match kind_of_term (pf_concl g) with 
    | App(pte,args) -> 
	let tac = 
	  if isVar pte 
	  then 
	    try 
	      let idxs,body,this_fix_id,new_type = Idmap.find (destVar pte) fixes
	      in 
	      let idx = idxs - 1 in 
	      tclTHEN 
		(rewrite_until_var idx)
		(* If we have an IH then with use the fixpoint *) 
		(Eauto.e_resolve_constr (mkVar this_fix_id)) 
		(* And left the generated subgoals to eauto *) 
	    with Not_found -> (* this is not a pte *) 
	      tclIDTAC
	  else tclIDTAC 
	in 
	tclTHENSEQ [tac; (* clear_fixes; *) eauto] g
    | _ -> eauto g
	
	      
let finalize_proof interactive_proof fixes hyps fnames term = 
  tclORELSE 
    (
      tclFIRST 
	(List.map 
	   (fun id -> tclTHEN (Eauto.e_resolve_constr (mkVar id)) 
	      (tclCOMPLETE (conclude fixes))) hyps
	)
    )
    (if interactive_proof then tclIDTAC else tclFAIL 0 (str ""))
    
    


let do_prove_princ_for_struct interactive_proof
    (* (rec_pos:int option) *)  (fnames:constant list)
    (ptes:identifier list) (fixes:(int*constr*identifier*constr) Idmap.t) (hyps: identifier list)
      (term:constr) : tactic =
  let finalize_proof term =
    finalize_proof (* rec_pos *) interactive_proof fixes hyps fnames term
  in
  let rec do_prove_princ_for_struct do_finalize term g =
(*      if Tacinterp.get_debug () <> Tactic_debug.DebugOff  *)
(*      then msgnl (str "Proving with body : " ++ pr_lconstr_env (pf_env g) term); *)
    let tac =
      fun g ->
	match kind_of_term term with
	  | Case(_,_,t,_) ->
	      observe_tac "case_eq" 
	      (case_eq (do_prove_princ_for_struct do_finalize) term t) g
	  | Lambda(n,t,b) ->
	      begin
		match kind_of_term( pf_concl g) with
		  | Prod _ ->
		      tclTHEN
			intro
			(fun g' ->
			   let (id,_,_) = pf_last_hyp g' in
			   let new_term = pf_nf_betaiota g' (mkApp(term,[|mkVar id|])) in
			   do_prove_princ_for_struct do_finalize new_term g'
			) g
		  | _ ->
		      do_finalize term g
	      end
	  | Cast(t,_,_) -> do_prove_princ_for_struct do_finalize t g
	  | Const _ | Var _ | Meta _ | Evar _ | Sort _ | Construct _ | Ind _ ->
	      do_finalize term g
	  | App(_,_) ->
	      let f,args = decompose_app term in
	      begin
		match kind_of_term f with
		  | Var _ | Construct _ | Rel _ | Evar _ | Meta _  | Ind _ ->
		      do_prove_princ_for_struct_args do_finalize f args g
		  | Const c when not (List.mem c fnames) ->
		      do_prove_princ_for_struct_args do_finalize f args g
		  | Const _ ->
		      do_finalize  term g
		  | _ ->
		      msg_warning (str "Applied binders not yet implemented: "++ Printer.pr_lconstr_env (pf_env g) term) ;
		      tclFAIL 0 (str "TODO") g
	      end
	  | Fix _ | CoFix _ ->
	      error ( "Anonymous local (co)fixpoints are not handled yet")
	  | Prod _ -> assert false
	  | LetIn (Name id,v,t,b) ->
	      do_prove_princ_for_struct do_finalize (subst1 v b) g
	  | LetIn(Anonymous,_,_,b) ->
	      do_prove_princ_for_struct do_finalize (pop  b) g
	  | _ ->
	      errorlabstrm "" (str "in do_prove_princ_for_struct found : "(* ++ *)
(* 				 pr_lconstr_env (pf_env g) term *)
			      )

      in
       tac g
  and do_prove_princ_for_struct_args do_finalize f_args' args :tactic =
    fun g ->
(*      if Tacinterp.get_debug () <> Tactic_debug.DebugOff  *)
(*      then msgnl (str "do_prove_princ_for_struct_args with "  ++  *)
(* 		   pr_lconstr_env (pf_env g) f_args' *)
(* 		); *)
      let tac =
	match args with
	  | []  ->
	      do_finalize f_args'
	  | arg::args ->
	      let do_finalize new_arg =
		tclTRYD
		  (do_prove_princ_for_struct_args
		     do_finalize
		     (mkApp(f_args',[|new_arg|]))
		     args
		  )
	      in
	      do_prove_princ_for_struct do_finalize arg
      in
      tclTRYD(tac) g
	
  in
  do_prove_princ_for_struct
    (finalize_proof)
    term

let is_pte_type t =
  isSort (snd (decompose_prod t))
    
let is_pte (_,_,t) = is_pte_type t

exception Not_Rec

let prove_princ_for_struct interactive_proof fun_num fnames all_funs _naprams : tactic =
   fun goal -> 
     observe (str "Proving principle for "++ str (string_of_int fun_num) ++ str "th function : " ++ 
		Printer.pr_lconstr (mkConst fnames.(fun_num)));
     let princ_type = pf_concl goal in 
     let princ_info = compute_elim_sig princ_type in
     let get_body const = 
       match (Global.lookup_constant const ).const_body with
	 | Some b ->
	     let body = force b in
	     Tacred.cbv_norm_flags
	       (Closure.RedFlags.mkflags [Closure.RedFlags.fZETA])
	       (Global.env ())
	       (Evd.empty)
	       body
	 | None -> error ( "Cannot define a principle over an axiom ")
     in
     let fbody = get_body fnames.(fun_num) in
     let params : identifier list ref = ref [] in 
     let predicates : identifier list ref = ref [] in 
     let args : identifier list ref = ref [] in 
     let branches : identifier list ref = ref [] in
     let pte_to_fix = ref Idmap.empty in 
     let fbody_with_params = ref None in 
     let intro_with_remembrance  ref number : tactic = 
       tclTHEN 
	 ( tclDO number intro ) 
	 (fun g -> 
	    let last_n = list_chop number (pf_hyps g) in 
	    ref :=  List.map (fun (id,_,_) -> id) (fst last_n)@ !ref;
	    tclIDTAC g
	 )
     in
     let rec partial_combine body params = 
       match kind_of_term body,params with 
	 | Lambda (x,t,b),param::params -> 
	     partial_combine (subst1 param b) params
	 | Fix(infos),_ ->
	     body,params, Some (infos)
	 | _ -> body,params,None
     in 
     let build_pte_to_fix (offset:int) params predicates
	 ((idxs,fix_num),(na,typearray,ca))  (avoid,_) =
(*        let true_params,_ =  list_chop offset params  in  *)
       let true_params = List.rev params in
       let avoid = ref avoid in 
       let res = list_fold_left_i
	 (fun i acc pte_id  -> 
	    let this_fix_id = fresh_id !avoid "fix___" in 
	    avoid := this_fix_id::!avoid;
(* 	    let this_body = substl (List.rev fnames_as_constr) ca.(i) in  *)
	    let this_body = substl (List.rev (Array.to_list all_funs)) ca.(i) in 
	    let new_type = prod_applist typearray.(i) true_params 
	    and new_body = Reductionops.nf_beta (applist(this_body,true_params)) in
	    let new_type_args,_ = decompose_prod new_type in 
	    let nargs = List.length new_type_args in
	    let pte_args = 
	      (* 	      let rev_args = List.rev_map (fun (id,_,_) -> mkVar id) new_type_args in  *)
	      let f = applist(all_funs.(i),true_params) in
	      let app_f = mkApp(f,Array.init nargs (fun i -> mkRel(nargs - i))) in 
	      (Array.to_list (Array.init nargs (fun i -> mkRel(nargs - i))))@[app_f]
	    in
	    let app_pte = applist(mkVar pte_id,pte_args) in 
	    let new_type = compose_prod new_type_args app_pte in 
	    let fix_info = idxs.(i) - offset + 1,new_body,this_fix_id ,new_type in 
	    pte_to_fix := Idmap.add  pte_id fix_info !pte_to_fix;
	    fix_info::acc
	 )
	 0 
	 []
	 predicates
       in
       !avoid,List.rev res
     in     
     let mk_fixes : tactic = 
       fun g -> 
	 let body_p,params',fix_infos = 
	   partial_combine fbody (List.rev_map mkVar  !params) 
	 in
	 fbody_with_params := Some body_p;
	 let offset  = List.length params' in 
	 let not_real_param,true_params = 
	   list_chop 
	     ((List.length !params ) - offset)
	     !params
	 in
	 params := true_params; args := not_real_param;
	 observe (str "mk_fixes : params are "++ 
		    prlist_with_sep spc
		    (fun id -> Printer.pr_lconstr (mkVar id))
		    !params
		 );
	 let new_avoid,infos = 
	   option_fold_right
	     (build_pte_to_fix 
		offset
		(List.map mkVar !params)
		(List.rev !predicates)
	     )
	     fix_infos
	     ((pf_ids_of_hyps g),[])
	 in
	 let pre_info,infos = list_chop fun_num infos in
	 match pre_info,infos with 
	   | [],[] -> tclIDTAC g 
	   | _,(idx,_,fix_id,_)::infos' -> 
	       let other_fix_info = 
		 List.map (fun (idx,_,fix_id,fix_typ) -> fix_id,idx,fix_typ) (pre_info@infos')
	       in
	       tclORELSE 
		 (h_mutual_fix fix_id idx other_fix_info) 
		 (tclFAIL 1000 (str "bad index" ++ str (string_of_int idx) ++
				  str "offset := " ++
				  (str (string_of_int offset))))
		 g
	   | _,[] -> anomaly "Not a valid information"
     in
     let do_prove pte_to_fix args : tactic = 
       fun g -> 
	 match kind_of_term (pf_concl g) with 
	   | App(pte,pte_args) when isVar pte -> 
	       begin
		 let pte = destVar pte in
		 try
		   let (_idx,_new_body,_this_fix_id,_new_type) =
		     try Idmap.find pte pte_to_fix with _ -> raise Not_Rec
		   in
		 let nparams = List.length !params in
		 let args_as_constr = List.map mkVar  args in
		  let rec_num,new_body =
		    let idx' = list_index pte (List.rev !predicates)  - 1 in 
		    let f = fnames.(idx') in 
		    let body_with_params = match !fbody_with_params with Some f -> f | _ -> anomaly "" 
		    in
		    let name_of_f = Name ( id_of_label (con_label f)) in 
		    let ((rec_nums,_),(na,_,bodies)) = destFix body_with_params in 
		    let idx'' = list_index name_of_f (Array.to_list na) - 1 in 
		    let body = substl (List.rev (Array.to_list all_funs)) bodies.(idx'') in 
		    let body = Reductionops.nf_beta (applist(body,(List.rev_map mkVar !params))) in
		    rec_nums.(idx'') - nparams ,body
		  in
		  let applied_body =
		    Reductionops.nf_beta 
		      (applist(new_body,List.rev args_as_constr))
		  in
		  let do_prove = 	
		    do_prove_princ_for_struct
		      interactive_proof
		      (Array.to_list fnames)
		      !predicates
		      pte_to_fix
		      !branches
		      applied_body 
		  in
		  let replace_and_prove = 
		    tclTHENS
		      (fun g -> 
			 observe (str "replacing " ++ 
				    Printer.pr_lconstr_env (pf_env g) (array_last pte_args) ++
				    str " with " ++ 
				    Printer.pr_lconstr_env (pf_env g) applied_body  ++ 
				    str " rec_arg_num is " ++ str (string_of_int rec_num)
				 );
			 (Equality.replace (array_last pte_args) applied_body) g
		      )
		      [
			do_prove;
			try 
			  let id = List.nth (List.rev args_as_constr) (rec_num) in
			  observe (str "choosen var := "++ Printer.pr_lconstr id);
			  (tclTHENSEQ
			     [(h_simplest_case id);
			      Tactics.intros_reflexivity
			     ])
			with _ -> tclIDTAC
			
		      ]
		  in
		  (observe_tac "doing replacement" ( replace_and_prove)) g 
		 with Not_Rec -> 
		   let fname = destConst (fst (decompose_app (array_last pte_args))) in 
		   tclTHEN 
		     (unfold_in_concl [([],Names.EvalConstRef fname)]) 
		     (observe_tac "" (fun g' ->
					do_prove_princ_for_struct
					  interactive_proof
					  (Array.to_list fnames)
					  !predicates
					  pte_to_fix
					  !branches
					  (array_last (snd (destApp (pf_concl g'))))
					  g'
				     ))
		     g
	       end
	   | _ -> assert false
     in
     tclTHENSEQ 
       [
	 (fun g -> observe_tac "introducing params" (intro_with_remembrance  params princ_info.nparams) g);
	 (fun g -> observe_tac "introducing predicate" (intro_with_remembrance predicates  princ_info.npredicates) g);
	 (fun g -> observe_tac "introducing branches" (intro_with_remembrance branches princ_info.nbranches) g);
	 (fun g -> observe_tac "declaring fix(es)" mk_fixes g);
	 (fun g -> 
	    let args = ref [] in 
	    tclTHEN 
	      (fun g -> observe_tac "introducing args" (intro_with_remembrance args princ_info.nargs) g)
	      (fun g -> observe_tac "proving" (fun  g -> do_prove !pte_to_fix !args g) g)
	      g
	 )
       ]
       goal








 
   



  
exception Toberemoved_with_rel of int*constr
exception Toberemoved
  
let compute_new_princ_type_from_rel rel_to_fun sorts princ_type =
  let princ_type_info = compute_elim_sig princ_type in 
  let env = Global.env () in 
(*   let type_sort = (Termops.new_sort_in_family InType) in  *)
  let change_predicate_sort i (x,_,t) = 
    let new_sort = sorts.(i) in
    let args,_ = decompose_prod t in 
    let real_args = 
      if princ_type_info.indarg_in_concl 
      then List.tl args 
      else args
    in
    x,None,compose_prod real_args (mkSort new_sort) 
  in
  let new_predicates = 
    list_map_i
      change_predicate_sort 
      0
      princ_type_info.predicates
  in
  let env_with_params_and_predicates = 
    Environ.push_rel_context 
      new_predicates
      (Environ.push_rel_context 
	 princ_type_info.params 
	 env
      )
  in
  let rel_as_kn = 
    fst (match princ_type_info.indref with
	   | Some (Libnames.IndRef ind) -> ind 
	   | _ -> failwith "Not a valid predicate"
	)
  in
  let pre_princ = 
    it_mkProd_or_LetIn 
      ~init:
      (it_mkProd_or_LetIn 
	 ~init:(option_fold_right
			   mkProd_or_LetIn
			   princ_type_info.indarg
			   princ_type_info.concl
			)
	 princ_type_info.args
      )
      princ_type_info.branches
  in
  let is_dom c =
    match kind_of_term c with
      | Ind((u,_)) -> u = rel_as_kn
      | Construct((u,_),_) -> u = rel_as_kn
      | _ -> false
  in
  let get_fun_num c =
    match kind_of_term c with
      | Ind(_,num) -> num
      | Construct((_,num),_) -> num
      | _ -> assert false
  in
  let dummy_var = mkVar (id_of_string "________") in
  let mk_replacement i args =
    mkApp(rel_to_fun.(i),Array.map pop (array_get_start args))
  in
  let rec has_dummy_var t  =
    fold_constr
      (fun b t -> b || (eq_constr t dummy_var) || (has_dummy_var t))
      false
      t
  in
  let rec compute_new_princ_type remove env pre_princ : types*(constr list) =
    let (new_princ_type,_) as res =
      match kind_of_term pre_princ with
	| Rel n ->
	    begin
	      try match Environ.lookup_rel n env with
		| _,_,t when is_dom t -> raise Toberemoved
		| _ -> pre_princ,[] with Not_found -> assert false
	    end
	| Prod(x,t,b) ->
	    compute_new_princ_type_for_binder remove mkProd env x t b
	| Lambda(x,t,b) ->
	    compute_new_princ_type_for_binder remove mkLambda env x t b
	| Ind _ | Construct _ when is_dom pre_princ -> raise Toberemoved
	| App(f,args) when is_dom f ->
	    let var_to_be_removed = destRel (array_last args) in
	    let num = get_fun_num f in
	    raise (Toberemoved_with_rel (var_to_be_removed,mk_replacement num args))
	| App(f,args) ->
	    let is_pte = 
	      match kind_of_term f with 
		| Rel n ->  
		    is_pte (Environ.lookup_rel n env)
		| _ -> false 
	    in
	    let args = 
	      if is_pte && remove 
	      then array_get_start args 
	      else args 
	    in
	    let new_args,binders_to_remove =
	      Array.fold_right (compute_new_princ_type_with_acc remove env)
		args
		([],[])
	    in
	    let new_f,binders_to_remove_from_f = compute_new_princ_type remove env f in
	    mkApp(new_f,Array.of_list new_args),
	    list_union_eq eq_constr binders_to_remove_from_f binders_to_remove
	| LetIn(x,v,t,b) ->
	    compute_new_princ_type_for_letin remove env x v t b
	| _ -> pre_princ,[]
    in
(*     if Tacinterp.get_debug () <> Tactic_debug.DebugOff *)
(*     then *)
(*       Pp.msgnl (str "compute_new_princ_type for "++ *)
(* 	       pr_lconstr_env env pre_princ ++ *)
(* 	       str" is "++ *)
(* 	       pr_lconstr_env env new_princ_type); *)
      res
	
  and compute_new_princ_type_for_binder remove bind_fun env x t b =
    begin
      try
	let new_t,binders_to_remove_from_t = compute_new_princ_type remove env t in
	let new_x : name = get_name (ids_of_context env) x in
	let new_env = Environ.push_rel (x,None,t) env in
	let new_b,binders_to_remove_from_b = compute_new_princ_type remove new_env b in
	if List.exists (eq_constr (mkRel 1)) binders_to_remove_from_b
	then (pop new_b),filter_map (eq_constr (mkRel 1)) pop binders_to_remove_from_b
	else
	  (
	    bind_fun(new_x,new_t,new_b),
	    list_union_eq
	      eq_constr
	      binders_to_remove_from_t
	      (List.map pop binders_to_remove_from_b)
	  )
	
      with
	| Toberemoved ->
(* 	    msgnl (str "Decl of "++Ppconstr.pr_name x ++ str " is removed "); *)
	    let new_b,binders_to_remove_from_b = compute_new_princ_type  remove env (substnl [dummy_var] 1 b)  in
	    new_b, List.map pop binders_to_remove_from_b
	| Toberemoved_with_rel (n,c) ->
(* 	    msgnl (str "Decl of "++Ppconstr.pr_name x ++ str " is removed "); *)
	    let new_b,binders_to_remove_from_b = compute_new_princ_type  remove env (substnl [c] n b)  in
	    new_b, list_add_set_eq eq_constr (mkRel n) (List.map pop binders_to_remove_from_b)
    end
  and compute_new_princ_type_for_letin remove env x v t b =
    begin
      try
	let new_t,binders_to_remove_from_t = compute_new_princ_type remove env t in
	let new_v,binders_to_remove_from_v = compute_new_princ_type remove env v in
	let new_x : name = get_name (ids_of_context env) x in
	let new_env = Environ.push_rel (x,Some v,t) env in
	let new_b,binders_to_remove_from_b = compute_new_princ_type remove  new_env b in
	if List.exists (eq_constr (mkRel 1)) binders_to_remove_from_b
	then (pop new_b),filter_map (eq_constr (mkRel 1)) pop binders_to_remove_from_b
	else
	  (
	    mkLetIn(new_x,new_v,new_t,new_b),
	    list_union_eq
	      eq_constr
	      (list_union_eq eq_constr binders_to_remove_from_t binders_to_remove_from_v)
	      (List.map pop binders_to_remove_from_b)
	  )
	
      with
	| Toberemoved ->
(* 	    msgnl (str "Decl of "++Ppconstr.pr_name x ++ str " is removed "); *)
	    let new_b,binders_to_remove_from_b = compute_new_princ_type remove env (substnl [dummy_var] 1 b)  in
	    new_b, List.map pop binders_to_remove_from_b
	| Toberemoved_with_rel (n,c) ->
(* 	    msgnl (str "Decl of "++Ppconstr.pr_name x ++ str " is removed "); *)
	    let new_b,binders_to_remove_from_b = compute_new_princ_type remove env (substnl [c] n b)  in
	    new_b, list_add_set_eq eq_constr (mkRel n) (List.map pop binders_to_remove_from_b)
    end
  and  compute_new_princ_type_with_acc remove env e (c_acc,to_remove_acc)  =
	      let new_e,to_remove_from_e = compute_new_princ_type remove env e
	      in
	      new_e::c_acc,list_union_eq eq_constr to_remove_from_e to_remove_acc
  in
(*   Pp.msgnl (Printer.pr_lconstr_env  env_with_params_and_predicates pre_princ); *)
  let pre_res,_ = 
    compute_new_princ_type princ_type_info.indarg_in_concl env_with_params_and_predicates pre_princ in 
  it_mkProd_or_LetIn  	 
    ~init:(it_mkProd_or_LetIn ~init:pre_res new_predicates)
    princ_type_info.params
    
  

let change_property_sort toSort princ princName = 
  let princ_info = compute_elim_sig princ in 
  let change_sort_in_predicate (x,v,t) = 
    (x,None,
     let args,_ = decompose_prod t in 
     compose_prod args (mkSort toSort)
    )
  in 
  let princName_as_constr = Tacinterp.constr_of_id (Global.env ()) princName in 
  let init = 
    let nargs =  (princ_info.nparams + (List.length  princ_info.predicates)) in 
    mkApp(princName_as_constr,
	  Array.init nargs
	    (fun i -> mkRel (nargs - i )))
  in
  it_mkLambda_or_LetIn
    ~init: 
    (it_mkLambda_or_LetIn ~init 
       (List.map change_sort_in_predicate princ_info.predicates)
    )
    princ_info.params
    

let generate_functional_principle 
    interactive_proof
    old_princ_type sorts new_princ_name funs i proof_tac 
    = 
  let f = funs.(i) in 
  let type_sort = Termops.new_sort_in_family InType in 
  let new_sorts = 
    match sorts with 
      | None -> Array.make (Array.length funs) (type_sort)
      | Some a -> a
  in
  (* First we get the type of the old graph principle *)
  let mutr_nparams = (compute_elim_sig old_princ_type).nparams in 
  (* First we get the type of the old graph principle *)
   let new_principle_type =
    compute_new_princ_type_from_rel
      (Array.map mkConst funs)
      new_sorts
      old_princ_type
  in
(*   let tim2 = Sys.time ()  in *)
(*   Pp.msgnl (str ("Time to compute type: ") ++ str (string_of_float (tim2 -. tim1))) ; *)
(*   msgnl (str "new principle type :"++ pr_lconstr  new_principle_type); *)
  let base_new_princ_name,new_princ_name =
    match new_princ_name with
      | Some (id) -> id,id
      | None ->
	  let id_of_f = id_of_label (con_label f) in
	  id_of_f,Indrec.make_elimination_ident id_of_f (family_of_sort type_sort)
  in
  let hook _ _  =
    if sorts = None 
    then
(*     let id_of_f = id_of_label (con_label f) in *)
    let register_with_sort fam_sort =
      let s = Termops.new_sort_in_family  fam_sort in
      let name = Indrec.make_elimination_ident base_new_princ_name fam_sort in
      let value =
	change_property_sort s new_principle_type new_princ_name
      in
(*       Pp.msgnl (str "new principle := " ++ Printer.pr_lconstr value); *)
      let ce =
	{ const_entry_body = value;
	  const_entry_type = None;
	  const_entry_opaque = false;
	  const_entry_boxed = Options.boxed_definitions()
	}
      in
      ignore(
	Declare.declare_constant
	  name
	  (Entries.DefinitionEntry ce,
	   Decl_kinds.IsDefinition (Decl_kinds.Scheme)
	  )
      )
    in
    register_with_sort InSet;
    register_with_sort InProp
  in
  begin
    Command.start_proof
      new_princ_name
      (Decl_kinds.Global,(Decl_kinds.Proof Decl_kinds.Theorem))
      new_principle_type
      hook
    ;
    try
(*       let tim1 = Sys.time ()  in *)
      Pfedit.by  (proof_tac (Array.map mkConst funs) mutr_nparams);
(*       let tim2 = Sys.time ()  in *)
(* Pp.msgnl (str ("Time to compute proof: ") ++ str (string_of_float (tim2 -. tim1))); *)
      let do_save =  Tacinterp.get_debug () = Tactic_debug.DebugOff && not interactive_proof in 
      if do_save then Options.silently Command.save_named false


(*       let tim3 = Sys.time ()  in *)
(* Pp.msgnl (str ("Time to save proof: ") ++ str (string_of_float (tim3 -. tim2))); *)

    with
      | e ->
	  msg_warning
	    (
	      Cerrors.explain_exn e
	    );
	  if Tacinterp.get_debug () = Tactic_debug.DebugOff
	  then begin Vernacentries.interp (Vernacexpr.VernacAbort None);raise e end
  end






let get_funs_constant mp dp = 
  let rec get_funs_constant const e : (Names.constant*int) array = 
    match kind_of_term (snd (decompose_lam e)) with 
      | Fix((_,(na,_,_))) -> 
	  Array.mapi 
	    (fun i na -> 
	       match na with 
		 | Name id -> 
		     let const = make_con mp dp (label_of_id id) in 
		     const,i
		 | Anonymous -> 
		     anomaly "Anonymous fix" 
	    )
	    na
      | _ -> [|const,0|]
  in
  function const -> 
    let find_constant_body const = 
      match (Global.lookup_constant const ).const_body with
	| Some b ->
	    let body = force b in
	    let body = Tacred.cbv_norm_flags
	      (Closure.RedFlags.mkflags [Closure.RedFlags.fZETA])
	      (Global.env ())
	      (Evd.empty)
	      body
	    in
	    body
	| None -> error ( "Cannot define a principle over an axiom ")
    in
    let f = find_constant_body const in
    let l_const = get_funs_constant const f in 
    (* 
       We need to check that all the functions found are in the same block 
       to prevent Reset stange thing
    *) 
    let l_bodies = List.map find_constant_body (Array.to_list (Array.map fst l_const)) in 
    let l_params,l_fixes = List.split (List.map decompose_lam l_bodies) in 
    (* all the paremeter must be equal*) 
    let _check_params = 
      let first_params = List.hd l_params  in 
      List.iter 
	(fun params -> 
	   if not ((=) first_params params) 
	   then error "Not a mutal recursive block"
	)
	l_params
    in
    (* The bodies has to be very similar *) 
    let _check_bodies = 
      let extract_info body = 
	match kind_of_term body with 
	  | Fix((idxs,_),(na,ta,ca)) -> (idxs,na,ta,ca)
	  | _ -> error "Not a mutal recursive block"
      in
      let first_infos = extract_info (List.hd l_bodies) in 
      let check body  = (* Hope this is correct *)
	if not (first_infos = (extract_info body)) 
	then  error "Not a mutal recursive block"
      in 
      List.iter check l_bodies
    in
    l_const
	
let make_scheme fas = 
  let env = Global.env () 
  and sigma = Evd.empty in
  let id_to_constr id = 
    Tacinterp.constr_of_id env  id
  in 
  let funs = List.map (fun (_,f,_) -> id_to_constr f) fas in 
  let first_fun = destConst (List.hd funs) in 
  let funs_mp,funs_dp,first_fun_id = Names.repr_con first_fun in 
  let first_fun_rel_id = mk_rel_id (id_of_label first_fun_id) in 
  let first_fun_kn = 
    (* Fixme: take into accour funs_mp and funs_dp *)
    fst (destInd (id_to_constr first_fun_rel_id))
  in
  let this_block_funs_indexes = get_funs_constant funs_mp funs_dp first_fun in
  let this_block_funs = Array.map fst this_block_funs_indexes in 
  let prop_sort = InProp in
  let funs_indexes = 
    let this_block_funs_indexes = Array.to_list this_block_funs_indexes in 
    List.map
      (function const -> List.assoc (destConst const) this_block_funs_indexes)
      funs
  in
  let ind_list = 
    List.map 
      (fun (idx) -> 
	 let ind = first_fun_kn,idx in 
	 let (mib,mip) = Global.lookup_inductive ind in
	 ind,mib,mip,true,prop_sort
      )
      funs_indexes
  in
  let l_schemes = Indrec.build_mutual_indrec env sigma ind_list in 
  let i = ref (-1) in
  let sorts = 
    List.rev_map (fun (_,_,x) -> 
		Termops.new_sort_in_family (Pretyping.interp_elimination_sort x)
	     ) 
      fas 
  in
  let _ = List.map2
    (fun princ_name scheme_type -> 
       incr i;
       observe (str "Generating " ++ Ppconstr.pr_id princ_name ++str " with " ++
	       Printer.pr_lconstr scheme_type);
       generate_functional_principle 
	 false
	 (Typing.type_of env sigma scheme_type)
	 (Some (Array.of_list sorts))
	 (Some princ_name)
	 this_block_funs
	 !i 
	 (prove_princ_for_struct false !i (Array.of_list (List.map destConst funs)))
    )
    (List.map (fun (x,_,_) -> x) fas) 
    l_schemes 
  in
  ()
