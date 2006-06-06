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
open Functional_principles_proofs

exception Toberemoved_with_rel of int*constr
exception Toberemoved





(* 
   Transform an inductive induction principle into 
   a functional one
*)  
let compute_new_princ_type_from_rel rel_to_fun sorts princ_type =
  let princ_type_info = compute_elim_sig princ_type in 
  let env = Global.env () in 
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
  let mk_replacement c i args =
    let res = mkApp(rel_to_fun.(i),Array.map pop (array_get_start args)) in 
(*     observe (str "replacing " ++ pr_lconstr c ++ str " by "  ++ pr_lconstr res); *)
    res
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
	    raise (Toberemoved_with_rel (var_to_be_removed,mk_replacement pre_princ num args))
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
	    applist(new_f, new_args),
	    list_union_eq eq_constr binders_to_remove_from_f binders_to_remove
	| LetIn(x,v,t,b) ->
	    compute_new_princ_type_for_letin remove env x v t b
	| _ -> pre_princ,[]
    in
(*     observennl ( *)
(*       match kind_of_term pre_princ with  *)
(* 	| Prod _ ->  *)
(* 	    str "compute_new_princ_type for "++ *)
(* 	      pr_lconstr_env env pre_princ ++ *)
(* 	      str" is "++ *)
(* 	      pr_lconstr_env env new_princ_type ++ fnl () *)
(* 	| _ -> str "" *)
(*     ); *)
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
(*   observe (str "Computing new principe from " ++ pr_lconstr_env  env_with_params_and_predicates pre_princ); *)
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
    

let pp_dur time time' = 
  str (string_of_float (System.time_difference time time'))

(* End of things to be removed latter : just here to compare 
   saving proof with and without  normalizing the proof 
*)

let qed () = Command.save_named true 
let defined () = Command.save_named false
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
(*    observe (str "new_principle_type : " ++ pr_lconstr new_principle_type); *)
  let base_new_princ_name,new_princ_name =
    match new_princ_name with
      | Some (id) -> id,id
      | None ->
	  let id_of_f = id_of_label (con_label f) in
	  id_of_f,Indrec.make_elimination_ident id_of_f (family_of_sort type_sort)
  in
  let names = ref [new_princ_name] in 
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
(*       Pp.msgnl (str "new principle := " ++ pr_lconstr value); *)
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
      );
      names := name :: !names
    in
    register_with_sort InProp;
    register_with_sort InSet
  in
  begin
    Command.start_proof
      new_princ_name
      (Decl_kinds.Global,(Decl_kinds.Proof Decl_kinds.Theorem))
      new_principle_type
      hook
    ;
    try
      let _tim1 = System.get_time ()  in
      Pfedit.by  (proof_tac (Array.map mkConst funs) mutr_nparams);
      let _tim2 =  System.get_time ()  in
(* 	begin *)
(* 	  let dur1 = System.time_difference tim1 tim2 in *)
(* 	  Pp.msgnl (str ("Time to compute proof: ") ++ str (string_of_float dur1)); *)
(* 	end; *)
      let do_save =  not (do_observe ()) && not interactive_proof in 
      let _ = 
	try 
(* 	  Vernacentries.show_script (); *)
	  Options.silently defined ();
	  let _dur2 = System.time_difference _tim2 (System.get_time ()) in
(* 	  Pp.msgnl (str ("Time to check proof: ") ++ str (string_of_float dur2)); *)
	  Options.if_verbose 
	    (fun () -> 
	       Pp.msgnl (
		 prlist_with_sep
		   (fun () -> str" is defined " ++ fnl ()) 
		   Ppconstr.pr_id
		   (List.rev !names) ++ str" is defined " 
	       )
	    ) 
	       ()
	with e when do_save -> 
	  msg_warning
	    (
	      Cerrors.explain_exn e
	    );
	  if not (do_observe ())
	  then begin Vernacentries.interp (Vernacexpr.VernacAbort None);raise e end
      in
      ()

(*       let tim3 = Sys.time ()  in *)
(* Pp.msgnl (str ("Time to save proof: ") ++ str (string_of_float (tim3 -. tim2))); *)

    with
      | e ->
	  msg_warning
	    (
	      Cerrors.explain_exn e
	    );
	  if not ( do_observe ())
	  then begin Vernacentries.interp (Vernacexpr.VernacAbort None);raise e end
  end




exception Not_Rec

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
      try 
	let extract_info is_first body = 
	  match kind_of_term body with 
	    | Fix((idxs,_),(na,ta,ca)) -> (idxs,na,ta,ca)
	    | _ -> 
		if is_first && (List.length l_bodies = 1) 
		then raise Not_Rec
		else error "Not a mutal recursive block"
	in
	let first_infos = extract_info true (List.hd l_bodies) in 
	let check body  = (* Hope this is correct *)
	  if not (first_infos = (extract_info false body)) 
	  then  error "Not a mutal recursive block"
	in 
	List.iter check l_bodies
      with Not_Rec -> ()
    in
    l_const

exception No_graph_found 
	
let make_scheme fas = 
  let env = Global.env () 
  and sigma = Evd.empty in
  let id_to_constr id = 
      Tacinterp.constr_of_id env  id
  in 
  let funs = 
    List.map
      (fun (_,f,_) -> 
	 try id_to_constr f     
	 with Not_found -> 
	   Util.error ("Cannot find "^ string_of_id f)
      )
      fas
  in 
  let first_fun = destConst (List.hd funs) in 
  let funs_mp,funs_dp,first_fun_id = Names.repr_con first_fun in 
  let first_fun_rel_id = mk_rel_id (id_of_label first_fun_id) in 
  let first_fun_kn = 
    try 
    (* Fixme: take into account funs_mp and funs_dp *)
    fst (destInd (id_to_constr first_fun_rel_id))
    with Not_found -> raise No_graph_found
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
  let l_schemes = List.map (Typing.type_of env sigma ) (Indrec.build_mutual_indrec env sigma ind_list) in 
  let i = ref (-1) in
  let sorts = 
    List.rev_map (fun (_,_,x) -> 
		Termops.new_sort_in_family (Pretyping.interp_elimination_sort x)
	     ) 
      fas 
  in
  let princ_names = List.map (fun (x,_,_) -> x) fas in 
  let _ = List.map2
    (fun princ_name scheme_type -> 
       incr i;
(*        observe (str "Generating " ++ Ppconstr.pr_id princ_name ++str " with " ++ *)
(* 	       pr_lconstr scheme_type ++ str " and " ++ (fun a -> prlist_with_sep spc (fun c -> pr_lconstr (mkConst c)) (Array.to_list a)) this_block_funs *)
(* 	       ); *)
       generate_functional_principle
	 false
	 scheme_type
	 (Some (Array.of_list sorts))
	 (Some princ_name)
	 this_block_funs
	 !i
	 (prove_princ_for_struct false !i (Array.of_list (List.map destConst funs)))
    )
    princ_names
    l_schemes 
  in
  ()

let make_case_scheme fa = 
  let env = Global.env () 
  and sigma = Evd.empty in
  let id_to_constr id = 
    Tacinterp.constr_of_id env  id
  in 
  let funs =  (fun (_,f,_) -> id_to_constr f) fa in 
  let first_fun = destConst  funs in 
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
    List.assoc (destConst funs) this_block_funs_indexes
  in
  let ind_fun = 
	 let ind = first_fun_kn,funs_indexes in 
	 ind,prop_sort
  in
  let scheme_type =  (Typing.type_of env sigma ) ((fun (ind,sf) -> Indrec.make_case_gen env sigma ind sf)  ind_fun) in 
  let sorts =
    (fun (_,_,x) ->
       Termops.new_sort_in_family (Pretyping.interp_elimination_sort x)
    )
      fa
  in
  let princ_name =  (fun (x,_,_) -> x) fa in
  let _ = 
(*     observe (str "Generating " ++ Ppconstr.pr_id princ_name ++str " with " ++ *)
(* 	       pr_lconstr scheme_type ++ str " and " ++ (fun a -> prlist_with_sep spc (fun c -> pr_lconstr (mkConst c)) (Array.to_list a)) this_block_funs *)
(* 	    ); *)
    generate_functional_principle
      false
      scheme_type
      (Some ([|sorts|]))
      (Some princ_name)
      this_block_funs
      0
      (prove_princ_for_struct false 0 [|destConst funs|])
  in
  ()
