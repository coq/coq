open Printer
open Util
open Term
open Termops
open Namegen
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


let pr_elim_scheme el =
  let env = Global.env () in
  let msg = str "params := " ++ Printer.pr_rel_context env el.params in
  let env = Environ.push_rel_context el.params env in
  let msg = msg ++ fnl () ++ str "predicates := "++ Printer.pr_rel_context env el.predicates in
  let env = Environ.push_rel_context el.predicates env in
  let msg = msg ++ fnl () ++ str "branches := " ++ Printer.pr_rel_context env el.branches in
  let env = Environ.push_rel_context el.branches env in
  let msg = msg ++ fnl () ++ str "args := " ++ Printer.pr_rel_context env el.args in
  let env = Environ.push_rel_context el.args env in
  msg ++ fnl () ++ str "concl := " ++ pr_lconstr_env env el.concl


let observe s =
  if do_observe ()
  then Pp.msgnl s


let pr_elim_scheme el =
  let env = Global.env () in
  let msg = str "params := " ++ Printer.pr_rel_context env el.params in
  let env = Environ.push_rel_context el.params env in
  let msg = msg ++ fnl () ++ str "predicates := "++ Printer.pr_rel_context env el.predicates in
  let env = Environ.push_rel_context el.predicates env in
  let msg = msg ++ fnl () ++ str "branches := " ++ Printer.pr_rel_context env el.branches in
  let env = Environ.push_rel_context el.branches env in
  let msg = msg ++ fnl () ++ str "args := " ++ Printer.pr_rel_context env el.args in
  let env = Environ.push_rel_context el.args env in
  msg ++ fnl () ++ str "concl := " ++ pr_lconstr_env env el.concl


let observe s =
  if do_observe ()
  then Pp.msgnl s

(*
   Transform an inductive induction principle into
   a functional one
*)
let compute_new_princ_type_from_rel rel_to_fun sorts princ_type =
  let princ_type_info = compute_elim_sig princ_type in
  let env = Global.env () in
  let env_with_params = Environ.push_rel_context princ_type_info.params env in
  let tbl = Hashtbl.create 792 in
  let rec change_predicates_names (avoid:identifier list) (predicates:rel_context)  : rel_context =
    match predicates with
    | [] -> []
    |(Name x,v,t)::predicates ->
       let id =  Namegen.next_ident_away x avoid in
       Hashtbl.add tbl id x;
       (Name id,v,t)::(change_predicates_names (id::avoid) predicates)
    | (Anonymous,_,_)::_ -> anomaly "Anonymous property binder "
  in
  let avoid = (Termops.ids_of_context env_with_params ) in
  let princ_type_info =
    { princ_type_info with
	predicates = change_predicates_names avoid princ_type_info.predicates
    }
  in
(*   observe (str "starting princ_type := " ++ pr_lconstr_env env princ_type); *)
(*   observe (str "princ_infos : " ++ pr_elim_scheme princ_type_info); *)
  let change_predicate_sort i (x,_,t) =
    let new_sort = sorts.(i) in
    let args,_ = decompose_prod t in
    let real_args =
      if princ_type_info.indarg_in_concl
      then List.tl args
      else args
    in
    Nameops.out_name x,None,compose_prod real_args (mkSort new_sort)
  in
  let new_predicates =
    list_map_i
      change_predicate_sort
      0
      princ_type_info.predicates
  in
  let env_with_params_and_predicates = List.fold_right Environ.push_named new_predicates env_with_params in
  let rel_as_kn =
    fst (match princ_type_info.indref with
	   | Some (Libnames.IndRef ind) -> ind
	   | _ -> error "Not a valid predicate"
	)
  in
  let ptes_vars = List.map (fun (id,_,_) -> id) new_predicates in
  let is_pte =
    let set = List.fold_right Idset.add ptes_vars Idset.empty in
    fun t ->
      match kind_of_term t with
	| Var id -> Idset.mem id set
	| _ -> false
  in
  let pre_princ =
    it_mkProd_or_LetIn
      ~init:
      (it_mkProd_or_LetIn
	 ~init:(Option.fold_right
			   mkProd_or_LetIn
			   princ_type_info.indarg
			   princ_type_info.concl
			)
	 princ_type_info.args
      )
      princ_type_info.branches
  in
  let pre_princ = substl (List.map mkVar ptes_vars) pre_princ in
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
	    compute_new_princ_type_for_binder  remove mkLambda env x t b
	| Ind _ | Construct _ when is_dom pre_princ -> raise Toberemoved
	| App(f,args) when is_dom f ->
	    let var_to_be_removed = destRel (array_last args) in
	    let num = get_fun_num f in
	    raise (Toberemoved_with_rel (var_to_be_removed,mk_replacement pre_princ num args))
	| App(f,args) ->
	    let args =
	      if is_pte f && remove
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
(*     let _ = match kind_of_term pre_princ with *)
(* 	| Prod _ -> *)
(* 	    observe(str "compute_new_princ_type for "++ *)
(* 	      pr_lconstr_env env pre_princ ++ *)
(* 	      str" is "++ *)
(* 	      pr_lconstr_env env new_princ_type ++ fnl ()) *)
(* 	| _ -> () in *)
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
(* 	    observe (str "Decl of "++Ppconstr.pr_name x ++ str " is removed "); *)
	    let new_b,binders_to_remove_from_b = compute_new_princ_type remove env (substnl [dummy_var] 1 b)  in
	    new_b, List.map pop binders_to_remove_from_b
	| Toberemoved_with_rel (n,c) ->
(* 	    observe (str "Decl of "++Ppconstr.pr_name x ++ str " is removed "); *)
	    let new_b,binders_to_remove_from_b = compute_new_princ_type remove env (substnl [c] n b)  in
	    new_b, list_add_set_eq eq_constr (mkRel n) (List.map pop binders_to_remove_from_b)
    end
  and compute_new_princ_type_for_letin remove env x v t b =
    begin
      try
	let new_t,binders_to_remove_from_t = compute_new_princ_type remove env t in
	let new_v,binders_to_remove_from_v = compute_new_princ_type remove env v in
	let new_x : name = get_name (ids_of_context env) x in
	let new_env = Environ.push_rel (x,Some v,t) env in
	let new_b,binders_to_remove_from_b = compute_new_princ_type remove new_env b in
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
(* 	    observe (str "Decl of "++Ppconstr.pr_name x ++ str " is removed "); *)
	    let new_b,binders_to_remove_from_b = compute_new_princ_type remove env (substnl [dummy_var] 1 b)  in
	    new_b, List.map pop binders_to_remove_from_b
	| Toberemoved_with_rel (n,c) ->
(* 	    observe (str "Decl of "++Ppconstr.pr_name x ++ str " is removed "); *)
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
    compute_new_princ_type princ_type_info.indarg_in_concl env_with_params_and_predicates pre_princ
  in
  let pre_res =
    replace_vars
      (list_map_i (fun i id -> (id, mkRel i)) 1 ptes_vars)
      (lift (List.length ptes_vars) pre_res)
  in
  it_mkProd_or_LetIn
    ~init:(it_mkProd_or_LetIn
	     ~init:pre_res (List.map (fun (id,t,b) -> Name(Hashtbl.find tbl id), t,b)
			      new_predicates)
	  )
    princ_type_info.params



let change_property_sort toSort princ princName =
  let princ_info = compute_elim_sig princ in
  let change_sort_in_predicate (x,v,t) =
    (x,None,
     let args,_ = decompose_prod t in
     compose_prod args (mkSort toSort)
    )
  in
  let princName_as_constr = Constrintern.global_reference princName in
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

(* let qed () = save_named true  *)
let defined () =
  try
    Lemmas.save_named false
  with
    | UserError("extract_proof",msg) ->
	Util.errorlabstrm
	  "defined"
	  ((try
	      str "On goal : " ++ fnl () ++  pr_open_subgoals () ++ fnl ()
	    with _ -> mt ()
	   ) ++msg)
    | e -> raise e



let build_functional_principle interactive_proof old_princ_type sorts funs i proof_tac hook =
  (* First we get the type of the old graph principle *)
  let mutr_nparams = (compute_elim_sig old_princ_type).nparams in
  (*   let time1 = System.get_time ()  in *)
  let new_principle_type =
    compute_new_princ_type_from_rel
      (Array.map mkConst funs)
      sorts
      old_princ_type
  in
  (*    let time2 = System.get_time ()  in *)
  (*    Pp.msgnl (str "computing principle type := " ++ System.fmt_time_difference time1 time2); *)
     observe (str "new_principle_type : " ++ pr_lconstr new_principle_type);
  let new_princ_name =
    next_ident_away_in_goal (id_of_string "___________princ_________") []
  in
  begin
    Lemmas.start_proof
      new_princ_name
      (Decl_kinds.Global,(Decl_kinds.Proof Decl_kinds.Theorem))
      new_principle_type
      (hook new_principle_type)
    ;
    (*       let _tim1 = System.get_time ()  in *)
    Pfedit.by  (proof_tac (Array.map mkConst funs) mutr_nparams);
    (*       let _tim2 =  System.get_time ()  in *)
    (* 	begin *)
    (* 	  let dur1 = System.time_difference tim1 tim2 in *)
    (* 	  Pp.msgnl (str ("Time to compute proof: ") ++ str (string_of_float dur1)); *)
    (* 	end; *)
    get_proof_clean true
  end



let generate_functional_principle
    interactive_proof
    old_princ_type sorts new_princ_name funs i proof_tac
    =
  try

  let f = funs.(i) in
  let type_sort = Termops.new_sort_in_family InType in
  let new_sorts =
    match sorts with
      | None -> Array.make (Array.length funs) (type_sort)
      | Some a -> a
  in
  let base_new_princ_name,new_princ_name =
    match new_princ_name with
      | Some (id) -> id,id
      | None ->
	  let id_of_f = id_of_label (con_label f) in
	  id_of_f,Indrec.make_elimination_ident id_of_f (family_of_sort type_sort)
  in
  let names = ref [new_princ_name] in
  let hook new_principle_type _ _  =
    if sorts = None
    then
      (*     let id_of_f = id_of_label (con_label f) in *)
      let register_with_sort fam_sort =
	let s = Termops.new_sort_in_family fam_sort in
	let name = Indrec.make_elimination_ident base_new_princ_name fam_sort in
	let value = change_property_sort s new_principle_type new_princ_name in
	(*       Pp.msgnl (str "new principle := " ++ pr_lconstr value); *)
	let ce =
	  { const_entry_body = value;
	    const_entry_type = None;
	    const_entry_opaque = false;
	    const_entry_boxed = Flags.boxed_definitions();
	    const_entry_inline_code = false
	  }
	in
	ignore(
	  Declare.declare_constant
	    name
	    (Entries.DefinitionEntry ce,
	     Decl_kinds.IsDefinition (Decl_kinds.Scheme)
	    )
	);
	Flags.if_verbose
	  (fun id -> Pp.msgnl (Ppconstr.pr_id id ++ str " is defined"))
	  name;
	names := name :: !names
      in
      register_with_sort InProp;
      register_with_sort InSet
  in
  let (id,(entry,g_kind,hook)) =
    build_functional_principle interactive_proof old_princ_type new_sorts funs i proof_tac hook
  in
  (* Pr  1278 :
     Don't forget to close the goal if an error is raised !!!!
  *)
  save false new_princ_name entry g_kind hook
  with e ->
    begin
      begin
	try
	  let id = Pfedit.get_current_proof_name () in
	  let s = string_of_id id in
	  let n = String.length "___________princ_________" in
	  if String.length s >= n
	  then if String.sub s 0 n = "___________princ_________"
	  then Pfedit.delete_current_proof ()
	  else ()
	  else ()
	with _ -> ()
      end;
      raise (Defining_principle e)
    end
(*   defined  () *)


exception Not_Rec

let get_funs_constant mp dp =
  let rec get_funs_constant const e : (Names.constant*int) array =
    match kind_of_term ((strip_lam e)) with
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
	| Def b | Opaque (Some b) ->
	    let body = force b in
	    let body = Tacred.cbv_norm_flags
	      (Closure.RedFlags.mkflags [Closure.RedFlags.fZETA])
	      (Global.env ())
	      (Evd.empty)
	      body
	    in
	    body
	| Opaque None -> error ( "Cannot define a principle over an axiom ")
	| Primitive _ -> error ( "Cannot define a principle over an primitive ")
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
exception Found_type of int

let make_scheme (fas : (constant*Rawterm.rawsort) list) : Entries.definition_entry list =
  let env = Global.env ()
  and sigma = Evd.empty in
  let funs = List.map fst fas in
  let first_fun = List.hd funs in


  let funs_mp,funs_dp,_ = Names.repr_con first_fun in
  let first_fun_kn =
    try
      fst (find_Function_infos  first_fun).graph_ind
    with Not_found -> raise No_graph_found
  in
  let this_block_funs_indexes = get_funs_constant funs_mp funs_dp first_fun in
  let this_block_funs = Array.map fst this_block_funs_indexes in
  let prop_sort = InProp in
  let funs_indexes =
    let this_block_funs_indexes = Array.to_list this_block_funs_indexes in
    List.map
      (function const -> List.assoc const this_block_funs_indexes)
      funs
  in
  let ind_list =
    List.map
      (fun (idx) ->
	 let ind = first_fun_kn,idx in
	 ind,true,prop_sort
      )
      funs_indexes
  in
  let l_schemes =
    List.map
      (Typing.type_of env sigma)
      (Indrec.build_mutual_induction_scheme env sigma ind_list)
  in
  let i = ref (-1) in
  let sorts =
    List.rev_map (fun (_,x) ->
		Termops.new_sort_in_family (Pretyping.interp_elimination_sort x)
	     )
      fas
  in
  (* We create the first priciple by tactic *)
  let first_type,other_princ_types =
    match l_schemes with
	s::l_schemes -> s,l_schemes
      | _ -> anomaly ""
  in
  let (_,(const,_,_)) =
    try
      build_functional_principle false
	first_type
	(Array.of_list sorts)
	this_block_funs
	0
	(prove_princ_for_struct false 0 (Array.of_list funs))
	(fun _ _ _ -> ())
  with e ->
    begin
      begin
	try
	  let id = Pfedit.get_current_proof_name () in
	  let s = string_of_id id in
	  let n = String.length "___________princ_________" in
	  if String.length s >= n
	  then if String.sub s 0 n = "___________princ_________"
	  then Pfedit.delete_current_proof ()
	  else ()
	  else ()
	with _ -> ()
      end;
      raise (Defining_principle e)
    end

  in
  incr i;
  let opacity =
    let finfos = find_Function_infos this_block_funs.(0) in
    try
      let equation =  Option.get finfos.equation_lemma in
      match (Global.lookup_constant equation).const_body with
      | Opaque _ -> true
      | _ -> false
    with Option.IsNone -> (* non recursive definition *)
      false
  in
  let const = {const with const_entry_opaque = opacity } in
  (* The others are just deduced *)
  if other_princ_types = []
  then
    [const]
  else
    let other_fun_princ_types =
      let funs = Array.map mkConst this_block_funs in
      let sorts = Array.of_list sorts in
      List.map (compute_new_princ_type_from_rel funs sorts) other_princ_types
    in
    let first_princ_body,first_princ_type = const.Entries.const_entry_body, const.Entries.const_entry_type in
    let ctxt,fix = decompose_lam_assum first_princ_body in (* the principle has for forall ...., fix .*)
    let (idxs,_),(_,ta,_ as decl) = destFix fix in
    let other_result =
      List.map (* we can now compute the other principles *)
	(fun scheme_type ->
	   incr i;
	   observe (Printer.pr_lconstr scheme_type);
	   let type_concl = (strip_prod_assum scheme_type) in
	   let applied_f = List.hd (List.rev (snd (decompose_app type_concl))) in
	   let f = fst (decompose_app applied_f) in
	   try (* we search the number of the function in the fix block (name of the function) *)
	     Array.iteri
	     (fun j t ->
		let t =  (strip_prod_assum t) in
		let applied_g = List.hd (List.rev (snd (decompose_app t))) in
		let g = fst (decompose_app applied_g) in
		if eq_constr f g
		then raise (Found_type j);
		observe (Printer.pr_lconstr f ++ str " <> " ++
			   Printer.pr_lconstr g)

	     )
	     ta;
	   (* If we reach this point, the two principle are not mutually recursive
	      We fall back to the previous method
	   *)
	     let (_,(const,_,_)) =
	       build_functional_principle
		 false
		 (List.nth other_princ_types (!i - 1))
		 (Array.of_list sorts)
		 this_block_funs
		 !i
		 (prove_princ_for_struct false !i (Array.of_list funs))
		 (fun _ _ _ -> ())
	     in
	     const
	 with Found_type i ->
	   let princ_body =
	     Termops.it_mkLambda_or_LetIn ~init:(mkFix((idxs,i),decl)) ctxt
	   in
	   {const with
	      Entries.const_entry_body = princ_body;
	      Entries.const_entry_type = Some scheme_type
	   }
      )
      other_fun_princ_types
    in
    const::other_result


let build_scheme fas =
  Dumpglob.pause ();
  let bodies_types =
    make_scheme
      (List.map
	 (fun (_,f,sort) ->
	    let f_as_constant =
	      try
		match Nametab.global f with
		  | Libnames.ConstRef c -> c
		  | _ -> Util.error "Functional Scheme can only be used with functions"
	      with Not_found ->
	      	Util.error ("Cannot find "^ Libnames.string_of_reference f)
	    in
	    (f_as_constant,sort)
	 )
	 fas
      )
  in
  List.iter2
    (fun (princ_id,_,_) def_entry ->
       ignore
	 (Declare.declare_constant
	    princ_id
	    (Entries.DefinitionEntry def_entry,Decl_kinds.IsProof Decl_kinds.Theorem));
       Flags.if_verbose
	 (fun id -> Pp.msgnl (Ppconstr.pr_id id ++ str " is defined")) princ_id
    )
    fas
    bodies_types;
    Dumpglob.continue ()



let build_case_scheme fa =
  let env = Global.env ()
  and sigma = Evd.empty in
(*   let id_to_constr id =  *)
(*     Constrintern.global_reference  id *)
(*   in  *)
  let funs =  (fun (_,f,_) ->
		 try Libnames.constr_of_global (Nametab.global f)
		 with Not_found ->
		   Util.error ("Cannot find "^ Libnames.string_of_reference f)) fa in
  let first_fun = destConst  funs in

  let funs_mp,funs_dp,_ = Names.repr_con first_fun in
  let first_fun_kn = try fst (find_Function_infos  first_fun).graph_ind with Not_found -> raise No_graph_found in



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
  let scheme_type =  (Typing.type_of env sigma ) ((fun (ind,sf) -> Indrec.build_case_analysis_scheme_default env sigma ind sf)  ind_fun) in
  let sorts =
    (fun (_,_,x) ->
       Termops.new_sort_in_family (Pretyping.interp_elimination_sort x)
    )
      fa
  in
  let princ_name =  (fun (x,_,_) -> x) fa in
  let _ =
  (*  Pp.msgnl (str "Generating " ++ Ppconstr.pr_id princ_name ++str " with " ++
	       pr_lconstr scheme_type ++ str " and " ++ (fun a -> prlist_with_sep spc (fun c -> pr_lconstr (mkConst c)) (Array.to_list a)) this_block_funs
	    );
  *)
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
