open Printer
open CErrors
open Term
open Sorts
open Util
open Constr
open Vars
open Namegen
open Names
open Pp
open Entries
open Tactics
open Context.Rel.Declaration
open Indfun_common
open Functional_principles_proofs

module RelDecl = Context.Rel.Declaration

exception Toberemoved_with_rel of int*constr
exception Toberemoved

let observe s =
  if do_observe ()
  then Feedback.msg_debug s

let pop t = Vars.lift (-1) t

(*
   Transform an inductive induction principle into
   a functional one
*)
let compute_new_princ_type_from_rel rel_to_fun sorts princ_type =
  let princ_type = EConstr.of_constr princ_type in
  let princ_type_info = compute_elim_sig Evd.empty princ_type (** FIXME *) in
  let env = Global.env () in
  let env_with_params = EConstr.push_rel_context princ_type_info.params env in
  let tbl = Hashtbl.create 792 in
  let rec change_predicates_names (avoid:Id.t list) (predicates:EConstr.rel_context)  : EConstr.rel_context =
    match predicates with
    | [] -> []
    | decl :: predicates ->
       (match Context.Rel.Declaration.get_name decl with
	| Name x ->
	   let id = Namegen.next_ident_away x (Id.Set.of_list avoid) in
	   Hashtbl.add tbl id x;
	   RelDecl.set_name (Name id) decl :: change_predicates_names (id::avoid) predicates
	| Anonymous -> anomaly (Pp.str "Anonymous property binder."))
  in
  let avoid = (Termops.ids_of_context env_with_params ) in
  let princ_type_info =
    { princ_type_info with
	predicates = change_predicates_names avoid princ_type_info.predicates
    }
  in
(*   observe (str "starting princ_type := " ++ pr_lconstr_env env princ_type); *)
(*   observe (str "princ_infos : " ++ pr_elim_scheme princ_type_info); *)
  let change_predicate_sort i decl =
    let new_sort = sorts.(i) in
    let args,_ = decompose_prod (EConstr.Unsafe.to_constr (RelDecl.get_type decl)) in
    let real_args =
      if princ_type_info.indarg_in_concl
      then List.tl args
      else args
    in
    Context.Named.Declaration.LocalAssum (Nameops.Name.get_id (Context.Rel.Declaration.get_name decl),
                                          Term.compose_prod real_args (mkSort new_sort))
  in
  let new_predicates =
    List.map_i
      change_predicate_sort
      0
      princ_type_info.predicates
  in
  let env_with_params_and_predicates = List.fold_right Environ.push_named new_predicates env_with_params in
  let rel_as_kn =
    fst (match princ_type_info.indref with
	   | Some (Globnames.IndRef ind) -> ind
	   | _ -> user_err Pp.(str "Not a valid predicate")
	)
  in
  let ptes_vars = List.map Context.Named.Declaration.get_id new_predicates in
  let is_pte =
    let set = List.fold_right Id.Set.add ptes_vars Id.Set.empty in
    fun t ->
      match Constr.kind t with
	| Var id -> Id.Set.mem id set
	| _ -> false
  in
  let pre_princ =
    let open EConstr in
    it_mkProd_or_LetIn
      (it_mkProd_or_LetIn
	 (Option.fold_right
			   mkProd_or_LetIn
			   princ_type_info.indarg
			   princ_type_info.concl
			)
	 princ_type_info.args
      )
      princ_type_info.branches
  in
  let pre_princ = EConstr.Unsafe.to_constr pre_princ in
  let pre_princ = substl (List.map mkVar ptes_vars) pre_princ in
  let is_dom c =
    match Constr.kind c with
      | Ind((u,_),_) -> MutInd.equal u rel_as_kn
      | Construct(((u,_),_),_) -> MutInd.equal u rel_as_kn
      | _ -> false
  in
  let get_fun_num c =
    match Constr.kind c with
      | Ind((_,num),_) -> num
      | Construct(((_,num),_),_) -> num
      | _ -> assert false
  in
  let dummy_var = mkVar (Id.of_string "________") in
  let mk_replacement c i args =
    let res = mkApp(rel_to_fun.(i), Array.map pop (array_get_start args)) in
    observe (str "replacing " ++
             pr_lconstr_env env Evd.empty c ++ str " by "  ++
             pr_lconstr_env env Evd.empty res);
    res
  in
  let rec compute_new_princ_type remove env pre_princ : types*(constr list) =
    let (new_princ_type,_) as res =
      match Constr.kind pre_princ with
	| Rel n ->
	    begin
	      try match Environ.lookup_rel n env with
		| LocalAssum (_,t) | LocalDef (_,_,t) when is_dom t -> raise Toberemoved
		| _ -> pre_princ,[]
	      with Not_found -> assert false
	    end
	| Prod(x,t,b) ->
	    compute_new_princ_type_for_binder remove mkProd env x t b
	| Lambda(x,t,b) ->
	    compute_new_princ_type_for_binder  remove mkLambda env x t b
	| Ind _ | Construct _ when is_dom pre_princ -> raise Toberemoved
	| App(f,args) when is_dom f ->
	    let var_to_be_removed = destRel (Array.last args) in
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
	    applistc new_f new_args,
	    list_union_eq Constr.equal binders_to_remove_from_f binders_to_remove
	| LetIn(x,v,t,b) ->
	    compute_new_princ_type_for_letin remove env x v t b
	| _ -> pre_princ,[]
    in
(*     let _ = match Constr.kind pre_princ with *)
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
	let new_x : Name.t = get_name (Termops.ids_of_context env) x in
	let new_env = Environ.push_rel (LocalAssum (x,t)) env in
	let new_b,binders_to_remove_from_b = compute_new_princ_type remove new_env b in
	 if List.exists (Constr.equal (mkRel 1)) binders_to_remove_from_b
	 then (pop new_b), filter_map (Constr.equal (mkRel 1)) pop binders_to_remove_from_b
	 else
	   (
	     bind_fun(new_x,new_t,new_b),
	     list_union_eq
	       Constr.equal
	       binders_to_remove_from_t
	       (List.map pop binders_to_remove_from_b)
	   )

       with
	 | Toberemoved ->
(* 	    observe (str "Decl of "++Ppconstr.Name.print x ++ str " is removed "); *)
	    let new_b,binders_to_remove_from_b = compute_new_princ_type remove env (substnl [dummy_var] 1 b)  in
	    new_b, List.map pop binders_to_remove_from_b
	| Toberemoved_with_rel (n,c) ->
(* 	    observe (str "Decl of "++Ppconstr.Name.print x ++ str " is removed "); *)
	    let new_b,binders_to_remove_from_b = compute_new_princ_type remove env (substnl [c] n b)  in
	    new_b, list_add_set_eq Constr.equal (mkRel n) (List.map pop binders_to_remove_from_b)
    end
  and compute_new_princ_type_for_letin remove env x v t b =
    begin
      try
	let new_t,binders_to_remove_from_t = compute_new_princ_type remove env t in
	let new_v,binders_to_remove_from_v = compute_new_princ_type remove env v in
	let new_x : Name.t = get_name (Termops.ids_of_context env) x in
	let new_env = Environ.push_rel (LocalDef (x,v,t)) env in
	let new_b,binders_to_remove_from_b = compute_new_princ_type remove new_env b in
	if List.exists (Constr.equal (mkRel 1)) binders_to_remove_from_b
	then (pop new_b),filter_map (Constr.equal (mkRel 1)) pop binders_to_remove_from_b
	else
	  (
	    mkLetIn(new_x,new_v,new_t,new_b),
	    list_union_eq
	      Constr.equal
	      (list_union_eq Constr.equal binders_to_remove_from_t binders_to_remove_from_v)
	      (List.map pop binders_to_remove_from_b)
	  )

      with
	| Toberemoved ->
(* 	    observe (str "Decl of "++Ppconstr.Name.print x ++ str " is removed "); *)
	    let new_b,binders_to_remove_from_b = compute_new_princ_type remove env (substnl [dummy_var] 1 b)  in
	    new_b, List.map pop binders_to_remove_from_b
	| Toberemoved_with_rel (n,c) ->
(* 	    observe (str "Decl of "++Ppconstr.Name.print x ++ str " is removed "); *)
	    let new_b,binders_to_remove_from_b = compute_new_princ_type remove env (substnl [c] n b)  in
	    new_b, list_add_set_eq Constr.equal (mkRel n) (List.map pop binders_to_remove_from_b)
    end
  and  compute_new_princ_type_with_acc remove env e (c_acc,to_remove_acc)  =
    let new_e,to_remove_from_e = compute_new_princ_type remove env e
    in
    new_e::c_acc,list_union_eq Constr.equal to_remove_from_e to_remove_acc
  in
(*   observe (str "Computing new principe from " ++ pr_lconstr_env  env_with_params_and_predicates pre_princ); *)
  let pre_res,_ =
    compute_new_princ_type princ_type_info.indarg_in_concl env_with_params_and_predicates pre_princ
  in
  let pre_res =
    replace_vars
      (List.map_i (fun i id -> (id, mkRel i)) 1 ptes_vars)
      (lift (List.length ptes_vars) pre_res)
  in
  it_mkProd_or_LetIn
    (it_mkProd_or_LetIn
       pre_res (List.map (function Context.Named.Declaration.LocalAssum (id,b)   -> LocalAssum (Name (Hashtbl.find tbl id), b)
                                 | Context.Named.Declaration.LocalDef (id,t,b) -> LocalDef (Name (Hashtbl.find tbl id), t, b))
          	      new_predicates)
    )
    (List.map (fun d -> Termops.map_rel_decl EConstr.Unsafe.to_constr d) princ_type_info.params)



let change_property_sort evd toSort princ princName =
  let open Context.Rel.Declaration in
  let princ = EConstr.of_constr princ in
  let princ_info = compute_elim_sig evd princ in
  let change_sort_in_predicate decl =
    LocalAssum
    (get_name decl,
     let args,ty = decompose_prod (EConstr.Unsafe.to_constr (get_type decl)) in
     let s = destSort ty in
       Global.add_constraints (Univ.enforce_leq (univ_of_sort toSort) (univ_of_sort s) Univ.Constraint.empty);
       Term.compose_prod args (mkSort toSort)
    )
  in
  let evd,princName_as_constr =
    Evd.fresh_global
      (Global.env ()) evd (Constrintern.locate_reference (Libnames.qualid_of_ident princName)) in
  let init =
    let nargs =  (princ_info.nparams + (List.length  princ_info.predicates)) in
    mkApp(EConstr.Unsafe.to_constr princName_as_constr,
	  Array.init nargs
	    (fun i -> mkRel (nargs - i )))
  in
  evd,  it_mkLambda_or_LetIn
    (it_mkLambda_or_LetIn init
       (List.map change_sort_in_predicate princ_info.predicates)
    )
    (List.map (fun d -> Termops.map_rel_decl EConstr.Unsafe.to_constr d) princ_info.params)

let build_functional_principle (evd:Evd.evar_map ref) interactive_proof old_princ_type sorts funs i proof_tac hook =
  (* First we get the type of the old graph principle *)
  let mutr_nparams = (compute_elim_sig !evd (EConstr.of_constr old_princ_type)).nparams in
  (*   let time1 = System.get_time ()  in *)
  let new_principle_type =
    compute_new_princ_type_from_rel
      (Array.map mkConstU funs)
      sorts
      old_princ_type
  in
  (*    let time2 = System.get_time ()  in *)
  (*    Pp.msgnl (str "computing principle type := " ++ System.fmt_time_difference time1 time2); *)
  let new_princ_name =
    next_ident_away_in_goal (Id.of_string "___________princ_________") Id.Set.empty
  in
  let sigma, _ = Typing.type_of ~refresh:true (Global.env ()) !evd (EConstr.of_constr new_principle_type) in
  evd := sigma;
  let hook = Lemmas.mk_hook (hook new_principle_type) in
  begin
    Lemmas.start_proof
      new_princ_name
      (Decl_kinds.Global,Flags.is_universe_polymorphism (),(Decl_kinds.Proof Decl_kinds.Theorem))
      !evd
      (EConstr.of_constr new_principle_type)
      hook
  ;
    (*       let _tim1 = System.get_time ()  in *)
      let map (c, u) = EConstr.mkConstU (c, EConstr.EInstance.make u) in
      ignore (Pfedit.by  (Proofview.V82.tactic (proof_tac (Array.map map funs) mutr_nparams)));
    (*       let _tim2 =  System.get_time ()  in *)
    (* 	begin *)
    (* 	  let dur1 = System.time_difference tim1 tim2 in *)
    (* 	  Pp.msgnl (str ("Time to compute proof: ") ++ str (string_of_float dur1)); *)
    (* 	end; *)
    get_proof_clean true, CEphemeron.create hook
  end



let generate_functional_principle (evd: Evd.evar_map ref)
    interactive_proof
    old_princ_type sorts new_princ_name funs i proof_tac
    =
  try

  let f = funs.(i) in
  let type_sort = Evarutil.evd_comb1 Evd.fresh_sort_in_family evd InType in
  let new_sorts =
    match sorts with
      | None -> Array.make (Array.length funs) (type_sort)
      | Some a -> a
  in
  let base_new_princ_name,new_princ_name =
    match new_princ_name with
      | Some (id) -> id,id
      | None ->
	  let id_of_f = Label.to_id (Constant.label (fst f)) in
	  id_of_f,Indrec.make_elimination_ident id_of_f (Sorts.family type_sort)
  in
  let names = ref [new_princ_name] in
  let hook =
    fun  new_principle_type _ _  -> 
    if Option.is_empty sorts
    then
      (*     let id_of_f = Label.to_id (con_label f) in *)
      let register_with_sort fam_sort =
        let evd' = Evd.from_env (Global.env ()) in
        let evd',s = Evd.fresh_sort_in_family evd' fam_sort in
        let name = Indrec.make_elimination_ident base_new_princ_name fam_sort in
        let evd',value = change_property_sort evd' s new_principle_type new_princ_name in
        let evd' = fst (Typing.type_of ~refresh:true (Global.env ()) evd' (EConstr.of_constr value)) in
        (* Pp.msgnl (str "new principle := " ++ pr_lconstr value); *)
        let univs =
          let poly = Flags.is_universe_polymorphism () in
          Evd.const_univ_entry ~poly evd'
        in
        let ce = Declare.definition_entry ~univs value in
        ignore(
	  Declare.declare_constant
	    name
	    (DefinitionEntry ce,
	     Decl_kinds.IsDefinition (Decl_kinds.Scheme))
	);
	Declare.definition_message name;
	names := name :: !names
      in
      register_with_sort InProp;
      register_with_sort InSet
  in
  let ((id,(entry,g_kind)),hook) =
    build_functional_principle evd interactive_proof old_princ_type new_sorts funs i
    proof_tac hook
  in
  (* Pr  1278 :
     Don't forget to close the goal if an error is raised !!!!
  *)
  save false new_princ_name entry g_kind hook
  with e when CErrors.noncritical e ->
    begin
      begin
	try
	  let id = Proof_global.get_current_proof_name () in
	  let s = Id.to_string id in
	  let n = String.length "___________princ_________" in
	  if String.length s >= n
	  then if String.equal (String.sub s 0 n) "___________princ_________"
	  then Proof_global.discard_current ()
	  else ()
	  else ()
	with e when CErrors.noncritical e -> ()
      end;
      raise (Defining_principle e)
    end
(*   defined  () *)


exception Not_Rec

let get_funs_constant mp dp =
  let get_funs_constant const e : (Names.Constant.t*int) array =
    match Constr.kind ((strip_lam e)) with
      | Fix((_,(na,_,_))) ->
	  Array.mapi
	    (fun i na ->
	       match na with
		 | Name id ->
		     let const = Constant.make3 mp dp (Label.of_id id) in
		     const,i
		 | Anonymous ->
		     anomaly (Pp.str "Anonymous fix.")
	    )
	    na
      | _ -> [|const,0|]
  in
  function const ->
    let find_constant_body const =
      match Global.body_of_constant const with
	| Some (body, _) ->
	    let body = Tacred.cbv_norm_flags
	      (CClosure.RedFlags.mkflags [CClosure.RedFlags.fZETA])
	      (Global.env ())
	      (Evd.from_env (Global.env ()))
	      (EConstr.of_constr body)
	    in
	    let body = EConstr.Unsafe.to_constr body in
	    body
	| None -> user_err Pp.(str ( "Cannot define a principle over an axiom "))
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
	   if not (List.equal (fun (n1, c1) (n2, c2) -> Name.equal n1 n2 && Constr.equal c1 c2) first_params params)
	   then user_err Pp.(str "Not a mutal recursive block")
	)
	l_params
    in
    (* The bodies has to be very similar *)
    let _check_bodies =
      try
	let extract_info is_first body =
	  match Constr.kind body with
	    | Fix((idxs,_),(na,ta,ca)) -> (idxs,na,ta,ca)
	    | _ ->
		if is_first && Int.equal (List.length l_bodies) 1
		then raise Not_Rec
		else user_err Pp.(str "Not a mutal recursive block")
	in
	let first_infos = extract_info true (List.hd l_bodies) in
	let check body  = (* Hope this is correct *)
	  let eq_infos (ia1, na1, ta1, ca1) (ia2, na2, ta2, ca2) =
            Array.equal Int.equal ia1 ia2 && Array.equal Name.equal na1 na2 &&
            Array.equal Constr.equal ta1 ta2 && Array.equal Constr.equal ca1 ca2
	  in
	  if not (eq_infos first_infos (extract_info false body))
	  then  user_err Pp.(str "Not a mutal recursive block")
	in
	List.iter check l_bodies
      with Not_Rec -> ()
    in
    l_const

exception No_graph_found
exception Found_type of int

let make_scheme evd (fas : (pconstant*Sorts.family) list) : Safe_typing.private_constants definition_entry list =
  let env = Global.env () in
  let funs = List.map fst fas in
  let first_fun = List.hd funs in
  let funs_mp,funs_dp,_ = KerName.repr (Constant.canonical (fst first_fun)) in
  let first_fun_kn =
    try
      fst (find_Function_infos  (fst first_fun)).graph_ind
    with Not_found -> raise No_graph_found
  in
  let this_block_funs_indexes = get_funs_constant funs_mp funs_dp (fst first_fun) in
  let this_block_funs = Array.map (fun (c,_) -> (c,snd first_fun)) this_block_funs_indexes in
  let prop_sort = InProp in
  let funs_indexes =
    let this_block_funs_indexes = Array.to_list this_block_funs_indexes in
    List.map
      (function cst -> List.assoc_f Constant.equal (fst cst) this_block_funs_indexes)
      funs
  in
  let ind_list =
    List.map
      (fun (idx) ->
	 let ind = first_fun_kn,idx in
	   (ind,snd first_fun),true,prop_sort
      )
      funs_indexes
  in
  let sigma, schemes = 
    Indrec.build_mutual_induction_scheme env !evd ind_list
  in
  let _ = evd := sigma in 
  let l_schemes =
    List.map (EConstr.of_constr %> Typing.unsafe_type_of env sigma %> EConstr.Unsafe.to_constr) schemes
  in
  let i = ref (-1) in
  let sorts =
    List.rev_map (fun (_,x) ->
                  Evarutil.evd_comb1 Evd.fresh_sort_in_family evd x
             )
      fas
  in
  (* We create the first priciple by tactic *)
  let first_type,other_princ_types =
    match l_schemes with
	s::l_schemes -> s,l_schemes
      | _ -> anomaly (Pp.str "")
  in
  let ((_,(const,_)),_) =
    try
      build_functional_principle evd false
	first_type
	(Array.of_list sorts)
	this_block_funs
	0
	(prove_princ_for_struct evd false 0 (Array.of_list (List.map fst funs)))
	(fun _ _ _ -> ())
    with e when CErrors.noncritical e ->
       begin
	 begin
	   try
	     let id = Proof_global.get_current_proof_name () in
	     let s = Id.to_string id in
	     let n = String.length "___________princ_________" in
	     if String.length s >= n
	     then if String.equal (String.sub s 0 n) "___________princ_________"
		  then Proof_global.discard_current ()
		  else ()
	     else ()
	   with e when CErrors.noncritical e -> ()
	 end;
	 raise (Defining_principle e)
       end

  in
  incr i;
  let opacity =
    let finfos = find_Function_infos (fst first_fun) in
    try
      let equation =  Option.get finfos.equation_lemma in
      Declareops.is_opaque (Global.lookup_constant equation)
    with Option.IsNone -> (* non recursive definition *)
      false
  in
  let const = {const with const_entry_opaque = opacity } in
  (* The others are just deduced *)
  if List.is_empty other_princ_types
  then
    [const]
  else
    let other_fun_princ_types =
      let funs = Array.map mkConstU this_block_funs in
      let sorts = Array.of_list sorts in
      List.map (compute_new_princ_type_from_rel funs sorts) other_princ_types
    in
    let first_princ_body,first_princ_type = const.const_entry_body, const.const_entry_type in
    let ctxt,fix = decompose_lam_assum (fst(fst(Future.force first_princ_body))) in (* the principle has for forall ...., fix .*)
    let (idxs,_),(_,ta,_ as decl) = destFix fix in
    let other_result =
      List.map (* we can now compute the other principles *)
	(fun scheme_type ->
	   incr i;
           observe (Printer.pr_lconstr_env env sigma scheme_type);
	   let type_concl = (strip_prod_assum scheme_type) in
	   let applied_f = List.hd (List.rev (snd (decompose_app type_concl))) in
	   let f = fst (decompose_app applied_f) in
	   try (* we search the number of the function in the fix block (name of the function) *)
	     Array.iteri
	     (fun j t ->
		let t =  (strip_prod_assum t) in
		let applied_g = List.hd (List.rev (snd (decompose_app t))) in
		let g = fst (decompose_app applied_g) in
		if Constr.equal f g
		then raise (Found_type j);
                observe (Printer.pr_lconstr_env env sigma f ++ str " <> " ++
                         Printer.pr_lconstr_env env sigma g)

	     )
	     ta;
	   (* If we reach this point, the two principle are not mutually recursive
	      We fall back to the previous method
	   *)
	     let ((_,(const,_)),_) =
	       build_functional_principle
		 evd
		 false
		 (List.nth other_princ_types (!i - 1))
		 (Array.of_list sorts)
		 this_block_funs
		 !i
		 (prove_princ_for_struct evd false !i (Array.of_list (List.map fst funs)))
		 (fun _ _ _ -> ())
	     in
	     const
	 with Found_type i ->
	   let princ_body =
	     Termops.it_mkLambda_or_LetIn (mkFix((idxs,i),decl)) ctxt
	   in
	   {const with
	      const_entry_body = 
                (Future.from_val (Safe_typing.mk_pure_proof princ_body));
	      const_entry_type = Some scheme_type
	   }
      )
      other_fun_princ_types
    in
    const::other_result

let build_scheme fas =
  let evd = (ref (Evd.from_env (Global.env ()))) in
  let pconstants = (List.map
	 (fun (_,f,sort) ->
	    let f_as_constant =
	      try
		Smartlocate.global_with_alias f
	      with Not_found ->
                user_err ~hdr:"FunInd.build_scheme"
                  (str "Cannot find " ++ Libnames.pr_qualid f)
	    in
            let evd',f = Evd.fresh_global (Global.env ()) !evd f_as_constant in
            let _ = evd := evd' in 
            let sigma, _ = Typing.type_of ~refresh:true (Global.env ()) !evd f in
            evd := sigma;
            let c, u =
              try EConstr.destConst !evd f
              with DestKO ->
                user_err Pp.(pr_econstr_env (Global.env ()) !evd f ++spc () ++ str "should be the named of a globally defined function")
            in
            (c, EConstr.EInstance.kind !evd u), sort
         )
	 fas
		   ) in
  let bodies_types =
    make_scheme evd pconstants      
  in

  List.iter2
    (fun (princ_id,_,_) def_entry ->
       ignore
	 (Declare.declare_constant
	    princ_id
	    (DefinitionEntry def_entry,Decl_kinds.IsProof Decl_kinds.Theorem));
       Declare.definition_message princ_id
    )
    fas
    bodies_types

let build_case_scheme fa =
  let env = Global.env ()
  and sigma = (Evd.from_env (Global.env ())) in
(*   let id_to_constr id =  *)
(*     Constrintern.global_reference  id *)
(*   in  *)
  let funs =
    let (_,f,_) = fa in
    try fst (Global.constr_of_global_in_context (Global.env ()) (Smartlocate.global_with_alias f))
    with Not_found ->
      user_err ~hdr:"FunInd.build_case_scheme"
        (str "Cannot find " ++ Libnames.pr_qualid f) in
  let first_fun,u = destConst  funs in
  let funs_mp,funs_dp,_ = Constant.repr3 first_fun in
  let first_fun_kn = try fst (find_Function_infos  first_fun).graph_ind with Not_found -> raise No_graph_found in
  let this_block_funs_indexes = get_funs_constant funs_mp funs_dp first_fun in
  let this_block_funs = Array.map (fun (c,_) -> (c,u)) this_block_funs_indexes in
  let prop_sort = InProp in
  let funs_indexes =
    let this_block_funs_indexes = Array.to_list this_block_funs_indexes in
    List.assoc_f Constant.equal (fst (destConst funs)) this_block_funs_indexes
  in
  let (ind, sf) =
	 let ind = first_fun_kn,funs_indexes in
	   (ind,Univ.Instance.empty)(*FIXME*),prop_sort
  in
  let (sigma, scheme) = 
      Indrec.build_case_analysis_scheme_default env sigma ind sf
  in
  let scheme_type = EConstr.Unsafe.to_constr ((Typing.unsafe_type_of env sigma) (EConstr.of_constr scheme)) in
  let sorts =
    (fun (_,_,x) ->
       UnivGen.new_sort_in_family x
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
      (ref (Evd.from_env (Global.env ())))
      false
      scheme_type
      (Some ([|sorts|]))
      (Some princ_name)
      this_block_funs
      0
      (prove_princ_for_struct (ref (Evd.from_env (Global.env ()))) false 0 [|fst (destConst funs)|])
  in
  ()
 

