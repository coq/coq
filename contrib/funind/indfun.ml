open Util
open Names
open Term

open Pp
open Indfun_common
open Libnames
open Rawterm
open Declarations

type annot = 
    Struct of identifier 
  | Wf of Topconstr.constr_expr * identifier option
  | Mes of Topconstr.constr_expr * identifier option


type newfixpoint_expr =
    identifier * annot * Topconstr.local_binder list * Topconstr.constr_expr * Topconstr.constr_expr

let rec abstract_rawconstr c = function
  | [] -> c
  | Topconstr.LocalRawDef (x,b)::bl -> Topconstr.mkLetInC(x,b,abstract_rawconstr c bl)
  | Topconstr.LocalRawAssum (idl,t)::bl ->
      List.fold_right (fun x b -> Topconstr.mkLambdaC([x],t,b)) idl
        (abstract_rawconstr c bl)

let interp_casted_constr_with_implicits sigma env impls c  =
(*   Constrintern.interp_rawconstr_with_implicits sigma env [] impls c *)
  Constrintern.intern_gen false sigma env ~impls:([],impls) 
    ~allow_soapp:false  ~ltacvars:([],[]) c

let build_newrecursive
(lnameargsardef)  =
  let env0 = Global.env()
  and sigma = Evd.empty
  in
  let (rec_sign,rec_impls) =
    List.fold_left
      (fun (env,impls) (recname,_,bl,arityc,_) ->
        let arityc = Command.generalize_constr_expr arityc bl in
        let arity = Constrintern.interp_type sigma env0 arityc in
	let impl =
	  if Impargs.is_implicit_args()
	  then Impargs.compute_implicits  env0 arity
	  else [] in
	let impls' =(recname,([],impl,Notation.compute_arguments_scope arity))::impls in
        (Environ.push_named (recname,None,arity) env, impls'))
      (env0,[]) lnameargsardef in
  let recdef =
    (* Declare local notations *)
    let fs = States.freeze() in
    let def =
      try
	List.map
	  (fun (_,_,bl,_,def)  ->
             let def = abstract_rawconstr def bl in
             interp_casted_constr_with_implicits
	       sigma rec_sign rec_impls def
	  )
          lnameargsardef
	with e ->
	States.unfreeze fs; raise e in
    States.unfreeze fs; def
  in
  recdef
	

let compute_annot (name,annot,args,types,body) =
  let names = List.map snd (Topconstr.names_of_local_assums args) in
  match annot with
    | None ->
        if List.length names > 1 then
          user_err_loc
            (dummy_loc,"Function",
             Pp.str "the recursive argument needs to be specified");
        let new_annot = (id_of_name (List.hd names)) in
	(name,Struct new_annot,args,types,body)
    | Some r -> (name,r,args,types,body)


let rec is_rec names = 
  let names = List.fold_right Idset.add names Idset.empty in 
  let check_id id names =  Idset.mem id names in 
  let rec lookup names = function 
    | RVar(_,id) -> check_id id names
    | RRef _ | REvar _ | RPatVar _ | RSort _ |  RHole _ | RDynamic _ -> false
    | RCast(_,b,_,_) -> lookup names b
    | RRec _ -> assert false 
    | RIf(_,b,_,lhs,rhs) -> 
	(lookup names b) || (lookup names lhs) || (lookup names rhs)
    | RLetIn(_,na,t,b) | RLambda(_,na,t,b) | RProd(_,na,t,b)  -> 
	lookup names t || lookup (Nameops.name_fold Idset.remove na names) b
    | RLetTuple(_,_,_,t,b) -> error "RLetTuple not handled"
    | RApp(_,f,args) -> List.exists (lookup names) (f::args)
    | RCases(_,_,el,brl) -> 
	List.exists (fun (e,_) -> lookup names e) el ||
	  List.exists (lookup_br names) brl
  and lookup_br names (_,idl,_,rt) = 
    let new_names = List.fold_right Idset.remove idl names in 
    lookup new_names rt
  in
  lookup names

let prepare_body (name,annot,args,types,body) rt = 
  let n = (Topconstr.local_binders_length args) in 
(*   Pp.msgnl (str "nb lambda to chop : " ++ str (string_of_int n) ++ fnl () ++Printer.pr_rawconstr rt); *)
  let fun_args,rt' = chop_rlambda_n n rt in
  (fun_args,rt')


let generate_principle 
    do_built fix_rec_l recdefs  interactive_proof parametrize 
    (continue_proof : int -> Names.constant array -> Term.constr array -> int -> Tacmach.tactic)  =
  let names = List.map (function (name,_,_,_,_) -> name) fix_rec_l in
  let fun_bodies = List.map2 prepare_body fix_rec_l recdefs in
  let funs_args = List.map fst fun_bodies in
  let funs_types =  List.map (function (_,_,_,types,_) -> types) fix_rec_l in
  try 
    (* We then register the Inductive graphs of the functions  *)
    Rawterm_to_relation.build_inductive parametrize names funs_args funs_types recdefs;
    if do_built 
    then
      begin
	let f_R_mut = Ident (dummy_loc,mk_rel_id (List.nth names 0)) in
	let ind_kn =
	  fst (locate_with_msg
		 (pr_reference f_R_mut++str ": Not an inductive type!")
		 locate_ind
		 f_R_mut)
	in
	let fname_kn (fname,_,_,_,_) =
	  let f_ref = Ident (dummy_loc,fname) in
	  locate_with_msg
	    (pr_reference f_ref++str ": Not an inductive type!")
	    locate_constant
	    f_ref
	in
	let funs_kn = Array.of_list (List.map fname_kn fix_rec_l) in 
	let _ = 
	  Util.list_map_i
	    (fun i x ->
	       let princ = destConst (Indrec.lookup_eliminator (ind_kn,i) (InProp)) in 
	       let princ_type = 
		 (Global.lookup_constant princ).Declarations.const_type
	       in
	       New_arg_principle.generate_functional_principle
		 interactive_proof 
		 princ_type
		 None
		 None 
		 funs_kn
		 i
		 (continue_proof  0 [|funs_kn.(i)|]) 
	    )
	    0
	    fix_rec_l
	in 
	()
      end
  with e -> 
    Pp.msg_warning (Cerrors.explain_exn e) 


let register_struct is_rec fixpoint_exprl = 
  match fixpoint_exprl with 
    | [(fname,_,bl,ret_type,body),_] when not is_rec -> 
	Command.declare_definition
	  fname
	  (Decl_kinds.Global,Options.boxed_definitions (),Decl_kinds.Definition)
	  bl
	  None
  	  body
	  (Some ret_type)
	  (fun _ _ -> ())
    | _ -> 
	Command.build_recursive fixpoint_exprl (Options.boxed_definitions())


let generate_correction_proof_wf tcc_lemma_ref   
    is_mes f_ref eq_ref rec_arg_num rec_arg_type nb_args relation
    (_: int) (_:Names.constant array) (_:Term.constr array) (_:int) : Tacmach.tactic = 
  Recdef.prove_principle  tcc_lemma_ref
    is_mes f_ref eq_ref rec_arg_num rec_arg_type nb_args relation


let register_wf ?(is_mes=false) fname wf_rel_expr wf_arg args ret_type body
    pre_hook 
    =  
  let type_of_f = Command.generalize_constr_expr ret_type args in 
  let rec_arg_num = 
    let names = 
      List.map
	snd
	(Topconstr.names_of_local_assums args) 
    in 
    match wf_arg with 
      | None -> 
	  if List.length names = 1 then 1
	  else error "Recursive argument must be specified"
      | Some wf_arg -> 
	  Util.list_index (Name wf_arg) names 
  in
  let unbounded_eq = 
    let f_app_args = 
      Topconstr.CApp 
	(dummy_loc, 
	 (None,Topconstr.mkIdentC fname) ,
	 (List.map 
	    (function
	       | _,Anonymous -> assert false 
	       | _,Name e -> (Topconstr.mkIdentC e,None)
	    ) 
	    (Topconstr.names_of_local_assums args)
	 )
	) 
    in
    Topconstr.CApp (dummy_loc,(None,Topconstr.mkIdentC (id_of_string "eq")),
		    [(f_app_args,None);(body,None)])
  in
  let eq = Command.generalize_constr_expr unbounded_eq args in 
  let hook tcc_lemma_ref f_ref eq_ref rec_arg_num rec_arg_type nb_args relation =
    try 
      pre_hook 
	(generate_correction_proof_wf tcc_lemma_ref is_mes
	   f_ref eq_ref rec_arg_num rec_arg_type nb_args relation
	);
      Command.save_named true
    with e -> 
      (* No proof done *) 
      ()
  in 
  Recdef.recursive_definition 
    is_mes fname 
    type_of_f
    wf_rel_expr
    rec_arg_num
    eq
    hook

    
let register_mes fname wf_mes_expr wf_arg args ret_type body = 
  let wf_arg_type,wf_arg = 
    match wf_arg with 
      | None -> 
	  begin
	    match args with 
	      | [Topconstr.LocalRawAssum ([(_,Name x)],t)] -> t,x 
	      | _ -> error "Recursive argument must be specified" 
	  end
      | Some wf_args -> 
	  try 
	    match 
	      List.find 
		(function 
		   | Topconstr.LocalRawAssum(l,t) -> 
		       List.exists 
			 (function (_,Name id) -> id =  wf_args | _ -> false) 
			 l 
		   | _ -> false
		)
		args 
	    with 
	      | Topconstr.LocalRawAssum(_,t)  ->	    t,wf_args
	      | _ -> assert false 
	  with Not_found -> assert false 
  in
  let ltof = 
    let make_dir l = make_dirpath (List.map id_of_string (List.rev l)) in 
    Libnames.Qualid (dummy_loc,Libnames.qualid_of_sp 
      (Libnames.make_path (make_dir ["Arith";"Wf_nat"]) (id_of_string "ltof")))
  in
  let fun_from_mes = 
    let applied_mes = 
      Topconstr.mkAppC(wf_mes_expr,[Topconstr.mkIdentC wf_arg])    in
    Topconstr.mkLambdaC ([(dummy_loc,Name wf_arg)],wf_arg_type,applied_mes) 
  in
  let wf_rel_from_mes = 
    Topconstr.mkAppC(Topconstr.mkRefC  ltof,[wf_arg_type;fun_from_mes])
  in
  register_wf ~is_mes:true fname wf_rel_from_mes (Some wf_arg) args ret_type body
	  

let do_generate_principle register_built interactive_proof fixpoint_exprl  = 
  let recdefs = build_newrecursive fixpoint_exprl in 
  let _is_struct = 
    match fixpoint_exprl with 
      | [((name,Some (Wf (wf_rel,wf_x)),args,types,body))] -> 
	  let pre_hook = 
	    generate_principle 
	      register_built
	      fixpoint_exprl 
	      recdefs
	      true
	      false
	  in 
	  if register_built then register_wf name wf_rel wf_x args types body pre_hook;
	  false
      | [((name,Some (Mes (wf_mes,wf_x)),args,types,body))] -> 
	  let pre_hook = 
	    generate_principle 
	      register_built
	      fixpoint_exprl 
	      recdefs
	      true
	      false
	  in 
	  if register_built then register_mes name wf_mes wf_x args types body pre_hook;
	  false
      | _ -> 
	  let fix_names = 
	    List.map (function (name,_,_,_,_) -> name) fixpoint_exprl 
	  in
	  let is_one_rec = is_rec fix_names  in
	  let old_fixpoint_exprl =  
	    List.map
	      (function
		 | (name,Some (Struct id),args,types,body),_ -> 
		     let names = 
		       List.map
			 snd
			 (Topconstr.names_of_local_assums args) 
		     in 
		     let annot = 
		       try Some (Util.list_index (Name id) names - 1), Topconstr.CStructRec 
		       with Not_found -> raise (UserError("",str "Cannot find argument " ++ Ppconstr.pr_id id)) 
		     in 
 		     (name,annot,args,types,body),(None:Vernacexpr.decl_notation) 
		 | (name,None,args,types,body),recdef -> 
		     let names =  (Topconstr.names_of_local_assums args) in
		     if  is_one_rec recdef  && List.length names > 1 then
		       Util.user_err_loc
			 (Util.dummy_loc,"Function",
			  Pp.str "the recursive argument needs to be specified in Function")
		     else 
		       (name,(Some 0, Topconstr.CStructRec),args,types,body),(None:Vernacexpr.decl_notation)
		 | (_,Some (Wf _),_,_,_),_ | (_,Some (Mes _),_,_,_),_-> 
		     error 
		       ("Cannot use mutual definition with well-founded recursion")
	      ) 
	      (List.combine fixpoint_exprl recdefs)
	  in
	  (* ok all the expressions are structural *) 
	  let fix_names = 
	    List.map (function (name,_,_,_,_) -> name) fixpoint_exprl 
	  in
	  let is_rec = List.exists (is_rec fix_names) recdefs in
	  if register_built then register_struct is_rec old_fixpoint_exprl;
	  generate_principle
	    register_built
	    fixpoint_exprl
	    recdefs 
	    interactive_proof
	    true
	    (New_arg_principle.prove_princ_for_struct interactive_proof);
	  true
						 
  in
  ()

let make_graph (id:identifier) =
 let c_body = 
    try
      let c = const_of_id id  in
      Global.lookup_constant c 
    with Not_found -> 
      raise (UserError ("",str "Cannot find " ++ Ppconstr.pr_id id) )
  in

  match c_body.const_body with
    | None -> error "Cannot build a graph over an axiom !"
    | Some b ->
	let env = Global.env () in
	let body = (force b) in
	let extern_body,extern_type = 
	  let old_implicit_args = Impargs.is_implicit_args ()
	  and old_strict_implicit_args =  Impargs.is_strict_implicit_args ()
	  and old_contextual_implicit_args = Impargs.is_contextual_implicit_args () in
	  let old_rawprint = !Options.raw_print in 
	  Options.raw_print := true;
	  Impargs.make_implicit_args false;
	  Impargs.make_strict_implicit_args false;
	  Impargs.make_contextual_implicit_args false;
	  try 
	    let res =  Constrextern.extern_constr false env body in 
	    let res' = Constrextern.extern_type false env  c_body.const_type in 
	    Impargs.make_implicit_args old_implicit_args;
	    Impargs.make_strict_implicit_args old_strict_implicit_args;
	    Impargs.make_contextual_implicit_args old_contextual_implicit_args;
	    Options.raw_print := old_rawprint;
	    res,res'
	  with
	    | UserError(s,msg) as e -> 
		Impargs.make_implicit_args old_implicit_args;
		Impargs.make_strict_implicit_args old_strict_implicit_args;
		Impargs.make_contextual_implicit_args old_contextual_implicit_args;
		Options.raw_print := old_rawprint;
		raise e
	    | e -> 
		Impargs.make_implicit_args old_implicit_args;
		Impargs.make_strict_implicit_args old_strict_implicit_args;
		Impargs.make_contextual_implicit_args old_contextual_implicit_args;
		Options.raw_print := old_rawprint;
		raise e
	in
	let expr_list = 
	  match extern_body with 
	    | Topconstr.CFix(loc,l_id,fixexprl) -> 
	      let l = 
		List.map
		  (fun (id,(n,recexp),bl,t,b) -> 
		     let nal =  
		       List.flatten 
			 (List.map 
			    (function 
			       | Topconstr.LocalRawDef (na,_)-> []
			       | Topconstr.LocalRawAssum (nal,_) -> nal
			    )
			    bl
			 )
		     in 
		     let rec_id = 
		       match List.nth nal (out_some n)  with |(_,Name id) -> id | _ -> anomaly ""
		     in
		     (id, Some (Struct rec_id),bl,t,b)
		  )
		  fixexprl
	      in
	      l
	    | _ ->  
		let rec get_args b t : Topconstr.local_binder list * 
		    Topconstr.constr_expr * Topconstr.constr_expr = 
(* 		  Pp.msgnl (str "body: " ++Ppconstr.pr_lconstr_expr b); *)
(* 		  Pp.msgnl (str "type: " ++ Ppconstr.pr_lconstr_expr t); *)
(* 		  Pp.msgnl (fnl ()); *)
		  match b with 
		    | Topconstr.CLambdaN (loc, (nal_ta), b') -> 
			begin
			  let n = 
			    (List.fold_left (fun n (nal,_) -> 
					       n+List.length nal) 0 nal_ta )
			  in
			  let rec chop_n_arrow n t = 
			    if n > 0 
			    then 
			      match t with 
				| Topconstr.CArrow(_,_,t) -> chop_n_arrow (n-1) t 
				| Topconstr.CProdN(_,nal_ta',t') -> 
				    let n' = 
				      List.fold_left 
					(fun n (nal,t'') -> 
					   n+List.length nal) n nal_ta' 
				    in
				    assert (n'<= n); 
				    chop_n_arrow (n - n') t'
				| _ -> anomaly "Not enough products"
			    else t
			  in 
			  let nal_tas,b'',t'' = get_args b' (chop_n_arrow n t) in 
			  (List.map (fun (nal,ta) -> (Topconstr.LocalRawAssum (nal,ta))) nal_ta)@nal_tas, b'',t'' 
			end
		    | _ -> [],b,t
		in
		let nal_tas,b,t = get_args extern_body extern_type in
		[(id,None,nal_tas,t,b)]
		  
	in
	do_generate_principle false false expr_list
(* let make_graph _ = assert false	 *)
	  
let do_generate_principle = do_generate_principle true 
