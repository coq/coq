open Util
open Names
open Term
open Pp
open Indfun_common
open Libnames
open Rawterm
open Declarations

(* arnaud: trucs factices *)
module Tacmach =
  struct
    type tactic = Tacticals.tactic
    let pf_type_of _ = Util.anomaly "Indfunc.pf_type_of: fantome"
    let pf_ids_of_hyps _ = Util.anomaly "Indfunc.pf_ids_of_hyps: fantome"
  end 
(* arnaud: /trucs factices *)

let is_rec_info scheme_info = 
  let test_branche min acc (_,_,br) = 
    acc || (
      let new_branche = 
	Sign.it_mkProd_or_LetIn mkProp (fst (Sign.decompose_prod_assum br)) in 
      let free_rels_in_br = Termops.free_rels new_branche in 
      let max = min + scheme_info.Tactics.npredicates in 
      Util.Intset.exists (fun i -> i >= min && i< max) free_rels_in_br
    )
  in
  Util.list_fold_left_i test_branche 1 false (List.rev scheme_info.Tactics.branches)


let choose_dest_or_ind scheme_info =
    if is_rec_info scheme_info
    then Tactics.new_induct false
    else Tactics.new_destruct false


let functional_induction with_clean c princl pat =
  let f,args = decompose_app c in 
  fun g ->      
    let princ,bindings, princ_type = 
      match princl with 
	| None -> (* No principle is given let's find the good one *)
	    begin
	      match kind_of_term f with
		| Const c' ->
		    let princ_option = 
		      let finfo = (* we first try to find out a graph on f *)
			try find_Function_infos c' 
			with Not_found -> 
			  errorlabstrm "" (str "Cannot find induction information on "++
					     Printer.pr_lconstr (mkConst c') )
		      in
		      match Tacticals.elimination_sort_of_goal g with 
			| InProp -> finfo.prop_lemma
			| InSet -> finfo.rec_lemma
			| InType -> finfo.rect_lemma
		    in
		    let princ =  (* then we get the principle *)
		      try mkConst (Option.get princ_option )
		      with Option.IsNone -> 
			(*i If there is not default lemma defined then, 
			  we cross our finger and try to find a lemma named f_ind 
			  (or f_rec, f_rect) i*)
			let princ_name = 
			  Indrec.make_elimination_ident
			    (id_of_label (con_label c'))
			    (Tacticals.elimination_sort_of_goal g)
			in
			try 
			  mkConst(const_of_id princ_name )
			with Not_found -> (* This one is neither defined ! *)
			  errorlabstrm "" (str "Cannot find induction principle for "
					   ++Printer.pr_lconstr (mkConst c') )
		    in
		    (princ,Rawterm.NoBindings, Tacmach.pf_type_of g princ)
		| _ -> raise (UserError("",str "functional induction must be used with a function" ))
		    
	    end
	| Some ((princ,binding)) -> 
	    princ,binding,Tacmach.pf_type_of g princ
    in
    let princ_infos = Tactics.compute_elim_sig princ_type in 
    let args_as_induction_constr =
      let c_list = 
	if princ_infos.Tactics.farg_in_concl 
	then [c] else [] 
      in
      List.map (fun c -> Tacexpr.ElimOnConstr (c,NoBindings)) (args@c_list) 
    in 
    let princ' = Some (princ,bindings) in 
    let princ_vars = 
      List.fold_right 
	(fun a acc -> 
	  try Idset.add (destVar a) acc
	  with _ -> acc
	)
	args
	Idset.empty
    in
    let old_idl = List.fold_right Idset.add (Tacmach.pf_ids_of_hyps g) Idset.empty in 
    let old_idl = Idset.diff old_idl princ_vars in 
    let subst_and_reduce g = 
      if with_clean 
      then
	let idl = 
	  map_succeed 
	    (fun id -> 
	       if Idset.mem id old_idl then failwith "subst_and_reduce";
	       id 
	    )
	    (Tacmach.pf_ids_of_hyps g)
	in 
	let flag = 
	  Rawterm.Cbv
	    {Rawterm.all_flags 
	     with Rawterm.rDelta = false; 		 
	    }
	in
	Tacticals.tclTHEN
	  (Tacticals.tclMAP (fun id -> Tacticals.tclTRY (Equality.subst [id])) idl )
	  (Hiddentac.h_reduce flag Tacticals.allClauses)	
	  g
      else Tacticals.tclIDTAC g 
	
    in
    Tacticals.tclTHEN
      (choose_dest_or_ind 
	 princ_infos
	 args_as_induction_constr
	 princ'
	 pat)
      subst_and_reduce
      g
      
      


type annot = 
    Struct of identifier 
  | Wf of Topconstr.constr_expr * identifier option * Topconstr.constr_expr list
  | Mes of Topconstr.constr_expr * identifier option * Topconstr.constr_expr list


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
    ~allow_patvar:false  ~ltacvars:([],[]) c


(* 
   Construct a fixpoint as a Rawterm 
   and not as a constr
*)
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
  recdef,rec_impls
	

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


(* Checks whether or not the mutual bloc is recursive *) 
let rec is_rec names = 
  let names = List.fold_right Idset.add names Idset.empty in 
  let check_id id names =  Idset.mem id names in 
  let rec lookup names = function 
    | RVar(_,id) -> check_id id names
    | RRef _ | REvar _ | RPatVar _ | RSort _ |  RHole _ | RDynamic _ -> false
    | RCast(_,b,_) -> lookup names b
    | RRec _ -> error "RRec not handled"
    | RIf(_,b,_,lhs,rhs) -> 
	(lookup names b) || (lookup names lhs) || (lookup names rhs)
    | RLetIn(_,na,t,b) | RLambda(_,na,t,b) | RProd(_,na,t,b)  -> 
	lookup names t || lookup (Nameops.name_fold Idset.remove na names) b
    | RLetTuple(_,nal,_,t,b) -> lookup names t || 
	lookup 
	  (List.fold_left 
	     (fun acc na -> Nameops.name_fold Idset.remove na acc)
	     names
	     nal
	  )
	  b
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


let derive_inversion fix_names =
  try 
    (* we first transform the fix_names identifier into their corresponding constant *)
    let fix_names_as_constant = 
      List.map (fun id -> destConst (Tacinterp.constr_of_id (Global.env ()) id)) fix_names 
    in 
    (* 
       Then we check that the graphs have been defined 
       If one of the graphs haven't been defined 
       we do nothing
    *)
    List.iter (fun c -> ignore (find_Function_infos c)) fix_names_as_constant ;
    try
      Invfun.derive_correctness 
	Functional_principles_types.make_scheme
	functional_induction 
	fix_names_as_constant
	(*i The next call to mk_rel_id is valid since we have just construct the graph 
	  Ensures by : register_built
	  i*) 
	(List.map
	   (fun id -> destInd (Tacinterp.constr_of_id (Global.env ()) (mk_rel_id id)))
	   fix_names
	)
    with e -> 
      msg_warning 
	(str "Cannot built inversion information" ++ 
	   if do_observe () then Cerrors.explain_exn e else mt ())
  with _ -> ()

let warning_error names e = 
  match e with 
    | Building_graph e -> 
	Pp.msg_warning 
	  (str "Cannot define graph(s) for " ++ 
	     h 1 (prlist_with_sep (fun _ -> str","++spc ()) Ppconstr.pr_id names) ++
	     if do_observe () then (spc () ++ Cerrors.explain_exn e) else mt ())
    | Defining_principle e -> 
	Pp.msg_warning
	  (str "Cannot define principle(s) for "++ 
	     h 1 (prlist_with_sep (fun _ -> str","++spc ()) Ppconstr.pr_id names) ++
	     if do_observe () then Cerrors.explain_exn e else mt ())
    | _ -> anomaly ""

let error_error names e = 
  match e with 
    | Building_graph e -> 
	errorlabstrm ""  
	  (str "Cannot define graph(s) for " ++ 
	     h 1 (prlist_with_sep (fun _ -> str","++spc ()) Ppconstr.pr_id names) ++
	     if do_observe () then (spc () ++ Cerrors.explain_exn e) else mt ())
    | _ -> anomaly ""

let generate_principle  on_error
    is_general do_built fix_rec_l recdefs  interactive_proof 
    (continue_proof : int -> Names.constant array -> Term.constr array -> int -> 
      Tacmach.tactic) : unit =
  let names = List.map (function (name,_,_,_,_) -> name) fix_rec_l in
  let fun_bodies = List.map2 prepare_body fix_rec_l recdefs in
  let funs_args = List.map fst fun_bodies in
  let funs_types =  List.map (function (_,_,_,types,_) -> types) fix_rec_l in
  try 
    (* We then register the Inductive graphs of the functions  *)
    Rawterm_to_relation.build_inductive names funs_args funs_types recdefs;
    if do_built 
    then
      begin
	(*i The next call to mk_rel_id is valid since we have just construct the graph 
	   Ensures by : do_built
	i*) 
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
	  list_map_i
	    (fun i x ->
	       let princ = destConst (Indrec.lookup_eliminator (ind_kn,i) (InProp)) in 
	       let princ_type = Typeops.type_of_constant (Global.env()) princ
	       in
	       Functional_principles_types.generate_functional_principle
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
	Array.iter (add_Function is_general) funs_kn;
	()
      end
  with e -> 
    on_error names e 

let register_struct is_rec fixpoint_exprl = 
  match fixpoint_exprl with 
    | [(fname,_,bl,ret_type,body),_] when not is_rec -> 
	Command.declare_definition
	  fname
	  (Decl_kinds.Global,Flags.boxed_definitions (),Decl_kinds.Definition)
	  bl
	  None
  	  body
	  (Some ret_type)
	  (fun _ _ -> ())
    | _ -> 
	Command.build_recursive fixpoint_exprl (Flags.boxed_definitions())

let generate_correction_proof_wf f_ref tcc_lemma_ref   
    is_mes functional_ref eq_ref rec_arg_num rec_arg_type nb_args relation
    (_: int) (_:Names.constant array) (_:Term.constr array) (_:int) : Tacmach.tactic = 
  Functional_principles_proofs.prove_principle_for_gen
    (f_ref,functional_ref,eq_ref)
    tcc_lemma_ref is_mes  rec_arg_num rec_arg_type relation


let register_wf ?(is_mes=false) fname rec_impls wf_rel_expr wf_arg using_lemmas args ret_type body
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
	  list_index (Name wf_arg) names 
  in
  let unbounded_eq = 
    let f_app_args = 
      Topconstr.CAppExpl 
	(dummy_loc, 
	 (None,(Ident (dummy_loc,fname))) ,
	 (List.map 
	    (function
	       | _,Anonymous -> assert false 
	       | _,Name e -> (Topconstr.mkIdentC e)
	    ) 
	    (Topconstr.names_of_local_assums args)
	 )
	) 
    in
    Topconstr.CApp (dummy_loc,(None,Topconstr.mkIdentC (id_of_string "eq")),
		    [(f_app_args,None);(body,None)])
  in
  let eq = Command.generalize_constr_expr unbounded_eq args in 
  let hook f_ref tcc_lemma_ref functional_ref eq_ref rec_arg_num rec_arg_type
      nb_args relation =
    try 
      pre_hook 
	(generate_correction_proof_wf f_ref tcc_lemma_ref is_mes
	   functional_ref eq_ref rec_arg_num rec_arg_type nb_args relation
	);
      derive_inversion [fname]
    with e -> 
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

    
let register_mes fname rec_impls wf_mes_expr wf_arg using_lemmas args ret_type body = 
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
  register_wf ~is_mes:true fname rec_impls wf_rel_from_mes (Some wf_arg) 
    using_lemmas args ret_type body
	  

let do_generate_principle on_error register_built interactive_proof fixpoint_exprl  = 
  let recdefs,rec_impls = build_newrecursive fixpoint_exprl in 
  let _is_struct = 
    match fixpoint_exprl with 
      | [((name,Some (Wf (wf_rel,wf_x,using_lemmas)),args,types,body))] -> 
	  let pre_hook = 
	    generate_principle 
	      on_error
	      true
	      register_built
	      fixpoint_exprl 
	      recdefs
	      true
	  in 
	  if register_built 
	  then register_wf name rec_impls wf_rel wf_x using_lemmas args types body pre_hook;
	  false
      | [((name,Some (Mes (wf_mes,wf_x,using_lemmas)),args,types,body))] -> 
	  let pre_hook = 
	    generate_principle 
	      on_error
	      true
	      register_built
	      fixpoint_exprl 
	      recdefs
	      true
	  in 
	  if register_built 
	  then register_mes name rec_impls wf_mes wf_x using_lemmas args types body pre_hook;
	  true
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
		       try Some (list_index0 (Name id) names), Topconstr.CStructRec 
		       with Not_found -> 
			 raise (UserError("",str "Cannot find argument " ++ 
					    Ppconstr.pr_id id)) 
		     in 
 		     (name,annot,args,types,body),(None:Vernacexpr.decl_notation) 
		 | (name,None,args,types,body),recdef -> 
		     let names =  (Topconstr.names_of_local_assums args) in
		     if  is_one_rec recdef  && List.length names > 1 then
		       user_err_loc
			 (dummy_loc,"Function",
			  Pp.str "the recursive argument needs to be specified in Function")
		     else 
		       (name,(Some 0, Topconstr.CStructRec),args,types,body),
		     (None:Vernacexpr.decl_notation)
		 | (_,Some (Wf _),_,_,_),_ | (_,Some (Mes _),_,_,_),_-> 
		     error 
		       ("Cannot use mutual definition with well-founded recursion or measure")
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
	    on_error
	    false
	    register_built
	    fixpoint_exprl
	    recdefs 
	    interactive_proof
	    (Functional_principles_proofs.prove_princ_for_struct interactive_proof);
	  if register_built then derive_inversion fix_names;
	  true;
  in
  ()

open Topconstr
let rec add_args id new_args b = 
  match b with 
  | CRef r -> 
      begin      match r with 
	| Libnames.Ident(loc,fname) when fname = id -> 
	    CAppExpl(dummy_loc,(None,r),new_args)
	| _ -> b
      end
  | CFix  _  | CCoFix _ -> anomaly "add_args : todo"
  | CArrow(loc,b1,b2) -> 
      CArrow(loc,add_args id new_args  b1, add_args id new_args b2)
  | CProdN(loc,nal,b1) -> 
      CProdN(loc,
	     List.map (fun (nal,b2) -> (nal,add_args id new_args b2)) nal, 
	     add_args id new_args  b1)
  | CLambdaN(loc,nal,b1) -> 
      CLambdaN(loc,
	       List.map (fun (nal,b2) -> (nal,add_args id new_args  b2)) nal, 
	       add_args id new_args  b1)
  | CLetIn(loc,na,b1,b2) -> 
      CLetIn(loc,na,add_args id new_args b1,add_args id new_args b2)
  | CAppExpl(loc,(pf,r),exprl) -> 
      begin 
	match r with 
	| Libnames.Ident(loc,fname) when fname = id -> 
	    CAppExpl(loc,(pf,r),new_args@(List.map (add_args id new_args) exprl))
	| _ -> CAppExpl(loc,(pf,r),List.map (add_args id new_args) exprl)
      end
  | CApp(loc,(pf,b),bl) -> 
      CApp(loc,(pf,add_args id new_args b), 
	   List.map (fun (e,o) -> add_args id new_args e,o) bl)
  | CCases(loc,b_option,cel,cal) -> 
      CCases(loc,Option.map (add_args id new_args) b_option,
	     List.map (fun (b,(na,b_option)) -> 
			 add_args id new_args b,
			 (na,Option.map (add_args id new_args) b_option)) cel, 
	     List.map (fun (loc,cpl,e) -> (loc,cpl,add_args id new_args e)) cal
	    )
  | CLetTuple(loc,nal,(na,b_option),b1,b2) -> 
      CLetTuple(loc,nal,(na,Option.map (add_args id new_args) b_option),
		add_args id new_args b1,
		add_args id new_args b2
	       )
		
  | CIf(loc,b1,(na,b_option),b2,b3) -> 
      CIf(loc,add_args id new_args b1, 
	  (na,Option.map (add_args id new_args) b_option),
	  add_args id new_args b2,
	  add_args id new_args b3
	 )
  | CHole _ -> b
  | CPatVar _ -> b
  | CEvar _ -> b
  | CSort _ -> b
  | CCast(loc,b1,CastConv(ck,b2))  -> 
      CCast(loc,add_args id new_args b1,CastConv(ck,add_args id new_args b2))
  | CCast(loc,b1,CastCoerce) ->
      CCast(loc,add_args id new_args b1,CastCoerce)
  | CNotation _ -> anomaly "add_args : CNotation"
  | CPrim _ -> b
  | CDelimiters _ -> anomaly "add_args : CDelimiters"
  | CDynamic _ -> anomaly "add_args : CDynamic"
exception Stop of  Topconstr.constr_expr


(* [chop_n_arrow n t] chops the [n] first arrows in [t] 
   Acts on Topconstr.constr_expr 
*)
let rec chop_n_arrow n t = 
  if n <= 0 
  then t (* If we have already removed all the arrows then return the type *)
  else (* If not we check the form of [t] *) 
    match t with 
      | Topconstr.CArrow(_,_,t) ->  (* If we have an arrow, we discard it and recall [chop_n_arrow] *)
	  chop_n_arrow (n-1) t
      | Topconstr.CProdN(_,nal_ta',t') -> (* If we have a forall, to result are possible : 
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
		| (nal,t'')::nal_ta' -> 
		    let nal_l = List.length nal in 
		    if n >= nal_l
		    then 
		      aux (n - nal_l) nal_ta'
		    else 
		      let new_t' = Topconstr.CProdN(dummy_loc,((snd (list_chop n nal)),t'')::nal_ta',t')
		      in 
		      raise (Stop new_t')
		in
		aux n nal_ta'
	    in 
	      chop_n_arrow new_n t'
	    with Stop t -> t
	  end
      | _ -> anomaly "Not enough products"
  

let rec get_args b t : Topconstr.local_binder list * 
    Topconstr.constr_expr * Topconstr.constr_expr = 
  match b with 
    | Topconstr.CLambdaN (loc, (nal_ta), b') -> 
	begin
	  let n = 
	    (List.fold_left (fun n (nal,_) -> 
			       n+List.length nal) 0 nal_ta )
	  in
	  let nal_tas,b'',t'' = get_args b' (chop_n_arrow n t) in 
	  (List.map (fun (nal,ta) -> 
		       (Topconstr.LocalRawAssum (nal,ta))) nal_ta)@nal_tas, b'',t'' 
	end
    | _ -> [],b,t


let make_graph (f_ref:global_reference) =
 let c,c_body = 
      match f_ref with 
	| ConstRef c -> 
	    begin try c,Global.lookup_constant c 
	    with Not_found -> 
	      raise (UserError ("",str "Cannot find " ++ Printer.pr_lconstr (mkConst c)) )
	    end
	| _ -> raise (UserError ("", str "Not a function reference") )

  in
  match c_body.const_body with
    | None -> error "Cannot build a graph over an axiom !"
    | Some b ->
	let env = Global.env () in
	let body = (force b) in
	let extern_body,extern_type = 
	  with_full_print 
	    (fun () -> 
	       (Constrextern.extern_constr false env body, 
		Constrextern.extern_type false env
                  (Typeops.type_of_constant_type env c_body.const_type)
	       )
	    )
	    ()
	in
	let (nal_tas,b,t)  = get_args extern_body extern_type in
	let expr_list = 
	  match b with 
	    | Topconstr.CFix(loc,l_id,fixexprl) -> 
		let l = 
		  List.map
		    (fun (id,(n,recexp),bl,t,b) -> 
		       let bl' =  
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
			 match List.nth bl' (Option.get n)  with 
			   |(_,Name id) -> id | _ -> anomaly ""
		       in
		       let new_args = 
			 List.flatten 
			   (List.map 
			      (function
 				 | Topconstr.LocalRawDef (na,_)-> []
			      	 | Topconstr.LocalRawAssum (nal,_) -> 
				     List.map 
				       (fun (loc,n) -> 
					  CRef(Libnames.Ident(loc, Nameops.out_name n))) 
				       nal
			      )
			      nal_tas
			   )
		       in
		       let b' = add_args id new_args b in 
		       (id, Some (Struct rec_id),nal_tas@bl,t,b')
		    )
		    fixexprl
		in
		l
	    | _ ->   
		let id = id_of_label (con_label c) in 
		[(id,None,nal_tas,t,b)]
	in
	do_generate_principle error_error false false expr_list;
	(* We register the infos *)
	let mp,dp,_ = repr_con c in 
	List.iter 
	  (fun (id,_,_,_,_) -> add_Function false (make_con mp dp (label_of_id id))) 
	  expr_list


(* let make_graph _ = assert false	 *)
	  
let do_generate_principle = do_generate_principle warning_error true 


