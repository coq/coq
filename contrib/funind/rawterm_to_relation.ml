open Printer
open Pp
open Names 
open Term
open Rawterm
open Libnames
open Indfun_common
open Util
open Rawtermops

let observe strm =  
  if do_observe ()
  then Pp.msgnl strm 
  else ()
let observennl strm =  
  if do_observe ()
  then Pp.msg strm 
  else ()


type binder_type =
  | Lambda of name 
  | Prod of name 
  | LetIn of name

type raw_context = (binder_type*rawconstr) list


(* 
   compose_raw_context [(bt_1,n_1,t_1);......] rt returns 
   b_1(n_1,t_1,.....,bn(n_k,t_k,rt)) where the b_i's are the 
   binders corresponding to the bt_i's
*)
let compose_raw_context = 
  let compose_binder  (bt,t) acc =
    match bt with 
      | Lambda n -> mkRLambda(n,t,acc)
      | Prod n -> mkRProd(n,t,acc)
      | LetIn n -> mkRLetIn(n,t,acc)
  in
  List.fold_right compose_binder
  

(* 
   The main part deals with building a list of raw constructor expressions
   from the rhs of a fixpoint equation. 
*)

type 'a build_entry_pre_return = 
    {
      context : raw_context;  (* the binding context of the result *)
      value : 'a; (* The value *)
    }

type 'a build_entry_return = 
    {
      result : 'a build_entry_pre_return list; 
      to_avoid : identifier list
    }

(*
  [combine_results combine_fun res1 res2] combine two results [res1] and [res2] 
  w.r.t. [combine_fun].

  Informally, both [res1] and [res2] are lists of "constructors"  [res1_1;...] 
  and [res2_1,....] and we need to produce 
  [combine_fun res1_1 res2_1;combine_fun res1_1 res2_2;........]
*)

let combine_results 
    (combine_fun : 'a build_entry_pre_return -> 'b build_entry_pre_return -> 
      'c build_entry_pre_return
    )  
    (res1: 'a build_entry_return) 
    (res2 : 'b build_entry_return) 
    : 'c build_entry_return 
    = 
  let pre_result =     List.map 
    ( fun res1 ->  (* for each result in arg_res *)
	  List.map (* we add it in each args_res *) 
	    (fun res2 -> 
	       combine_fun res1 res2
	    )
	    res2.result
      )
      res1.result
  in (* and then we flatten the map *)
  {
    result = List.concat pre_result; 
    to_avoid = list_union res1.to_avoid res2.to_avoid
  }
    

(* 
   The combination function for an argument with a list of argument 
*)

let combine_args arg args = 
  {
    context = arg.context@args.context; 
    (* Note that the binding context of [arg] MUST be placed before the one of 
       [args] in order to preserve possible type dependencies 
    *)
    value = arg.value::args.value;
  }


let ids_of_binder =  function 
  | LetIn Anonymous | Prod Anonymous | Lambda Anonymous -> []
  | LetIn (Name id)  | Prod (Name id) | Lambda (Name id) -> [id]

let rec change_vars_in_binder mapping = function 
    [] -> []
  | (bt,t)::l ->
      let new_mapping = List.fold_right Idmap.remove (ids_of_binder bt) mapping in 
      (bt,change_vars mapping t)::
	(if idmap_is_empty new_mapping
	 then l 
	 else change_vars_in_binder new_mapping l
	)

let rec replace_var_by_term_in_binder x_id term = function
  | [] -> []
  | (bt,t)::l -> 
      (bt,replace_var_by_term x_id term t)::
	if List.mem x_id (ids_of_binder bt) 
	then l
	else replace_var_by_term_in_binder x_id term l

let add_bt_names bt = List.append (ids_of_binder bt)

let apply_args ctxt body args = 
  let need_convert_id avoid id = 
    List.exists (is_free_in id) args || List.mem id avoid 
  in 
  let need_convert avoid  bt =  
    List.exists (need_convert_id avoid) (ids_of_binder bt)
  in
  let next_name_away (na:name) (mapping: identifier Idmap.t) (avoid: identifier list) = 
    match na with 
       | Name id when List.mem id avoid -> 
	   let new_id = Nameops.next_ident_away id avoid in 
	   Name new_id,Idmap.add id new_id mapping,new_id::avoid
       | _ -> na,mapping,avoid
  in
  let next_bt_away bt (avoid:identifier list) = 
    match bt with 
      | LetIn na -> 
	  let new_na,mapping,new_avoid = next_name_away na Idmap.empty avoid  in 
	  LetIn new_na,mapping,new_avoid
      | Prod na -> 
	  let new_na,mapping,new_avoid = next_name_away na Idmap.empty avoid  in 
	  Prod new_na,mapping,new_avoid
      | Lambda na -> 
	  let new_na,mapping,new_avoid = next_name_away na Idmap.empty avoid  in 
	  Lambda new_na,mapping,new_avoid
  in
  let rec do_apply avoid ctxt body args = 
    match ctxt,args with  
      | _,[] -> (* No more args *)
	  (ctxt,body)
      | [],_ -> (* no more fun *)
	  let f,args' = raw_decompose_app body in
	  (ctxt,mkRApp(f,args'@args))
      | (Lambda Anonymous,t)::ctxt',arg::args' -> 
	  do_apply avoid ctxt' body args'
      | (Lambda (Name id),t)::ctxt',arg::args' -> 
	  let new_avoid,new_ctxt',new_body,new_id = 
	    if need_convert_id avoid id 
	    then 
	      let new_avoid =  id::avoid in 
	      let new_id = Nameops.next_ident_away id new_avoid in 
	      let new_avoid' = new_id :: new_avoid in 
	      let mapping = Idmap.add id new_id Idmap.empty in 
	      let new_ctxt' = change_vars_in_binder mapping ctxt' in 
	      let new_body = change_vars mapping body in 
	      new_avoid',new_ctxt',new_body,new_id
	    else 
	      id::avoid,ctxt',body,id 
	  in
	  let new_body = replace_var_by_term new_id arg new_body in
	  let new_ctxt' = replace_var_by_term_in_binder new_id arg new_ctxt' in
	  do_apply avoid new_ctxt' new_body args'
      | (bt,t)::ctxt',_ -> 
	  let new_avoid,new_ctxt',new_body,new_bt = 
	    let new_avoid = add_bt_names bt avoid in 
	    if need_convert avoid bt 
	    then 
	      let new_bt,mapping,new_avoid = next_bt_away bt new_avoid in 
	      (
		new_avoid,
		change_vars_in_binder mapping ctxt',
		change_vars mapping body,
		new_bt
	     )
	    else new_avoid,ctxt',body,bt
	  in
	  let new_ctxt',new_body = 
	    do_apply new_avoid new_ctxt' new_body args 
	  in
	  (new_bt,t)::new_ctxt',new_body
  in 
  do_apply []  ctxt body args


let combine_app f args = 
  let new_ctxt,new_value = apply_args f.context f.value args.value in 
  { 
    (* Note that the binding context of [args] MUST be placed before the one of 
       the applied value in order to preserve possible type dependencies 
    *)
      context = args.context@new_ctxt;
      value = new_value;
  }

let combine_lam n t b = 
  {
    context = []; 
    value = mkRLambda(n, compose_raw_context t.context t.value, 
		      compose_raw_context b.context b.value )
  }



let combine_prod n t b = 
  { context = t.context@((Prod n,t.value)::b.context); value = b.value}

let combine_letin n t b = 
  { context = t.context@((LetIn n,t.value)::b.context); value = b.value}


let mk_result ctxt value avoid = 
  { 
    result = 
      [{context = ctxt;
	value = value}]
	;
    to_avoid = avoid
  }
(*************************************************
  Some functions to deal with overlapping patterns 
**************************************************)

let coq_True_ref = 
  lazy  (Coqlib.gen_reference "" ["Init";"Logic"] "True")

let coq_False_ref = 
  lazy  (Coqlib.gen_reference "" ["Init";"Logic"] "False")

(*
  [make_discr_match_el \[e1,...en\]] builds match e1,...,en with
  (the list of expresions on which we will do the matching)
 *) 
let make_discr_match_el  = 
  List.map (fun e -> (e,(Anonymous,None)))

(*
  [make_discr_match_brl i \[pat_1,...,pat_n\]]  constructs a discrimination pattern matching on the ith expression. 
  that is. 
  match ?????? with \\
  | pat_1 => False  \\
  | pat_{i-1} => False \\
  | pat_i => True \\
  | pat_{i+1} => False \\
  \vdots 
  | pat_n => False
  end
*)
let make_discr_match_brl i = 
  list_map_i 
    (fun j (_,idl,patl,_) -> 
       if j=i
       then (dummy_loc,idl,patl, mkRRef (Lazy.force coq_True_ref))
       else (dummy_loc,idl,patl, mkRRef (Lazy.force coq_False_ref))
    )
    0 
(* 
   [make_discr_match brl el i] generates an hypothesis such that it reduce to true iff 
   brl_{i} is the first branch matched by [el] 

   Used when we want to simulate the coq pattern matching algorithm
*)
let make_discr_match brl = 
  fun el i -> 
  mkRCases(None,
	   make_discr_match_el el,
	   make_discr_match_brl i brl)

let pr_name = function
  | Name id -> Ppconstr.pr_id id
  | Anonymous -> str "_"

(**********************************************************************)
(*  functions used to build case expression from lettuple and if ones *)
(**********************************************************************)		

(* [build_constructors_of_type] construct the array of pattern of its inductive argument*)	  
let build_constructors_of_type ind' argl = 
  let (mib,ind) = Inductive.lookup_mind_specif (Global.env()) ind' in
  let npar = mib.Declarations.mind_nparams in
  Array.mapi (fun i _ ->
		let construct = ind',i+1 in 
		let constructref = ConstructRef(construct) in 
		let _implicit_positions_of_cst =
		  Impargs.implicits_of_global constructref
		in
		let cst_narg = 
		  Inductiveops.mis_constructor_nargs_env
		    (Global.env ())
		    construct
		in 
		let argl = 
		  if argl = [] 
		  then
 		    Array.to_list 
		      (Array.init (cst_narg - npar) (fun _ -> mkRHole ())
		      )
		  else argl
		in
		let pat_as_term = 
		  mkRApp(mkRRef (ConstructRef(ind',i+1)),argl)
		in
		cases_pattern_of_rawconstr Anonymous pat_as_term
	     )
    ind.Declarations.mind_consnames

(* [find_type_of] very naive attempts to discover the type of an if or a letin *)
let rec find_type_of nb b = 
  let f,_ = raw_decompose_app b in 
  match f with 
    | RRef(_,ref) -> 
	begin 
	  let ind_type  = 
	    match ref with 
	      | VarRef _ | ConstRef _ -> 
		  let constr_of_ref = constr_of_global ref in  
		  let type_of_ref = Typing.type_of (Global.env ()) Evd.empty constr_of_ref in 
		  let (_,ret_type) = Reduction.dest_prod (Global.env ()) type_of_ref in 
		  let ret_type,_ = decompose_app ret_type in 
		  if not (isInd ret_type) then 
		    begin
(* 		      Pp.msgnl (str "not an inductive" ++ pr_lconstr ret_type); *)
		      raise (Invalid_argument "not an inductive")
		    end;
		  destInd ret_type
	      | IndRef ind -> ind
	      | ConstructRef c -> fst c 
	  in
	  let _,ind_type_info = Inductive.lookup_mind_specif (Global.env()) ind_type in 
	  if not (Array.length ind_type_info.Declarations.mind_consnames = nb )
	  then raise (Invalid_argument "find_type_of : not a valid inductive");
	  ind_type	   
	end
    | RCast(_,b,_) -> find_type_of nb b 
    | RApp _ -> assert false (* we have decomposed any application via raw_decompose_app *)
    | _ -> raise (Invalid_argument "not a ref")
    



(******************)
(* Main functions *)
(******************)



let raw_push_named (na,raw_value,raw_typ) env = 
  match na with 
    | Anonymous -> env 
    | Name id -> 
	let value = Option.map (Pretyping.Default.understand Evd.empty env) raw_value in 
	let typ = Pretyping.Default.understand_type Evd.empty env raw_typ in 
	Environ.push_named (id,value,typ) env


let add_pat_variables pat typ env : Environ.env = 
  let rec add_pat_variables env pat typ  : Environ.env = 
    observe (str "new rel env := " ++ Printer.pr_rel_context_of env);

    match pat with 
      | PatVar(_,na) -> Environ.push_rel (na,None,typ) env 
      | PatCstr(_,c,patl,na) -> 
	  let Inductiveops.IndType(indf,indargs) = 
	    try Inductiveops.find_rectype env Evd.empty typ
	    with Not_found -> assert false 
	  in
	  let constructors = Inductiveops.get_constructors env indf in 
	  let constructor : Inductiveops.constructor_summary = List.find (fun cs -> cs.Inductiveops.cs_cstr = c) (Array.to_list constructors) in 
	  let cs_args_types :types list = List.map (fun (_,_,t) -> t) constructor.Inductiveops.cs_args in 
	  List.fold_left2 add_pat_variables env patl (List.rev cs_args_types) 
  in
  let new_env = add_pat_variables  env pat typ in 
  let res =
    fst (
      Sign.fold_rel_context
	(fun (na,v,t) (env,ctxt) ->
	 match na with
	   | Anonymous -> assert false
	   | Name id ->
	       let new_t =  substl ctxt t in
	       let new_v = Option.map (substl ctxt) v in
	       observe (str "for variable " ++ Ppconstr.pr_id id ++  fnl () ++
			  str "old type := " ++ Printer.pr_lconstr t ++ fnl () ++
			  str "new type := " ++ Printer.pr_lconstr new_t ++ fnl () ++
			  Option.fold_right (fun v _ -> str "old value := " ++ Printer.pr_lconstr v ++ fnl ()) v (mt ()) ++
			  Option.fold_right (fun v _ -> str "new value := " ++ Printer.pr_lconstr v ++ fnl ()) new_v (mt ())
		       );
	       (Environ.push_named (id,new_v,new_t) env,mkVar id::ctxt)
      )
	(Environ.rel_context new_env)
	~init:(env,[])
    )
  in
  observe (str "new var env := " ++ Printer.pr_named_context_of res);
  res




let rec pattern_to_term_and_type env typ  = function
  | PatVar(loc,Anonymous) -> assert false
  | PatVar(loc,Name id) ->
	mkRVar id
  | PatCstr(loc,constr,patternl,_) ->
      let cst_narg =
	Inductiveops.mis_constructor_nargs_env
	  (Global.env ())
	  constr
      in
      let Inductiveops.IndType(indf,indargs) = 
	try Inductiveops.find_rectype env Evd.empty typ
	with Not_found -> assert false 
      in
      let constructors = Inductiveops.get_constructors env indf in 
      let constructor  = List.find (fun cs -> cs.Inductiveops.cs_cstr = constr) (Array.to_list constructors) in 
      let cs_args_types :types list = List.map (fun (_,_,t) -> t) constructor.Inductiveops.cs_args in 
      let _,cstl = Inductiveops.dest_ind_family indf in 
      let csta = Array.of_list cstl in 
      let implicit_args =
	Array.to_list
	  (Array.init
	     (cst_narg - List.length patternl)
	     (fun i -> Detyping.detype false [] (Termops.names_of_rel_context env) csta.(i))
	  )
      in
      let patl_as_term =
	List.map2 (pattern_to_term_and_type env)  (List.rev cs_args_types)  patternl
      in
      mkRApp(mkRRef(ConstructRef constr),
	     implicit_args@patl_as_term
	    )

(* [build_entry_lc funnames avoid rt] construct the list (in fact a build_entry_return) 
   of constructors corresponding to [rt] when replacing calls to [funnames] by calls to the 
   corresponding graphs. 


   The idea to transform a term [t] into a list of constructors [lc] is the following:
   \begin{itemize} 
   \item if the term is a binder (bind x, body) then first compute [lc'] the list corresponding 
   to [body] and add (bind x. _) to each elements of [lc]
   \item if the term has the form (g t1 ... ... tn) where g does not appears in (fnames) 
   then compute [lc1] ... [lcn] the lists of constructors corresponding to [t1] ... [tn], 
   then combine those lists and [g] as follows~: for each element [c1,...,cn] of [lc1\times...\times lcn], 
   [g c1 ... cn] is an element of [lc]
   \item if the term has the form (f t1 .... tn) where [f] appears in [fnames] then 
   compute [lc1] ... [lcn] the lists of constructors corresponding to [t1] ... [tn], 
   then compute those lists and [f] as follows~: for each element [c1,...,cn] of [lc1\times...\times lcn]
   create a new variable [res] and [forall res, R_f c1 ... cn res] is in [lc]
   \item if the term is a cast just treat its body part
   \item 
   if the term is a match, an if or a lettuple then compute the lists corresponding to each branch of the case 
   and concatenate them (informally, each branch of a match produces a new constructor)
   \end{itemize}
   
   WARNING: The terms constructed here are only USING the rawconstr syntax but are highly bad formed. 
   We must wait to have complete all the current calculi to set the recursive calls. 
   At this point, each term [f t1 ... tn]  (where f appears in [funnames]) is replaced by 
   a pseudo term [forall res, res t1 ... tn, res]. A reconstruction phase is done later. 
   We in fact not create a constructor list since then end of each constructor has not the expected form 
   but only the value of the function 
*)


let rec build_entry_lc env funnames avoid rt  : rawconstr build_entry_return = 
  observe (str " Entering : " ++ Printer.pr_rawconstr rt);
  match rt with 
    | RRef _ | RVar _ | REvar _ | RPatVar _     | RSort _  | RHole _  -> 
	(* do nothing (except changing type of course) *)
	mk_result [] rt avoid 
    | RApp(_,_,_) ->
	let f,args = raw_decompose_app rt in
	let args_res : (rawconstr list) build_entry_return =
	  List.fold_right (* create the arguments lists of constructors and combine them *)
	    (fun arg ctxt_argsl ->
	       let arg_res = build_entry_lc env funnames ctxt_argsl.to_avoid arg in
	       combine_results combine_args arg_res ctxt_argsl
	    )
	    args
	    (mk_result [] [] avoid)
	in
	begin
	  match f with
	    | RVar(_,id) when Idset.mem id funnames ->
		(* if we have [f t1 ... tn] with [f]$\in$[fnames]
		   then we create a fresh variable [res], 
		   add [res] and its "value" (i.e. [res v1 ... vn]) to each 
		   pseudo constructor build for the arguments (i.e. a pseudo context [ctxt] and 
		   a pseudo value "v1 ... vn". 
		   The "value" of this branch is then simply [res]
		*)
		let rt_as_constr = Pretyping.Default.understand Evd.empty env rt in 
		let rt_typ = Typing.type_of env Evd.empty rt_as_constr in 
		let res_raw_type = Detyping.detype false [] (Termops.names_of_rel_context env) rt_typ in
		let res = fresh_id args_res.to_avoid "res" in
		let new_avoid = res::args_res.to_avoid in
		let res_rt = mkRVar res in 
		let new_result = 
		  List.map 
		    (fun arg_res -> 
		       let new_hyps = 
			 [Prod (Name res),res_raw_type;
			  Prod Anonymous,mkRApp(res_rt,(mkRVar id)::arg_res.value)]
		       in
		       {context =  arg_res.context@new_hyps; value = res_rt } 
		    )
		    args_res.result
		in 
		{ result = new_result; to_avoid = new_avoid }
	    | RVar _ | REvar _ | RPatVar _ | RHole _ | RSort _ | RRef _ -> 
		(* if have [g t1 ... tn] with [g] not appearing in [funnames] 
		   then  
		   foreach [ctxt,v1 ... vn] in [args_res] we return  
		   [ctxt, g v1 .... vn]
		*)
		{
		  args_res with 
		    result = 
		    List.map 
		      (fun args_res -> 
			 {args_res with value = mkRApp(f,args_res.value)})
		      args_res.result
		}
	    | RApp _ -> assert false (* we have collected all the app in [raw_decompose_app] *)
       	    | RLetIn(_,n,t,b) -> 
		(* if we have [(let x := v in b) t1 ... tn] , 
		   we discard our work and compute the list of constructor for 
		   [let x = v in (b t1 ... tn)] up to alpha conversion 
		*)
		let new_n,new_b,new_avoid = 
		  match n with 
		    | Name id when List.exists (is_free_in id) args -> 
			(* need to alpha-convert the name *)
			let new_id = Nameops.next_ident_away id avoid in 
			let new_avoid = id:: avoid in
			let new_b = 
			  replace_var_by_term
			    id
			    (RVar(dummy_loc,id)) 
			    b
			in 
			(Name new_id,new_b,new_avoid)
		    | _ -> n,b,avoid
		in
		build_entry_lc 
		  env
		  funnames 
		  avoid
		  (mkRLetIn(new_n,t,mkRApp(new_b,args)))
	    | RCases _ | RLambda _ | RIf _ | RLetTuple _ -> 
		(* we have [(match e1, ...., en with ..... end) t1 tn]
		   we first compute the result from the case and 
		   then combine each of them with each of args one
		*)
		let f_res = build_entry_lc env funnames args_res.to_avoid f in
		combine_results combine_app f_res  args_res
	    | RDynamic _ ->error "Not handled RDynamic" 
	    | RCast(_,b,_) -> 
		(* for an applied cast we just trash the cast part 
		   and restart the work. 

		   WARNING: We need to restart since [b] itself should be an application term
		*)
		build_entry_lc env funnames avoid (mkRApp(b,args))
	    | RRec _ -> error "Not handled RRec"
	    | RRecord _ -> error "Not handled RRecord"
	    | RProd _ -> error "Cannot apply a type"
	end (* end of the application treatement *) 

    | RLambda(_,n,_,t,b) ->
	(* we first compute the list of constructor 
	   corresponding to the body of the function, 
	   then the one corresponding to the type 
	   and combine the two result
	*)
	let t_res = build_entry_lc env funnames avoid t  in
	let new_n = 
	  match n with 
	    | Name _ -> n 
	    | Anonymous -> Name (Indfun_common.fresh_id [] "_x")
	in
	let new_env = raw_push_named (new_n,None,t) env in
	let b_res = build_entry_lc new_env funnames avoid b in
	combine_results (combine_lam new_n) t_res b_res
    | RProd(_,n,_,t,b) ->
	(* we first compute the list of constructor 
	   corresponding to the body of the function, 
	   then the one corresponding to the type 
	   and combine the two result
	*)
	let t_res = build_entry_lc env funnames avoid t in
	let new_env = raw_push_named (n,None,t) env in
	let b_res = build_entry_lc new_env funnames avoid b in
	combine_results (combine_prod n) t_res b_res
    | RLetIn(_,n,v,b) ->
	(* we first compute the list of constructor 
	   corresponding to the body of the function, 
	   then the one corresponding to the value [t] 
	   and combine the two result
	*)
	let v_res = build_entry_lc env funnames avoid v in
	let v_as_constr = Pretyping.Default.understand Evd.empty env v in 
	let v_type = Typing.type_of env Evd.empty v_as_constr in 
	let new_env = 
	  match n with
	      Anonymous -> env
	    | Name id -> Environ.push_named (id,Some v_as_constr,v_type) env 
	in
	let b_res = build_entry_lc new_env funnames avoid b in
	combine_results (combine_letin n) v_res b_res
    | RCases(_,_,_,el,brl) -> 
	(* we create the discrimination function 
	   and treat the case itself 
	*)
	let make_discr = make_discr_match brl in 
	build_entry_lc_from_case env funnames make_discr el brl avoid
    | RIf(_,b,(na,e_option),lhs,rhs) -> 
	let b_as_constr = Pretyping.Default.understand Evd.empty env b in
	let b_typ = Typing.type_of env Evd.empty b_as_constr in 
	let (ind,_) =  
	  try Inductiveops.find_inductive env Evd.empty b_typ 
	  with Not_found -> 
	    errorlabstrm "" (str "Cannot find the inductive associated to " ++ 
			       Printer.pr_rawconstr b ++ str " in " ++
			       Printer.pr_rawconstr rt ++ str ". try again with a cast")
	in
	let case_pats = build_constructors_of_type ind [] in 
	assert (Array.length case_pats = 2);
	let brl =
	  list_map_i
	    (fun i x -> (dummy_loc,[],[case_pats.(i)],x))
	    0
	    [lhs;rhs]
	in
	let match_expr =
	  mkRCases(None,[(b,(Anonymous,None))],brl)
	in
	(* 		Pp.msgnl (str "new case := " ++ Printer.pr_rawconstr match_expr); *)
	build_entry_lc env funnames avoid match_expr
    | RLetTuple(_,nal,_,b,e) ->  
	begin
	  let nal_as_rawconstr =
	    List.map
	      (function
		   Name id -> mkRVar id
		 | Anonymous -> mkRHole ()
	      )
	      nal
	  in
	  let b_as_constr = Pretyping.Default.understand Evd.empty env b in
	  let b_typ = Typing.type_of env Evd.empty b_as_constr in 
	  let (ind,_) = 
	    try Inductiveops.find_inductive env Evd.empty b_typ 
	    with Not_found -> 
	      errorlabstrm "" (str "Cannot find the inductive associated to " ++ 
				 Printer.pr_rawconstr b ++ str " in " ++
				 Printer.pr_rawconstr rt ++ str ". try again with a cast")
	  in
	  let case_pats = build_constructors_of_type ind nal_as_rawconstr in 
	  assert (Array.length case_pats = 1);
	  let br =
	    (dummy_loc,[],[case_pats.(0)],e)
	  in
	  let match_expr = mkRCases(None,[b,(Anonymous,None)],[br]) in
	  build_entry_lc env funnames avoid match_expr

	end
    | RRec _ -> error "Not handled RRec"
    | RRecord _ -> error "Not handled RRecord"
    | RCast(_,b,_) -> 
	build_entry_lc env funnames  avoid b
    | RDynamic _ -> error "Not handled RDynamic"
and build_entry_lc_from_case env funname make_discr
    (el:tomatch_tuples)
    (brl:Rawterm.cases_clauses) avoid : 
    rawconstr build_entry_return = 
  match el with 
    | [] -> assert false (* this case correspond to match <nothing> with .... !*) 
    | el -> 
	(* this case correspond to 
	   match el with brl end
	   we first compute the list of lists corresponding to [el] and 
	   combine them . 
	   Then for each elemeent of the combinations, 
	   we compute the result we compute one list per branch in [brl] and 
	   finally we just concatenate those list 
	*)
	let case_resl = 
	    List.fold_right
	    (fun (case_arg,_) ctxt_argsl ->
	       let arg_res = build_entry_lc env funname avoid case_arg  in
	       combine_results combine_args arg_res ctxt_argsl
	    )
	    el
	      (mk_result [] [] avoid)
	in
	(****** The next works only if the match is not dependent ****)
	let types = 
	  List.map (fun (case_arg,_) -> 
		      let case_arg_as_constr = Pretyping.Default.understand Evd.empty env case_arg in 
		      Typing.type_of env Evd.empty case_arg_as_constr
		   ) el
	in
	let results =
	  List.map 
	    (build_entry_lc_from_case_term
	       env types
	       funname (make_discr (* (List.map fst el) *))
	       []  brl 
	       case_resl.to_avoid) 
	    case_resl.result 
	in 
	{ 
	  result = List.concat (List.map (fun r -> r.result) results);
	  to_avoid = 
	    List.fold_left (fun acc r -> list_union acc r.to_avoid) [] results
	} 

and build_entry_lc_from_case_term env types funname make_discr patterns_to_prevent brl avoid
    matched_expr =
  match brl with
    | [] -> (* computed_branches  *) {result = [];to_avoid = avoid}
    | br::brl' ->
	(* alpha convertion to prevent name clashes *)
	let _,idl,patl,return = alpha_br avoid br in
	let new_avoid  = idl@avoid in 	(* for now we can no more use idl as an indentifier *)
	(* building a list of precondition stating that we are not in this branch 
	   (will be used in the following recursive calls)
	*)
	let new_env = List.fold_right2 add_pat_variables patl types env in 
	let not_those_patterns : (identifier list -> rawconstr -> rawconstr) list = 
	  List.map2
	    (fun pat typ -> 
	       fun avoid pat'_as_term -> 
		 let renamed_pat,_,_ = alpha_pat avoid pat in
		 let pat_ids = get_pattern_id renamed_pat  in 
		 let env_with_pat_ids = add_pat_variables pat typ new_env in 
		   List.fold_right 
		   (fun id acc -> 		 
		      let typ_of_id = Typing.type_of env_with_pat_ids Evd.empty (mkVar id) in 
		      let raw_typ_of_id = 
			Detyping.detype false [] (Termops.names_of_rel_context env_with_pat_ids) typ_of_id
		      in
		      mkRProd (Name id,raw_typ_of_id,acc))
		   pat_ids
		   (raw_make_neq pat'_as_term (pattern_to_term renamed_pat))
	    )
	    patl
	    types
	in
	(* Checking if we can be in this branch 
	   (will be used in the following recursive calls)
	*)	   
	let unify_with_those_patterns : (cases_pattern -> bool*bool) list =
	  List.map 
	    (fun pat pat' -> are_unifiable pat pat',eq_cases_pattern pat pat') 
	    patl
	in
	(* 
	   we first compute the other branch result (in ordrer to keep the order of the matching 
	   as much as possible)
	*)
	let brl'_res =
	  build_entry_lc_from_case_term
	    env 
	    types
	    funname
	    make_discr
	    ((unify_with_those_patterns,not_those_patterns)::patterns_to_prevent)
	    brl'
	    avoid
	    matched_expr
	in
	(* We now create the precondition of this branch i.e.

	   1- the list of variable appearing in the different patterns of this branch and 
	      the list of equation stating than el = patl (List.flatten ...)
	   2- If there exists a previous branch which pattern unify with the one of this branch 
              then a discrimination precond stating that we are not in a previous branch (if List.exists ...)
	*)
      	let those_pattern_preconds =
	  (List.flatten
	    (
	      list_map3
	      (fun pat e typ_as_constr ->
		 let this_pat_ids = ids_of_pat pat in 
		 let typ = Detyping.detype false [] (Termops.names_of_rel_context new_env) typ_as_constr in
		 let pat_as_term = pattern_to_term pat in
		 List.fold_right 
		   (fun id  acc -> 
		      if Idset.mem id this_pat_ids 
		      then (Prod (Name id),
		      let typ_of_id = Typing.type_of new_env Evd.empty (mkVar id) in 
		      let raw_typ_of_id = 
			Detyping.detype false [] (Termops.names_of_rel_context new_env) typ_of_id
		      in
		      raw_typ_of_id
			   )::acc
		      else acc
			
		   )
		   idl
		   [(Prod Anonymous,raw_make_eq ~typ pat_as_term e)]
	      )
	      patl
	      matched_expr.value
	      types
	  )
	  )
	  @
	  (if List.exists (function (unifl,_) ->
			     let (unif,_) = 
			       List.split (List.map2 (fun x y -> x y) unifl patl)
			     in
			     List.for_all (fun x -> x) unif) patterns_to_prevent
	   then 
	     let i = List.length patterns_to_prevent in 
	     let pats_as_constr = List.map2 (pattern_to_term_and_type new_env) types patl in
	     [(Prod Anonymous,make_discr pats_as_constr i  )]
	   else 
	     []
	  )
	in
	(* We compute the result of the value returned by the branch*)
	let return_res = build_entry_lc new_env funname new_avoid return in
	(* and combine it with the preconds computed for this branch *)
	let this_branch_res =
	  List.map
	    (fun res  ->
	       { context = matched_expr.context@those_pattern_preconds@res.context ;
		 value = res.value}
	    )
	    return_res.result
	in
	{ brl'_res with result = this_branch_res@brl'_res.result }
	  
	  
let is_res id = 
  try
    String.sub (string_of_id id) 0 3 = "res"
  with Invalid_argument _ -> false 

(* 
   The second phase which reconstruct the real type of the constructor. 
   rebuild the raw constructors expression. 
   eliminates some meaningless equalities, applies some rewrites......
*)
let rec rebuild_cons nb_args relname args crossed_types depth rt = 
  match rt with 
    | RProd(_,n,k,t,b) -> 
	let not_free_in_t id = not (is_free_in id t) in 
	let new_crossed_types = t::crossed_types in 
	begin
	  match t with 
	    | RApp(_,(RVar(_,res_id) as res_rt),args') when is_res res_id ->
		begin
		  match args' with 
		    | (RVar(_,this_relname))::args' -> 
			let new_b,id_to_exclude =  
			  rebuild_cons 
			    nb_args relname
			    args new_crossed_types
			    (depth + 1) b
			in 
			(*i The next call to mk_rel_id is valid since we are constructing the graph
			  Ensures by: obvious
			  i*) 

			let new_t = 
			  mkRApp(mkRVar(mk_rel_id this_relname),args'@[res_rt]) 
			in mkRProd(n,new_t,new_b),
			Idset.filter not_free_in_t id_to_exclude
		    | _ -> (* the first args is the name of the function! *)
			assert false 
		end
	    | RApp(_,RRef(_,eq_as_ref),[_;RVar(_,id);rt]) 
		when  eq_as_ref = Lazy.force Coqlib.coq_eq_ref  && n = Anonymous
		  -> 
		let is_in_b = is_free_in id b in
		let _keep_eq = 
		  not (List.exists (is_free_in id) args) || is_in_b  || 
		    List.exists (is_free_in id) crossed_types 
		in 
		let new_args = List.map (replace_var_by_term id rt) args in 
		let subst_b = 
		  if is_in_b then b else  replace_var_by_term id rt b 
		in 
		let new_b,id_to_exclude =  
		  rebuild_cons 
		    nb_args relname
		    new_args new_crossed_types
		    (depth + 1) subst_b
		in 
		mkRProd(n,t,new_b),id_to_exclude
		  (* J.F:. keep this comment  it explain how to remove some meaningless equalities 
		     if keep_eq then
		     mkRProd(n,t,new_b),id_to_exclude
		     else new_b, Idset.add id id_to_exclude
		  *)
	    | _ -> 
		let new_b,id_to_exclude =  
		  rebuild_cons 
		    nb_args relname
		    args new_crossed_types
		    (depth + 1) b
		in 
		match n with
		  | Name id when Idset.mem id id_to_exclude && depth >= nb_args ->
		      new_b,Idset.remove id 
			(Idset.filter not_free_in_t id_to_exclude)
		  | _ -> mkRProd(n,t,new_b),Idset.filter not_free_in_t id_to_exclude
	end
    | RLambda(_,n,k,t,b) ->
	begin
	  let not_free_in_t id = not (is_free_in id t) in
	  let new_crossed_types = t :: crossed_types in
	  match n with
	    | Name id ->
		let new_b,id_to_exclude = 
		  rebuild_cons 
		    nb_args relname
		    (args@[mkRVar id])new_crossed_types
		    (depth + 1 ) b 
		in
		if Idset.mem id id_to_exclude && depth >= nb_args
		then 
		  new_b, Idset.remove id (Idset.filter not_free_in_t id_to_exclude)
		else
		  RProd(dummy_loc,n,k,t,new_b),Idset.filter not_free_in_t id_to_exclude
	    | _ -> anomaly "Should not have an anonymous function here" 
		(* We have renamed all the anonymous functions during alpha_renaming phase *)
	  
	end
    | RLetIn(_,n,t,b) -> 
	begin
	  let not_free_in_t id = not (is_free_in id t) in 
	  let new_b,id_to_exclude = 
	    rebuild_cons 
	      nb_args relname
	      args (t::crossed_types)
	      (depth + 1 ) b in
	  match n with 
	    | Name id when Idset.mem id id_to_exclude && depth >= nb_args  -> 
		new_b,Idset.remove id (Idset.filter not_free_in_t id_to_exclude)
	    | _ -> RLetIn(dummy_loc,n,t,new_b),
		Idset.filter not_free_in_t id_to_exclude
	end
    | RLetTuple(_,nal,(na,rto),t,b) -> 
	assert (rto=None);
	begin
	  let not_free_in_t id = not (is_free_in id t) in 
	  let new_t,id_to_exclude' = 
	    rebuild_cons 
	      nb_args
	      relname 
	      args (crossed_types) 
	      depth t 
	  in
	  let new_b,id_to_exclude = 
	    rebuild_cons 
	      nb_args relname
	      args (t::crossed_types) 
	      (depth + 1) b 
	  in
(* 	  match n with  *)
(* 	    | Name id when Idset.mem id id_to_exclude ->  *)
(* 		new_b,Idset.remove id (Idset.filter not_free_in_t id_to_exclude) *)
(* 	    | _ -> *)
	  RLetTuple(dummy_loc,nal,(na,None),t,new_b),
		Idset.filter not_free_in_t (Idset.union id_to_exclude id_to_exclude')

	end

    | _ -> mkRApp(mkRVar  relname,args@[rt]),Idset.empty


(* debuging wrapper *)
let rebuild_cons nb_args relname args crossed_types rt = 
(*   observennl  (str "rebuild_cons : rt := "++ pr_rawconstr rt ++  *)
(* 		 str "nb_args := " ++ str (string_of_int nb_args)); *)
  let res = 
    rebuild_cons nb_args relname args crossed_types 0 rt 
  in
(*   observe (str " leads to "++ pr_rawconstr (fst res)); *)
  res


(* naive implementation of parameter detection. 

   A parameter is an argument which is only preceded by parameters and whose 
   calls are all syntaxically equal. 

   TODO: Find a valid way to deal with implicit arguments here! 
*)
let rec compute_cst_params relnames params = function 
  | RRef _ | RVar _ | REvar _ | RPatVar _ -> params
  | RApp(_,RVar(_,relname'),rtl) when Idset.mem relname' relnames ->
      compute_cst_params_from_app [] (params,rtl)
  | RApp(_,f,args) -> 
      List.fold_left (compute_cst_params relnames) params (f::args)
  | RLambda(_,_,_,t,b) | RProd(_,_,_,t,b) | RLetIn(_,_,t,b) | RLetTuple(_,_,_,t,b) -> 
      let t_params = compute_cst_params relnames params t in 
      compute_cst_params relnames t_params b
  | RCases _ ->
      params  (* If there is still cases at this point they can only be 
		 discriminitation ones *)
  | RSort _ -> params
  | RHole _ -> params
  | RIf _ | RRecord _ | RRec _ | RCast _ | RDynamic _  ->
      raise (UserError("compute_cst_params", str "Not handled case"))
and compute_cst_params_from_app acc (params,rtl) = 
  match params,rtl with 
    | _::_,[] -> assert false (* the rel has at least nargs + 1 arguments ! *)
    | ((Name id,_,is_defined) as param)::params',(RVar(_,id'))::rtl' 
	when id_ord id id' == 0 && not is_defined -> 
	compute_cst_params_from_app (param::acc) (params',rtl')
    | _  -> List.rev acc 
   
let compute_params_name relnames (args : (Names.name * Rawterm.rawconstr * bool) list array) csts =  
  let rels_params = 
    Array.mapi 
      (fun i args -> 
	 List.fold_left 
	   (fun params (_,cst) -> compute_cst_params relnames params cst) 
	   args
	   csts.(i)
      )
      args
  in 
  let l = ref [] in 
  let _ = 
    try 
      list_iter_i
	(fun i ((n,nt,is_defined) as param) -> 
	   if array_for_all 
	     (fun l -> 
		let (n',nt',is_defined') = List.nth l i in 
		n = n' && Topconstr.eq_rawconstr nt nt' && is_defined = is_defined')
	     rels_params
	   then 
	     l := param::!l
	) 
	rels_params.(0)
    with _ -> 
      ()
  in 
  List.rev !l

let rec rebuild_return_type rt = 
  match rt with 
    | Topconstr.CProdN(loc,n,t') -> 
	Topconstr.CProdN(loc,n,rebuild_return_type t') 
    | Topconstr.CArrow(loc,t,t') -> 
	Topconstr.CArrow(loc,t,rebuild_return_type t')
    | Topconstr.CLetIn(loc,na,t,t') -> 
	Topconstr.CLetIn(loc,na,t,rebuild_return_type t') 
    | _ -> Topconstr.CArrow(dummy_loc,rt,Topconstr.CSort(dummy_loc,RType None))


let do_build_inductive 
    funnames (funsargs: (Names.name * rawconstr * bool) list list)  
    returned_types 
    (rtl:rawconstr list) =
  let _time1 = System.get_time () in
(*   Pp.msgnl (prlist_with_sep fnl Printer.pr_rawconstr rtl); *)
  let funnames_as_set = List.fold_right Idset.add funnames Idset.empty in
  let funnames = Array.of_list funnames in  
  let funsargs = Array.of_list funsargs in 
  let returned_types = Array.of_list returned_types in
  (* alpha_renaming of the body to prevent variable capture during manipulation *)
  let rtl_alpha = List.map (function rt ->  expand_as (alpha_rt [] rt)) rtl in
  let rta = Array.of_list rtl_alpha in
  (*i The next call to mk_rel_id is valid since we are constructing the graph
    Ensures by: obvious
    i*) 
  let relnames = Array.map mk_rel_id funnames in
  let relnames_as_set = Array.fold_right Idset.add relnames Idset.empty in 
  (* Construction of the pseudo constructors *)
  let env = 
    Array.fold_right 
      (fun id env -> 
	 Environ.push_named (id,None,Typing.type_of env Evd.empty (Tacinterp.constr_of_id env id))  env
      )
      funnames 
      (Global.env ())
  in      
  let resa = Array.map (build_entry_lc env  funnames_as_set []) rta in 
  (* and of the real constructors*)
  let constr i res = 
    List.map 
      (function result (* (args',concl') *) -> 
	 let rt = compose_raw_context result.context result.value in 
	 let nb_args = List.length funsargs.(i) in 
	 (*  with_full_print (fun rt -> Pp.msgnl (str "raw constr " ++ pr_rawconstr rt)) rt; *)
	 fst (
	   rebuild_cons nb_args relnames.(i)
	     []
	     []
	     rt 
	 )
      ) 
      res.result 
  in 
  (* adding names to constructors  *)
 let next_constructor_id = ref (-1) in 
  let mk_constructor_id i = 
    incr next_constructor_id;
    (*i The next call to mk_rel_id is valid since we are constructing the graph
      Ensures by: obvious
      i*) 
    id_of_string ((string_of_id (mk_rel_id funnames.(i)))^"_"^(string_of_int !next_constructor_id))
  in
  let rel_constructors i rt : (identifier*rawconstr) list = 
    next_constructor_id := (-1);
    List.map (fun constr -> (mk_constructor_id i),constr) (constr i rt)
  in
  let rel_constructors = Array.mapi rel_constructors resa in
  (* Computing the set of parameters if asked *)
  let rels_params = compute_params_name relnames_as_set funsargs  rel_constructors in
  let nrel_params = List.length rels_params in
  let rel_constructors = (* Taking into account the parameters in constructors *)
    Array.map (List.map 
    (fun (id,rt) -> (id,snd (chop_rprod_n nrel_params rt))))
    rel_constructors
  in
  let rel_arity i funargs =  (* Reduilding arities (with parameters) *)
    let rel_first_args :(Names.name * Rawterm.rawconstr * bool ) list  = 
      (snd (list_chop nrel_params funargs))
    in 
    List.fold_right
      (fun (n,t,is_defined) acc -> 
	 if is_defined
	 then 
	   Topconstr.CLetIn(dummy_loc,(dummy_loc, n),Constrextern.extern_rawconstr Idset.empty t,
			    acc)
	 else
	   Topconstr.CProdN
	   (dummy_loc,
	   [[(dummy_loc,n)],Topconstr.default_binder_kind,Constrextern.extern_rawconstr Idset.empty t],
	    acc
	   )
      )
      rel_first_args
      (rebuild_return_type returned_types.(i))
  in
  (* We need to lift back our work topconstr but only with all information 
     We mimick a Set Printing All. 
     Then save the graphs and reset Printing options to their primitive values 
  *)
  let rel_arities = Array.mapi rel_arity funsargs in
  let rel_params =  
    List.map 
      (fun (n,t,is_defined) -> 
	 if is_defined 
	 then
	   Topconstr.LocalRawDef((dummy_loc,n), Constrextern.extern_rawconstr Idset.empty t)
	 else
	 Topconstr.LocalRawAssum 
	   ([(dummy_loc,n)], Topconstr.default_binder_kind, Constrextern.extern_rawconstr Idset.empty t)
      )
      rels_params
  in 
  let ext_rels_constructors = 
    Array.map (List.map 
      (fun (id,t) -> 
	 false,((dummy_loc,id),
		Flags.with_option
		  Flags.raw_print
		  (Constrextern.extern_rawtype Idset.empty) ((* zeta_normalize *) t)
	       )
      ))
      (rel_constructors)
  in
  let rel_ind i ext_rel_constructors = 
    ((dummy_loc,relnames.(i)),
    rel_params,
    rel_arities.(i),
    ext_rel_constructors),None
  in
  let ext_rel_constructors = (Array.mapi rel_ind ext_rels_constructors) in 
  let rel_inds = Array.to_list ext_rel_constructors in 
(*   let _ =  *)
(*   Pp.msgnl  (\* observe *\) ( *)
(*       str "Inductive" ++ spc () ++ *)
(* 	prlist_with_sep  *)
(* 	(fun () -> fnl ()++spc () ++ str "with" ++ spc ())  *)
(* 	(function ((_,id),_,params,ar,constr) ->  *)
(* 	   Ppconstr.pr_id id ++ spc () ++  *)
(* 	     Ppconstr.pr_binders params ++ spc () ++ *)
(* 	     str ":" ++ spc () ++  *)
(* 	     Ppconstr.pr_lconstr_expr ar ++ spc () ++ str ":=" ++ *)
(* 	     prlist_with_sep  *)
(* 	     (fun _ -> fnl () ++ spc () ++ str "|" ++ spc ()) *)
(* 	     (function (_,((_,id),t)) ->  *)
(* 		Ppconstr.pr_id id ++ spc () ++ str ":" ++ spc () ++ *)
(* 		  Ppconstr.pr_lconstr_expr t) *)
(* 	     constr *)
(* 	) *)
(* 	rel_inds *)
(*     ) *)
(*   in *)
  let _time2 = System.get_time () in 
  try 
    with_full_print (Flags.silently (Command.build_mutual rel_inds)) true
  with 
    | UserError(s,msg) as e ->
	let _time3 = System.get_time () in
(* 	Pp.msgnl (str "error : "++ str (string_of_float (System.time_difference time2 time3))); *)
	let msg = 		     
	  str "while trying to define"++ spc () ++
	    Ppvernac.pr_vernac (Vernacexpr.VernacInductive(true,rel_inds)) ++ fnl () ++
	    msg
	in
	observe (msg);
	raise e
    | e -> 
	let _time3 = System.get_time () in
(* 	Pp.msgnl (str "error : "++ str (string_of_float (System.time_difference time2 time3))); *)
	let msg = 		     
	  str "while trying to define"++ spc () ++
	    Ppvernac.pr_vernac (Vernacexpr.VernacInductive(true,rel_inds)) ++ fnl () ++
	    Cerrors.explain_exn e
	in
 	observe msg;
	raise e



let build_inductive funnames funsargs returned_types rtl = 
  try 
    do_build_inductive funnames funsargs returned_types rtl
  with e -> raise (Building_graph e)
      

