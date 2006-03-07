open Printer
open Pp
open Names 
open Term
open Rawterm
open Libnames
open Indfun_common
open Util
open Rawtermops


(* type binder_type =  *)
(*   | Lambda  *)
(*   | Prod  *)
(*   | LetIn *)
  
(* type raw_context = (binder_type*name*rawconstr) list *)

type binder_type =
  | Lambda of name 
  | Prod of name 
  | LetIn of name
(*   | LetTuple of name list * name  *)

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
(*       | LetTuple (nal,na) ->  *)
(* 	  RLetTuple(dummy_loc,nal,(na,None),t,acc) *)
  in
  List.fold_right compose_binder
  

(* 
   The main part deals with building a list of raw constructor expressions
   from a rhs of a fixpoint equation. 
   
   
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
(*   | LetTuple(nal,_) ->  *)
(*       map_succeed (function Name id -> id | _ -> failwith "ids_of_binder") nal *)

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

(* let rec replace_var_by_term_in_binder x_id term = function  *)
(*   | [] -> []  *)
(*   | (bt,Name id,t)::l when id_ord id x_id = 0 ->  *)
(*       (bt,Name id,replace_var_by_term x_id term t)::l *)
(*   | (bt,na,t)::l ->  *)
(*       (bt,na,replace_var_by_term x_id term t)::(replace_var_by_term_in_binder x_id term l) *)

(* let rec change_vars_in_binder mapping = function *)
(*   | [] -> [] *)
(*   | (bt,(Name id as na),t)::l when Idmap.mem id mapping -> *)
(*       (bt,na,change_vars mapping t):: l *)
(*   | (bt,na,t)::l -> *)
(*       (bt,na,change_vars mapping t):: *)
(* 	(change_vars_in_binder mapping l) *)

   
(* let alpha_ctxt avoid b = *)
(*   let rec alpha_ctxt = function *)
(*     | [] -> [],b *)
(*     | (bt,n,t)::ctxt -> *)
(* 	let new_ctxt,new_b = alpha_ctxt ctxt in *)
(* 	match n with *)
(* 	  | Name id when List.mem id avoid -> *)
(* 	      let new_id = Nameops.next_ident_away id avoid in *)
(* 	      let mapping = Idmap.add id new_id Idmap.empty in *)
(* 	      (bt,Name new_id,t):: *)
(* 		(change_vars_in_binder mapping new_ctxt), *)
(* 	      change_vars mapping new_b *)
(* 	  | _ -> (bt,n,t)::new_ctxt,new_b *)
(*   in *)
(*   alpha_ctxt *)
let apply_args ctxt body args = 
  let need_convert_id avoid id = 
    List.exists (is_free_in id) args || List.mem id avoid 
  in 
  let need_convert avoid  bt =  
    List.exists (need_convert_id avoid) (ids_of_binder bt)
  in
(*   let add_name na avoid =  *)
(*     match na with  *)
(*       | Anonymous -> avoid  *)
(*       | Name id -> id::avoid  *)
(*   in *)
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
(*       | LetTuple (nal,na) ->  *)
(* 	  let rev_new_nal,mapping,new_avoid =  *)
(* 	    List.fold_left *)
(* 	      (fun (nal,mapping,(avoid:identifier list)) na ->  *)
(* 		 let new_na,new_mapping,new_avoid = next_name_away na mapping avoid in *)
(* 		 (new_na::nal,new_mapping,new_avoid) *)
(* 	      ) *)
(* 	      ([],Idmap.empty,avoid) *)
(* 	      nal *)
(* 	  in  *)
(* 	  (LetTuple(List.rev rev_new_nal,na),mapping,new_avoid) *)
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

(* let combine_tuple nal na b in_e =  *)
(*   {  *)
(*     context = b.context@(LetTuple(nal,na),b.value)::in_e.context;  *)
(*     value = in_e.value *)
(*   } *)

let mk_result ctxt value avoid = 
  { 
    result = 
      [{context = ctxt;
	value = value}]
	;
    to_avoid = avoid
  }


let make_discr_match_el  = 
  List.map (fun e -> (e,(Anonymous,None)))

let coq_True_ref = 
  lazy  (Coqlib.gen_reference "" ["Init";"Logic"] "True")

let coq_False_ref = 
  lazy  (Coqlib.gen_reference "" ["Init";"Logic"] "False")

let make_discr_match_brl i = 
  list_map_i 
    (fun j (_,idl,patl,_) -> 
       if j=i
       then (dummy_loc,idl,patl, mkRRef (Lazy.force coq_True_ref))
       else (dummy_loc,idl,patl, mkRRef (Lazy.force coq_False_ref))
    )
    0 
    
let make_discr_match brl = 
  fun el i -> 
  mkRCases(None,
	   make_discr_match_el el,
	   make_discr_match_brl i brl)
  

let rec build_entry_lc funnames avoid rt  : rawconstr build_entry_return = 
(*   Pp.msgnl (str " Entering : " ++ Printer.pr_rawconstr rt); *)
  match rt with 
    | RRef _ | RVar _ | REvar _ | RPatVar _     | RSort _  | RHole _  -> 
	mk_result [] rt avoid
    | RApp(_,_,_) ->
	let f,args = raw_decompose_app rt in
	let args_res : (rawconstr list) build_entry_return =
	  List.fold_right
	    (fun arg ctxt_argsl ->
	       let arg_res = build_entry_lc  funnames ctxt_argsl.to_avoid arg in
	       combine_results combine_args  arg_res ctxt_argsl
	    )
	    args
	    (mk_result [] [] avoid)
	in
	begin
	  match f with
	    | RVar(_,id) when Idset.mem id funnames ->
		let res = fresh_id args_res.to_avoid "res" in
		let new_avoid = res::args_res.to_avoid in
		let res_rt = mkRVar res in 
		let new_result = 
		  List.map 
		    (fun arg_res -> 
		       let new_hyps = 
			 [Prod (Name res),mkRHole ();
			  Prod Anonymous,mkRApp(res_rt,(mkRVar id)::arg_res.value)]
		       in
		       {context =  arg_res.context@new_hyps; value = res_rt } 
		    )
		    args_res.result
		in 
		{ result = new_result; to_avoid = new_avoid }
	    | RVar _ | REvar _ | RPatVar _ | RHole _ | RSort _ | RRef _ -> 
		{
		  args_res with 
		    result = 
		    List.map 
		      (fun args_res -> 
			 {args_res with value = mkRApp(f,args_res.value)})
		      args_res.result
		}
	    | RApp _ -> assert false (* we have collected all the app *)
       	    | RLetIn(_,n,t,b) -> 
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
		  funnames 
		  avoid
		  (mkRLetIn(new_n,t,mkRApp(new_b,args)))
	    | RCases _ | RLambda _  -> 
		let f_res = build_entry_lc funnames  args_res.to_avoid f in
		combine_results combine_app f_res  args_res
	    | RDynamic _ ->error "Not handled RDynamic"
	    | RCast _ -> error "Not handled RCast"
	    | RRec _ -> error "Not handled RRec"
	    | RIf _ -> error "Not handled RIf"
	    | RLetTuple _ -> error "Not handled RLetTuple"
	    | RProd _ -> error "Cannot apply a type"
	end
    | RLambda(_,n,t,b) ->
	let b_res = build_entry_lc funnames  avoid b in
	let t_res = build_entry_lc funnames avoid t  in
	combine_results (combine_lam n) t_res b_res
    | RProd(_,n,t,b) ->
	let b_res = build_entry_lc funnames avoid b in
	let t_res = build_entry_lc funnames avoid t in
	combine_results (combine_prod n) t_res b_res
    | RLetIn(_,n,t,b) ->
	let b_res = build_entry_lc funnames avoid b in
	let t_res = build_entry_lc funnames avoid t in
	combine_results (combine_letin n) t_res b_res
    | RCases(_,_,el,brl) -> 
	let make_discr = make_discr_match brl in 
	build_entry_lc_from_case funnames make_discr el brl avoid
    | RIf _ -> error "Not handled RIf"
    | RLetTuple _ -> error "Not handled RLetTuple"
    | RRec _ -> error "Not handled RRec"
    | RCast _ -> error "Not handled RCast"
    | RDynamic _ -> error "Not handled RDynamic"
and build_entry_lc_from_case funname make_discr
    (el:(Rawterm.rawconstr *
	   (Names.name * (loc * Names.inductive * Names.name list) option) )
       list)
    (brl:(loc * identifier list * cases_pattern list * rawconstr) list) avoid : 
    rawconstr build_entry_return = 
  match el with 
    | [] -> assert false (* matched on Nothing !*) 
    | el -> 
	let case_resl = 
	    List.fold_right
	    (fun (case_arg,_) ctxt_argsl ->
	       let arg_res = build_entry_lc funname avoid case_arg  in
	       combine_results combine_args arg_res ctxt_argsl
	    )
	    el
	      (mk_result [] [] avoid)
	in
	let results =
	  List.map 
	    (build_entry_lc_from_case_term funname make_discr []  brl case_resl.to_avoid) 
	    case_resl.result 
	in 
	{ 
	  result = List.concat (List.map (fun r -> r.result) results);
	  to_avoid = 
	    List.fold_left (fun acc r -> list_union acc r.to_avoid) [] results
	} 

and build_entry_lc_from_case_term funname make_discr patterns_to_prevent brl avoid
    matched_expr =
  match brl with
    | [] -> (* computed_branches  *) {result = [];to_avoid = avoid}
    | br::brl' ->
	let _,idl,patl,return = alpha_br avoid br in
	let new_avoid  = idl@avoid in 
(* 	let e_ctxt,el = (matched_expr.context,matched_expr.value) in *)
(*  	if  (List.length patl) <> (List.length el) *)
(* 	then error ("Pattern matching on product: not yet implemented"); *)
	let not_those_patterns : (identifier list -> rawconstr -> rawconstr) list = 
	  List.map 
	    (fun pat -> 
	       fun avoid pat'_as_term -> 
		 let renamed_pat,_,_ = alpha_pat avoid pat in
		 let pat_ids = get_pattern_id renamed_pat  in 
		 List.fold_right 
		   (fun id acc -> mkRProd (Name id,mkRHole (),acc))
		   pat_ids
		   (raw_make_neq pat'_as_term (pattern_to_term renamed_pat))
	    )
	    patl
	in
	let unify_with_those_patterns : (cases_pattern -> bool*bool) list =
	  List.map 
	    (fun pat pat' -> are_unifiable pat pat',eq_cases_pattern pat pat') 
	    patl
	in
	let brl'_res =
	  build_entry_lc_from_case_term
	    funname
	    make_discr
	    ((unify_with_those_patterns,not_those_patterns)::patterns_to_prevent)
	    brl'
	    avoid
	    matched_expr
	in
	let ids = List.map (fun id -> Prod (Name id),mkRHole ()) idl in 
      	let those_pattern_preconds =
	  (
	    List.map2
	      (fun pat e -> 
		 let pat_as_term = pattern_to_term pat in 
		 (Prod Anonymous,raw_make_eq pat_as_term e)
	      )
	      patl
	      matched_expr.value
	  )
	  @
	    ( if List.exists (function (unifl,neql) -> 
		let (unif,eqs) = 
		  List.split (List.map2 (fun x y -> x y) unifl patl)
		in
		List.for_all (fun x -> x) unif) patterns_to_prevent
	      then 
		let i = List.length patterns_to_prevent in 
		[(Prod Anonymous,make_discr (List.map pattern_to_term patl) i  )]
	      else 
		[]
	      )
	in
	let return_res = build_entry_lc funname new_avoid return in
	let this_branch_res =
	  List.map
	    (fun res  ->
	       { context = 
		   matched_expr.context@ids@those_pattern_preconds@res.context ;
		 value = res.value}
	    )
	    return_res.result
	in
	{ brl'_res with result = this_branch_res@brl'_res.result }

	  
let is_res id = 
  try
    String.sub (string_of_id id) 0 3 = "res"
  with Invalid_argument _ -> false 

(* rebuild the raw constructors expression. 
   eliminates some meaningless equality, applies some rewrites......
*)
let rec rebuild_cons relname args crossed_types rt = 
  match rt with 
    | RProd(_,n,t,b) -> 
	let not_free_in_t id = not (is_free_in id t) in 
	let new_crossed_types = t::crossed_types in 
	begin
	  match t with 
	    | RApp(_,(RVar(_,res_id) as res_rt),args') when is_res res_id ->
		begin
		  match args' with 
		    | (RVar(_,this_relname))::args' -> 
			let new_b,id_to_exclude =  rebuild_cons relname args new_crossed_types b in 
			let new_t = 
			  mkRApp(mkRVar(mk_rel_id this_relname),args'@[res_rt]) 
			in mkRProd(n,new_t,new_b),
			Idset.filter not_free_in_t id_to_exclude
		    | _ -> (* the first args is the name of the function! *)
			assert false 
		end
	    | RApp(_,RRef(_,eq_as_ref),[_;RVar(_,id);rt]) 
		when  eq_as_ref = Lazy.force Coqlib.coq_eq_ref  
		  -> 
		let is_in_b = is_free_in id b in
		let keep_eq = 
		  not (List.exists (is_free_in id) args) || is_in_b  || 
		    List.exists (is_free_in id) crossed_types 
		in 
		let new_args = List.map (replace_var_by_term id rt) args in 
		let subst_b = 
		  if is_in_b then b else  replace_var_by_term id rt b 
		in 
		let new_b,id_to_exclude =  rebuild_cons relname new_args new_crossed_types subst_b in 
		if keep_eq then mkRProd(n,t,new_b),id_to_exclude 
		else new_b, Idset.add id id_to_exclude
	    | _ -> 
		let new_b,id_to_exclude =  rebuild_cons relname args new_crossed_types b in 
		match n with
		  | Name id when Idset.mem id id_to_exclude ->
		      new_b,Idset.remove id 
			(Idset.filter not_free_in_t id_to_exclude)
		  | _ -> mkRProd(n,t,new_b),Idset.filter not_free_in_t id_to_exclude
	end
    | RLambda(_,n,t,b) ->
	begin
	  let not_free_in_t id = not (is_free_in id t) in 
	  let new_crossed_types = t :: crossed_types in 
	  let new_b,id_to_exclude = rebuild_cons relname args new_crossed_types b in
	  match n with
	    | Name id when Idset.mem id id_to_exclude ->
		new_b,
		Idset.remove id (Idset.filter not_free_in_t id_to_exclude)
	    | _ -> 
		RProd(dummy_loc,n,t,new_b),Idset.filter not_free_in_t id_to_exclude
	end
    | RLetIn(_,n,t,b) -> 
	begin
	  let not_free_in_t id = not (is_free_in id t) in 
	  let new_b,id_to_exclude = 
	    rebuild_cons relname args (t::crossed_types) b in
	  match n with 
	    | Name id when Idset.mem id id_to_exclude -> 
		new_b,Idset.remove id (Idset.filter not_free_in_t id_to_exclude)
	    | _ -> RLetIn(dummy_loc,n,t,new_b),
		Idset.filter not_free_in_t id_to_exclude
	end
    | RLetTuple(_,nal,(na,rto),t,b) -> 
	assert (rto=None);
	begin
	  let not_free_in_t id = not (is_free_in id t) in 
	  let new_t,id_to_exclude' = 
	    rebuild_cons relname args (crossed_types) t 
	  in
	  let new_b,id_to_exclude = 
	    rebuild_cons relname args (t::crossed_types) b 
	  in
(* 	  match n with  *)
(* 	    | Name id when Idset.mem id id_to_exclude ->  *)
(* 		new_b,Idset.remove id (Idset.filter not_free_in_t id_to_exclude) *)
(* 	    | _ -> *)
	  RLetTuple(dummy_loc,nal,(na,None),t,new_b),
		Idset.filter not_free_in_t (Idset.union id_to_exclude id_to_exclude')

	end

    | _ -> mkRApp(mkRVar  relname,args@[rt]),Idset.empty



let rec compute_cst_params relnames params = function 
  | RRef _ | RVar _ | REvar _ | RPatVar _ -> params
  | RApp(_,RVar(_,relname'),rtl) when Idset.mem relname' relnames ->
      compute_cst_params_from_app [] (params,rtl)
  | RApp(_,f,args) -> 
      List.fold_left (compute_cst_params relnames) params (f::args)
  | RLambda(_,_,t,b) | RProd(_,_,t,b) | RLetIn(_,_,t,b) | RLetTuple(_,_,_,t,b) -> 
      let t_params = compute_cst_params relnames params t in 
      compute_cst_params relnames t_params b
  | RCases _ -> params  (* If there is still cases at this point they can only be 
			discriminitation ones *)
  | RSort _ -> params
  | RHole _ -> params
  | RIf _ | RRec _ | RCast _ | RDynamic _  ->
      raise (UserError("compute_cst_params", str "Not handled case"))
and compute_cst_params_from_app acc (params,rtl) = 
  match params,rtl with 
    | _::_,[] -> assert false (* the rel has at least nargs + 1 arguments ! *)
    | ((Name id,_) as param)::params',(RVar(_,id'))::rtl' 
	when id_ord id id' == 0 -> 
	compute_cst_params_from_app (param::acc) (params',rtl')
    | _  -> List.rev acc 
   
let compute_params_name relnames args csts =  
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
	(fun i ((n,nt) as param) -> 
	   if array_for_all 
	     (fun l -> 
		let (n',nt') = List.nth l i in 
		n = n' && Topconstr.eq_rawconstr nt nt')
	     rels_params
	   then 
	     l := param::!l
	) 
	rels_params.(0)
    with _ -> 
      ()
  in 
  List.rev !l



let build_inductive parametrize funnames funsargs  returned_types (rtl:rawconstr list) =
  let funnames_as_set = List.fold_right Idset.add funnames Idset.empty in
  let funnames = Array.of_list funnames in  
  let funsargs = Array.of_list funsargs in 
  let returned_types = Array.of_list returned_types in
  let rtl_alpha = List.map (function rt ->  (alpha_rt [] rt) ) rtl in
  let rta = Array.of_list rtl_alpha in
  let relnames = Array.map mk_rel_id funnames in
  let relnames_as_set = Array.fold_right Idset.add relnames Idset.empty in 
  let resa = Array.map (build_entry_lc funnames_as_set []) rta in 
  let constr i res = 
    List.map 
      (function result (* (args',concl') *) -> 
	 let rt = compose_raw_context result.context result.value in 
(* 	 Pp.msgnl (str "raw constr " ++ pr_rawconstr rt); *)
	 fst (
	   rebuild_cons relnames.(i)
	     (List.map (function 
			    (Anonymous,_) -> mkRVar(fresh_id res.to_avoid "x__") 
			  | Name id, _ -> mkRVar id
		       )
		funsargs.(i)) 
	     []
	     rt 
	 )
      ) 
      res.result 
  in 
  let next_constructor_id = ref (-1) in 
  let mk_constructor_id i = 
    incr next_constructor_id;
    id_of_string ((string_of_id (mk_rel_id funnames.(i)))^"_"^(string_of_int !next_constructor_id))
  in
  let rel_constructors i rt : (identifier*rawconstr) list = 
    List.map (fun constr -> (mk_constructor_id i),constr) (constr i rt)
  in
  let rel_constructors = Array.mapi rel_constructors resa in
  let rels_params = 
    if parametrize 
    then
      compute_params_name relnames_as_set funsargs  rel_constructors 
    else []
  in
  let nrel_params = List.length rels_params in
  let rel_constructors = 
    Array.map (List.map 
    (fun (id,rt) -> (id,snd (chop_rprod_n nrel_params rt))))
    rel_constructors
  in
  let rel_arity i funargs = 
    let rel_first_args :(Names.name * Rawterm.rawconstr) list  = (snd (list_chop nrel_params funargs)) in 
    List.fold_right
      (fun (n,t) acc -> 
	 Topconstr.CProdN
	   (dummy_loc,
	    [[(dummy_loc,n)],Constrextern.extern_rawconstr Idset.empty t],
	    acc
	   )
      )
      rel_first_args
      (Topconstr.CProdN
	 (dummy_loc,
	  [[(dummy_loc,Anonymous)],returned_types.(i)],
	  Topconstr.CSort(dummy_loc, RProp Null )
	 )
      )
  in
  let rel_arities = Array.mapi rel_arity funsargs in
  let old_rawprint = !Options.raw_print in 
  Options.raw_print := true;
  let rel_params =  
    List.map 
      (fun (n,t) -> 
	 Topconstr.LocalRawAssum 
	   ([(dummy_loc,n)], Constrextern.extern_rawconstr Idset.empty t)
      )
      rels_params
  in 
  let ext_rels_constructors = 
    Array.map (List.map 
      (fun (id,t) -> 
	 false,((dummy_loc,id),Constrextern.extern_rawtype Idset.empty t)
      ))
      rel_constructors
  in
  let rel_ind i ext_rel_constructors = 
    (dummy_loc,relnames.(i)),
    None,
    rel_params,
    rel_arities.(i),
    ext_rel_constructors
  in 
  let rel_inds = Array.to_list (Array.mapi rel_ind ext_rels_constructors) in 
(*   msgnl ( *)
(*     match rel_ind with  *)
(* 	(_,id),_,params,ar,constr ->  *)
(* 	  str "Inductive" ++ spc () ++ Ppconstr.pr_id id ++ *)
(* 	    spc () ++  *)
(* 	    prlist_with_sep  *)
(* 	    spc *)
(* 	    (function *)
(* 	       | (Topconstr.LocalRawAssum([_,n],t)) ->  *)
(* 		   str "(" ++ Ppconstr.pr_name n ++ str":" ++  *)
(* 		     Ppconstr.pr_type t ++ str ")" *)
(* 	       | _ -> assert false *)
(* 	    ) *)
(* 	    params ++ *)
(* 	    spc () ++ str ":" ++ spc () ++ *)
(* 	    Ppconstr.pr_type rel_arity ++  *)
(* 	    spc () ++  str ":=" ++ spc () ++ *)
(* 	    prlist_with_sep  *)
(* 	    (fun () -> fnl () ++ spc () ++ str "|" ++ spc ())  *)
(* 	    (function (_,((_,id),t)) ->  *)
(* 	       Ppconstr.pr_id id ++ spc () ++ str ":"++spc () ++ *)
(* 		 Ppconstr.pr_type t *)
(* 	    ) *)
(* 	    ext_rel_constructors *)
(*   ); *)
  let old_implicit_args = Impargs.is_implicit_args ()
  and old_strict_implicit_args =  Impargs.is_strict_implicit_args ()
  and old_contextual_implicit_args = Impargs.is_contextual_implicit_args () in
  Impargs.make_implicit_args false;
  Impargs.make_strict_implicit_args false;
  Impargs.make_contextual_implicit_args false;
  try 
    Command.build_mutual rel_inds true;
    Impargs.make_implicit_args old_implicit_args;
    Impargs.make_strict_implicit_args old_strict_implicit_args;
    Impargs.make_contextual_implicit_args old_contextual_implicit_args;
    Options.raw_print := old_rawprint;
  with
    | UserError(s,msg) -> 
	Impargs.make_implicit_args old_implicit_args;
	Impargs.make_strict_implicit_args old_strict_implicit_args;
	Impargs.make_contextual_implicit_args old_contextual_implicit_args;
	Options.raw_print := old_rawprint;
	raise 
	  (UserError(s,
		     str "while trying to define"++ spc () ++
		       Ppvernac.pr_vernac (Vernacexpr.VernacInductive(true,rel_inds)) ++ fnl () ++
		       msg
		    )
	  )
    | e -> 
	Impargs.make_implicit_args old_implicit_args;
	Impargs.make_strict_implicit_args old_strict_implicit_args;
	Impargs.make_contextual_implicit_args old_contextual_implicit_args;
	Options.raw_print := old_rawprint;
	raise 
	  (UserError("",
		     str "while trying to define"++ spc () ++
		       Ppvernac.pr_vernac (Vernacexpr.VernacInductive(true,rel_inds)) ++ fnl () ++
		       Cerrors.explain_exn e
		    )
	  )


