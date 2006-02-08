open Util
open Names
open Term

open Pp
open Indfun_common
open Libnames
open Rawterm

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
(lnameargsardef:(newfixpoint_expr ) list)  =
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

let rec is_rec names = 
  let names = List.fold_right Idset.add names Idset.empty in 
  let check_id id =  Idset.mem id names in 
  let rec lookup = function 
    | RVar(_,id) -> check_id id
    | RRef _ | REvar _ | RPatVar _ | RSort _ |  RHole _ | RDynamic _ -> false
    | RCast(_,b,_,_) -> lookup b
    | RRec _ -> assert false 
    | RIf _ -> failwith "Rif not implemented"
    | RLetTuple _ -> failwith "RLetTuple not implemented"
    | RLetIn(_,_,t,b) | RLambda(_,_,t,b) | RProd(_,_,t,b) -> 
	lookup t || lookup b
    | RApp(_,f,args) -> List.exists lookup (f::args)
    | RCases(_,_,el,brl) -> 
	List.exists (fun (e,_) -> lookup e) el ||
	  List.exists (fun (_,_,_,ret)-> lookup ret) brl
  in
  lookup 

    
let register is_rec fixpoint_exprl = 
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
	

let generate_correction_proof_struct  ind_kn  newfixpoint_exprl =
  let fname_kn (fname,_,_,_,_) =
    let f_ref = Ident (dummy_loc,fname) in
    locate_with_msg
      (pr_reference f_ref++str ": Not an inductive type!")
      locate_constant
      f_ref
  in
  let funs_kn = Array.of_list (List.map fname_kn newfixpoint_exprl) in 
  ignore
    (Util.list_map_i
       (fun i x ->
(* 	  let f_kn = fname_kn x in *)
	  New_arg_principle.generate_new_structural_principle
	    (destConst (Indrec.lookup_eliminator (ind_kn,i) (InProp)))
	    (Termops.new_sort_in_family InType)
	    None
	    true
	    funs_kn
	    i
       )
       0
       newfixpoint_exprl
    );
    ()
 
let compute_annot (name,annot,args,types,body) =
  let names = List.map snd (Topconstr.names_of_local_assums args) in
  match annot with
    | None ->
        if List.length names > 1 then
            user_err_loc
              (dummy_loc,"GenFixpoint",
               Pp.str "the recursive argument needs to be specified");
        let new_annot = (id_of_name (List.hd names)) in
	(name,Struct new_annot,args,types,body)
    | Some r -> (name,r,args,types,body)



let rec is_rec names = 
  let names = List.fold_right Idset.add names Idset.empty in 
  let check_id id =  Idset.mem id names in 
  let rec lookup = function 
    | RVar(_,id) -> check_id id
    | RRef _ | REvar _ | RPatVar _ | RSort _ |  RHole _ | RDynamic _ -> false
    | RCast(_,b,_,_) -> lookup b
    | RRec _ -> assert false 
    | RIf _ -> failwith "Rif not implemented"
    | RLetTuple _ -> failwith "RLetTuple not implemented"
    | RLetIn(_,_,t,b) | RLambda(_,_,t,b) | RProd(_,_,t,b) -> 
	lookup t || lookup b
    | RApp(_,f,args) -> List.exists lookup (f::args)
    | RCases(_,_,el,brl) -> 
	List.exists (fun (e,_) -> lookup e) el ||
	  List.exists (fun (_,_,_,ret)-> lookup ret) brl
  in
  lookup 

    
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

let register_wf ?(is_mes=false) fname wf_rel_expr wf_arg args ret_type body =  
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
  Recdef.recursive_definition is_mes fname type_of_f wf_rel_expr rec_arg_num eq
    
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
		       List.exists (function (_,Name id) -> id =  wf_args | _ -> false) l 
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
      Topconstr.mkAppC(wf_mes_expr,[Topconstr.mkIdentC wf_arg])
    in
    Topconstr.mkLambdaC ([(dummy_loc,Name wf_arg)],wf_arg_type,applied_mes) 
  in
  let wf_rel_from_mes = 
    Topconstr.mkAppC(Topconstr.mkRefC  ltof,[wf_arg_type;fun_from_mes])
  in
  register_wf ~is_mes:true fname wf_rel_from_mes (Some wf_arg) args ret_type body
	  



let register (fixpoint_exprl :  newfixpoint_expr list) = 
  let recdefs = build_newrecursive fixpoint_exprl in 
  let is_struct = 
    match fixpoint_exprl with 
      | [((name,Wf (wf_rel,wf_x),args,types,body))] -> 
	  register_wf name wf_rel wf_x args types body;
	  false
      | [((name,Mes (wf_mes,wf_x),args,types,body))] -> 
	  register_mes name wf_mes wf_x args types body;
	  false
      | _ -> 
	  
	  let old_fixpoint_exprl =  
	    List.map 
	      (function
		 | (name,Struct id,args,types,body) -> 
		     let names = 
		       List.map
			 snd
			 (Topconstr.names_of_local_assums args) 
		     in 
		     let annot = Util.list_index (Name id) names - 1 in 
 		     (name,annot,args,types,body),(None:Vernacexpr.decl_notation) 
		 | (_,Wf _,_,_,_) | (_,Mes _,_,_,_)  -> 
		     error 
		       ("Cannot use mutual definition with well-founded recursion")
	      ) 
	      fixpoint_exprl 
	  in
	  (* ok all the expressions are structural *) 
	  let fix_names = 
	    List.map (function (name,_,_,_,_) -> name) fixpoint_exprl 
	  in
	  let is_rec = List.exists (is_rec fix_names) recdefs in
	  register_struct is_rec old_fixpoint_exprl;
	  true
						 
  in
  recdefs,is_struct

let prepare_body (name,annot,args,types,body) rt = 
  let fun_args,rt' = chop_rlambda_n (Topconstr.local_binders_length args) rt in
  (fun_args,rt')

let do_generate_principle fix_rec_l = 
  (* we first of all checks whether on not all the correct 
     assumption  are here 
  *)
  let newfixpoint_exprl = List.map compute_annot fix_rec_l in 
  (* we can then register the functions *) 
  let recdefs,is_struct = register newfixpoint_exprl in 
(*   Pp.msgnl (str "Fixpoint(s) registered"); *)
  let names = List.map (function (name,_,_,_,_) -> name) fix_rec_l in
  let fun_bodies = List.map2 prepare_body newfixpoint_exprl recdefs in
  let funs_args = List.map fst fun_bodies in
  let funs_types =  List.map (function (_,_,_,types,_) -> types) fix_rec_l in
  try 
    (* We then register the Inductive graphs of the functions  *)
    Rawterm_to_relation.build_inductive names funs_args funs_types recdefs;
    let f_R_mut = Ident (dummy_loc,mk_rel_id (List.nth names 0)) in
    let ind =
      locate_with_msg
	(pr_reference f_R_mut++str ": Not an inductive type!")
	locate_ind
	f_R_mut
    in
    (*   let mut_ind,_ = Global.lookup_inductive ind in *)
    if is_struct 
    then
      generate_correction_proof_struct (fst ind)  newfixpoint_exprl
  with _ -> () 
;;


(* let do_generate_principle fix_rec_l = *)
(*   let compute_annot (name,annot,args,types,body) = *)
(*     let names = List.map snd (Topconstr.names_of_local_assums args) in *)
(*     match annot with *)
(*       | None -> *)
(*           if List.length names > 1 then *)
(*             user_err_loc *)
(*               (dummy_loc,"GenFixpoint", *)
(*                Pp.str "the recursive argument needs to be specified"); *)
(*           let new_annot = (id_of_name (List.hd names)) in *)
(* 	  (name,new_annot,args,types,body) *)
(*       | Some r -> (name,r,args,types,body) *)
(*   in *)
(*   let newfixpoint_exprl = List.map compute_annot fix_rec_l in *)
(*   let prepare_body (name,annot,args,types,body) rt = *)
(*     let fun_args,rt' = chop_rlambda_n (Topconstr.local_binders_length args) rt in *)
(*     (name,annot,args,types,body,fun_args,rt') *)
(*   in *)
(*   match build_newrecursive newfixpoint_exprl with *)
(*     | [] -> assert false *)
(*     | l -> *)
(* 	let l' = List.map2 prepare_body newfixpoint_exprl l in *)
(* 	let names = List.map (function (name,_,_,_,_,_,_) -> name) l' in *)
(* 	let funs_args = List.map (function (_,_,_,_,_,fun_args,_) -> fun_args) l' in *)
(* 	let funs_types =  List.map (function (_,_,_,types,_,_,_) -> types) l' in *)
(* (\* 	let t1 = Sys.time () in  *\) *)
(* 	Rawterm_to_relation.build_inductive names funs_args funs_types l; *)
(* (\* 	let t2 = Sys.time () in  *\) *)
(* (\* 	Pp.msgnl (str "Time to compute graph" ++ str (string_of_float (t2 -. t1))); *\) *)
(* 	let f_R_mut = Ident (dummy_loc,mk_rel_id (List.nth names 0)) in *)
(* 	let ind = *)
(* 	  locate_with_msg *)
(* 	    (pr_reference f_R_mut++str ": Not an inductive type!") *)
(* 	    locate_ind *)
(* 	    f_R_mut *)
(* 	in *)
(* 	let mut_ind,_ = Global.lookup_inductive ind in *)
(* 	let is_rec = *)
(* 	  List.exists (is_rec names) l *)
(* 	in *)
(* (\* 	msgnl (str "Inductives registered ... "); *\) *)
(* 	let fixpoint_exprl : (Topconstr.fixpoint_expr*'a) list = *)
(* 	  List.map *)
(* 	    (fun (fname,annot,args,types,body) -> *)
(* 	       let names = List.map snd (Topconstr.names_of_local_assums args) in *)
(* 	       let annot = *)
(* 		 match annot with *)
(* 		   |  id -> *)
(* 			Util.list_index (Name id) names - 1 *)
			  
(* 	       in *)
(* 	       (fname,annot,args,types,body),(None:Vernacexpr.decl_notation) *)
(* 	    ) *)
(* 	    newfixpoint_exprl *)
(* 	in *)
(* 	register is_rec fixpoint_exprl; *)

(* 	generate_correction_proof_struct *)
(* 	  is_rec *)
(* 	  (fst ind) *)
(* 	  mut_ind *)
(* 	  newfixpoint_exprl *)
