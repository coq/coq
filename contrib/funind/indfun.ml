open Util
open Names
open Term

open Pp
open Indfun_common
open Libnames
open Rawterm

type annot = identifier 


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
	

let generate_correction_proof_struct is_rec ind_kn mut_ind newfixpoint_exprl =
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

let do_generate_principle fix_rec_l = 
  let compute_annot (name,annot,args,types,body) =
    let names = List.map snd (Topconstr.names_of_local_assums args) in
    match annot with
      | None ->
          if List.length names > 1 then
            user_err_loc
              (dummy_loc,"GenFixpoint",
               Pp.str "the recursive argument needs to be specified");
          let new_annot = (id_of_name (List.hd names)) in 
	  (name,new_annot,args,types,body)
      | Some r -> (name,r,args,types,body)
  in
  let newfixpoint_exprl = List.map compute_annot fix_rec_l in 
  let prepare_body (name,annot,args,types,body) rt = 
    let fun_args,rt' = chop_rlambda_n (Topconstr.local_binders_length args) rt in 
    (name,annot,args,types,body,fun_args,rt')
  in
  match build_newrecursive newfixpoint_exprl with 
    | [] -> assert false
    | l ->
	let l' = List.map2 prepare_body newfixpoint_exprl l in 
	let names = List.map (function (name,_,_,_,_,_,_) -> name) l' in 
	let funs_args = List.map (function (_,_,_,_,_,fun_args,_) -> fun_args) l' in 
	let funs_types =  List.map (function (_,_,_,types,_,_,_) -> types) l' in 
(* 	let t1 = Sys.time () in  *)
	Rawterm_to_relation.build_inductive names funs_args funs_types l;
(* 	let t2 = Sys.time () in  *)
(* 	Pp.msgnl (str "Time to compute graph" ++ str (string_of_float (t2 -. t1))); *)
	let f_R_mut = Ident (dummy_loc,mk_rel_id (List.nth names 0)) in
	let ind =
	  locate_with_msg
	    (pr_reference f_R_mut++str ": Not an inductive type!")
	    locate_ind
	    f_R_mut
	in
	let mut_ind,_ = Global.lookup_inductive ind in
	let is_rec = 
	  List.exists (is_rec names) l
	in
(* 	msgnl (str "Inductives registered ... "); *)
	let fixpoint_exprl : (Topconstr.fixpoint_expr*'a) list =
	  List.map
	    (fun (fname,annot,args,types,body) ->
	       let names = List.map snd (Topconstr.names_of_local_assums args) in
	       let annot =
		 match annot with
		   |  id ->
			Util.list_index (Name id) names - 1
			  
	       in
	       (fname,annot,args,types,body),(None:Vernacexpr.decl_notation)
	    )
	    newfixpoint_exprl
	in
	register is_rec fixpoint_exprl;

	generate_correction_proof_struct
	  is_rec
	  (fst ind)
	  mut_ind
	  newfixpoint_exprl
