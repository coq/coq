open Closure
open RedFlags
open Declarations
open Entries
open Dyn
open Libobject
open Pattern
open Matching
open Pp
open Rawterm
open Sign
open Tacred
open Util
open Names
open Nameops
open Libnames
open Nametab
open Pfedit
open Proof_type
open Refiner
open Tacmach
open Tactic_debug
open Topconstr
open Term
open Termops
open Tacexpr
open Safe_typing
open Typing
open Hiddentac
open Genarg
open Decl_kinds
open Mod_subst
open Printer
open Inductiveops
open Syntax_def
open Environ
open Tactics
open Tacticals
open Tacinterp
open Vernacexpr
open Notation

module SPretyping = Subtac_pretyping.Pretyping
open Subtac_utils
open Pretyping

(*********************************************************************)
(* Functions to parse and interpret constructions *)

let evar_nf isevars c =
  isevars := Evarutil.nf_evar_defs !isevars;
  Evarutil.nf_isevar !isevars c

let interp_gen kind isevars env 
               ?(impls=([],[])) ?(allow_soapp=false) ?(ltacvars=([],[]))
               c =
  let c' = Constrintern.intern_gen (kind=IsType) ~impls ~allow_soapp ~ltacvars (Evd.evars_of !isevars) env c in
  let c' = Subtac_interp_fixpoint.rewrite_cases env c' in
  let c' = SPretyping.pretype_gen isevars env ([],[]) kind c' in
    evar_nf isevars c'
    
let interp_constr isevars env c =
  interp_gen (OfType None) isevars env c 

let interp_type isevars env ?(impls=([],[])) c =
  interp_gen IsType isevars env ~impls c

let interp_casted_constr isevars env ?(impls=([],[])) c typ =
  interp_gen (OfType (Some typ)) isevars env ~impls c 

let interp_open_constr isevars env c =
  let c = SPretyping.pretype_gen isevars env ([], []) (OfType None) 
	    (Constrintern.intern_constr (Evd.evars_of !isevars) env c) in
    evar_nf isevars c

let interp_constr_judgment isevars env c =
  let j = 
    SPretyping.understand_judgment_tcc isevars env
      (Constrintern.intern_constr (Evd.evars_of !isevars) env c) 
  in
    { uj_val = evar_nf isevars j.uj_val; uj_type = evar_nf isevars j.uj_type }

let locate_if_isevar loc na = function
  | RHole _ -> 
      (try match na with
	| Name id ->  Reserve.find_reserved_type id
	| Anonymous -> raise Not_found 
      with Not_found -> RHole (loc, Evd.BinderType na))
  | x -> x

let interp_binder sigma env na t =
  let t = Constrintern.intern_gen true (Evd.evars_of !sigma) env t in
    SPretyping.understand_type (Evd.evars_of !sigma) env (locate_if_isevar (loc_of_rawconstr t) na t)
      

let interp_context sigma env params = 
  List.fold_left
    (fun (env,params) d -> match d with
      | LocalRawAssum ([_,na],(CHole _ as t)) ->
	  let t = interp_binder sigma env na t in
	  let d = (na,None,t) in
	  (push_rel d env, d::params)
      | LocalRawAssum (nal,t) ->
	  let t = interp_type sigma env t in
	  let ctx = list_map_i (fun i (_,na) -> (na,None,lift i t)) 0 nal in
	  let ctx = List.rev ctx in
	  (push_rel_context ctx env, ctx@params)
      | LocalRawDef ((_,na),c) ->
	  let c = interp_constr_judgment sigma env c in
	  let d = (na, Some c.uj_val, c.uj_type) in
	  (push_rel d env,d::params))
    (env,[]) params

(* try to find non recursive definitions *)

let list_chop_hd i l = match list_chop i l with
  | (l1,x::l2) -> (l1,x,l2)
  | _ -> assert false

let collect_non_rec env = 
  let rec searchrec lnonrec lnamerec ldefrec larrec nrec = 
    try
      let i = 
        list_try_find_i
          (fun i f ->
             if List.for_all (fun (_, _, def) -> not (occur_var env f def)) ldefrec
             then i else failwith "try_find_i")
          0 lnamerec 
      in
      let (lf1,f,lf2) = list_chop_hd i lnamerec in
      let (ldef1,def,ldef2) = list_chop_hd i ldefrec in
      let (lar1,ar,lar2) = list_chop_hd i larrec in
      let newlnv = 
	try 
	  match list_chop i nrec with 
            | (lnv1,_::lnv2) -> (lnv1@lnv2)
	    | _ -> [] (* nrec=[] for cofixpoints *)
        with Failure "list_chop" -> []
      in 
      searchrec ((f,def,ar)::lnonrec) 
	(lf1@lf2) (ldef1@ldef2) (lar1@lar2) newlnv
    with Failure "try_find_i" -> 
      (List.rev lnonrec,
       (Array.of_list lnamerec, Array.of_list ldefrec,
        Array.of_list larrec, Array.of_list nrec))
  in 
  searchrec [] 

let definition_message id =
  Options.if_verbose message ((string_of_id id) ^ " is defined")

let recursive_message v =
  match Array.length v with
    | 0 -> error "no recursive definition"
    | 1 -> (Printer.pr_global v.(0) ++ str " is recursively defined")
    | _ -> hov 0 (prvect_with_sep pr_coma Printer.pr_global v ++
		    spc () ++ str "are recursively defined")

let filter_map f l = 
  let rec aux acc = function
      hd :: tl -> (match f hd with Some t -> aux (t :: acc) tl
		     | None -> aux acc tl)
    | [] -> List.rev acc
  in aux [] l

let list_of_local_binders l = 
  let rec aux acc = function
      Topconstr.LocalRawDef (n, c) :: tl -> aux ((n, Some c, None) :: acc) tl
    | Topconstr.LocalRawAssum (nl, c) :: tl -> 
	aux (List.fold_left (fun acc n -> (n, None, Some c) :: acc) acc nl) tl
    | [] -> List.rev acc
  in aux [] l

let build_recursive (lnameargsardef:(fixpoint_expr * decl_notation) list) boxed =
  let sigma = Evd.empty
  and env0 = Global.env()
  in 
  let lnameargsardef =
    (*List.map (fun (f, d) -> Subtac_interp_fixpoint.rewrite_fixpoint env0 protos (f, d))*)
      lnameargsardef
  in
  let lrecnames = List.map (fun ((f,_,_,_,_),_) -> f) lnameargsardef 
  and nv = List.map (fun ((_,n,_,_,_),_) -> n) lnameargsardef
  in
  (* Build the recursive context and notations for the recursive types *)
  let (rec_sign,rec_impls,arityl) = 
    List.fold_left 
      (fun (env,impls,arl) ((recname,(n, ro),bl,arityc,body),_) -> 
	let isevars = ref (Evd.create_evar_defs sigma) in	  
	  match ro with
	      CStructRec ->
		let arityc = Command.generalize_constr_expr arityc bl in
		let arity = interp_type isevars env0 arityc in
		let impl = 
		  if Impargs.is_implicit_args()
		  then Impargs.compute_implicits env0 arity
		  else [] in
		let impls' =(recname,([],impl,compute_arguments_scope arity))::impls in
		  (Environ.push_named (recname,None,arity) env, impls', (isevars, None, arity)::arl)
	    | CWfRec r -> 		    
		let _ = trace (str "Rewriting fixpoint: " ++ Ppconstr.pr_id recname ++ 
			       Ppconstr.pr_binders bl ++ str " : " ++ 
			       Ppconstr.pr_constr_expr arityc ++ str " := " ++ spc () ++
			       Ppconstr.pr_constr_expr body)
		in
		let env', binders_rel = interp_context isevars env0 bl in
		let before, ((argname, _, argtyp) as arg), after = list_chop_hd n binders_rel in
		let argid = match argname with Name n -> n | _ -> assert(false) in
		let after' = List.map (fun (n, c, t) -> (n, option_app (lift 1) c, lift 1 t)) after in
		let envwf = push_rel_context before env0 in
		let wf_rel = interp_constr isevars envwf r in
		let accarg_id = id_of_string ("Acc_" ^ string_of_id argid) in
		let accarg = (Name accarg_id, None, mkApp (Lazy.force acc_inv, [| wf_rel; mkRel 1 |])) in
		let argid' = id_of_string (string_of_id argid ^ "'") in
		let before_length, after_length = List.length before, List.length after in
		let full_length = before_length + 1 + after_length in
		let wfarg = (Name argid, None, 
			     mkSubset (Name argid') argtyp 
			       (mkApp (wf_rel, [|mkRel 1; mkRel (full_length + 1)|])))
		in
		let new_bl = before @ (arg :: accarg :: after')
		and intern_bl =  before @ (wfarg :: after)
		in
		let intern_env = push_rel_context intern_bl env0 in
		let env' = push_rel_context new_bl env0 in
		let arity = interp_type isevars intern_env arityc in
		let intern_arity = it_mkProd_or_LetIn arity intern_bl in
		let arity' = interp_type isevars env' arityc in
		let arity' = it_mkProd_or_LetIn arity' new_bl in
		let fun_bl = before @ (arg :: (Name recname, None, arity) :: after') in
		let impl = 
		  if Impargs.is_implicit_args()
		  then Impargs.compute_implicits intern_env arity'
		  else [] in
		let impls' = (recname,([],impl,compute_arguments_scope arity'))::impls in
		  (Environ.push_named (recname,None,arity') env, impls', 
		   (isevars, Some (full_length - n, argtyp, wf_rel, fun_bl, intern_bl, intern_arity), arity')::arl))
      (env0,[],[]) lnameargsardef in
  let arityl = List.rev arityl in
  let notations = 
    List.fold_right (fun (_,ntnopt) l -> option_cons ntnopt l) 
      lnameargsardef [] in

  let recdef =

    (* Declare local notations *)
    let fs = States.freeze() in
    let def = 
      try
	List.iter (fun (df,c,scope) -> (* No scope for tmp notation *)
	 Metasyntax.add_notation_interpretation df rec_impls c None) notations;
	List.map2
	  (fun ((_,_,bl,_,def),_) (isevars, info, arity) ->
	     match info with
		 None ->
		   let def = abstract_constr_expr def bl in
		     isevars, info, interp_casted_constr isevars rec_sign ~impls:([],rec_impls)
		       def arity
	       | Some (n, artyp, wfrel, bl, intern_bl, intern_arity) ->
		   let rec_sign = push_rel_context bl rec_sign in
		   let cstr = interp_casted_constr isevars rec_sign ~impls:([],rec_impls)
				def intern_arity
		   in isevars, info, cstr)
          lnameargsardef arityl
      with e ->
	States.unfreeze fs; raise e in
    States.unfreeze fs; def 
  in

  let (lnonrec,(namerec,defrec,arrec,nvrec)) = 
    collect_non_rec env0 lrecnames recdef arityl nv in
  let nvrec' = Array.map fst nvrec in(* ignore rec order *)
  let declare arrec defrec =
    let recvec = 
      Array.map (subst_vars (List.rev (Array.to_list namerec))) defrec in
    let recdecls = (Array.map (fun id -> Name id) namerec, arrec, recvec) in
    let rec declare i fi =
      trace (str "Declaring: " ++ pr_id fi ++ spc () ++
	     my_print_constr env0 (recvec.(i)));
      let ce = 
	{ const_entry_body = mkFix ((nvrec',i),recdecls); 
          const_entry_type = Some arrec.(i);
          const_entry_opaque = false;
          const_entry_boxed = boxed} in
      let kn = Declare.declare_constant fi (DefinitionEntry ce,IsDefinition Fixpoint)
      in (ConstRef kn)
    in 
      (* declare the recursive definitions *)
    let lrefrec = Array.mapi declare namerec in
      Options.if_verbose ppnl (recursive_message lrefrec);


      (*(* The others are declared as normal definitions *)
      let var_subst id = (id, Constrintern.global_reference id) in
      let _ = 
	List.fold_left
	  (fun subst (f,def,t) ->
	     let ce = { const_entry_body = replace_vars subst def;
			const_entry_type = Some t;
			const_entry_opaque = false;
			const_entry_boxed = boxed } in
	     let _ =
	       Declare.declare_constant f (DefinitionEntry ce,IsDefinition Definition)
	     in
      	       warning ((string_of_id f)^" is non-recursively defined");
      	       (var_subst f) :: subst)
	  (List.map var_subst (Array.to_list namerec))
	  lnonrec 
      in*)
      List.iter (fun (df,c,scope) ->
		   Metasyntax.add_notation_interpretation df [] c scope) notations
  in 
  let declare l = 
    let recvec = Array.of_list l
    and arrec = Array.map pi3 arrec
    in declare arrec recvec
  in
  let recdefs = Array.length defrec in
    trace (int recdefs ++ str " recursive definitions");
    (* Solve remaining evars *)
  let rec collect_evars i acc = 
    if i < recdefs then
      let (isevars, info, def) = defrec.(i) in
      let _ = trace (str "In solve evars, isevars is: " ++ Evd.pr_evar_defs !isevars) in
      let def = evar_nf isevars def in
      let isevars = Evd.undefined_evars !isevars in
      let _ = trace (str "In solve evars, undefined is: " ++ Evd.pr_evar_defs isevars) in
      let evm = Evd.evars_of isevars in
      let _, _, typ = arrec.(i) in
      let id = namerec.(i) in
      let def = 
	match info with 
	    Some (n, artyp, wfrel, funbl, bl, arity) ->
	      def (* mkApp (def, *)

	  | None -> def
		     in
	(* Generalize by the recursive prototypes  *)
      let def = 
	Termops.it_mkNamedLambda_or_LetIn def (Environ.named_context rec_sign)
      and typ = 
	Termops.it_mkNamedProd_or_LetIn typ (Environ.named_context rec_sign) in
      let evars_def, evars_typ, evars = Eterm.eterm_term evm def (Some typ) in 
      (*let evars_typ = match evars_typ with Some t -> t | None -> assert(false) in*)
      (*let fi = id_of_string (string_of_id id ^ "_evars") in*)
      (*let ce = 
	{ const_entry_body = evars_def; 
	  const_entry_type = Some evars_typ;
	  const_entry_opaque = false;
	  const_entry_boxed = boxed} in
      let kn = Declare.declare_constant fi (DefinitionEntry ce,IsDefinition Definition) in
	definition_message fi;
	trace (str (string_of_id fi) ++ str " is defined");*)
	let evar_sum =
	  if evars = [] then None
	  else 
	    let sum = Subtac_utils.build_dependent_sum evars in
	      trace (str "Evars sum: " ++ my_print_constr env0 (pi1 sum));
	      Some sum
	in
	  collect_evars (succ i) ((id, evars_def, evar_sum) :: acc)
    else acc
  in 
  let defs = collect_evars 0 [] in

  (* Solve evars then create the definitions *)
  let real_evars = 
    filter_map (fun (id, kn, sum) ->
		  match sum with Some (sumg, sumtac, _) -> Some (id, kn, sumg, sumtac) | None -> None)
      defs
  in
    Subtac_utils.and_tac real_evars
      (fun f _ gr ->
	 let _ = trace (str "Got a proof of: " ++ pr_global gr) in
	 let constant = match gr with Libnames.ConstRef c -> c
	   | _ -> assert(false)
	 in
	   try
	     (*let value = Environ.constant_value (Global.env ()) constant in*)
	     let pis = f (mkConst constant) in
	       trace (str "Accessors: " ++
		      List.fold_right (fun (_, _, _, c) acc -> my_print_constr env0 c ++ spc () ++ acc)
			pis (mt()));
	       trace (str "Applied existentials: " ++
		      (List.fold_right
			 (fun (id, kn, sumg, pi) acc ->
			    let args = Subtac_utils.destruct_ex pi sumg in
			      my_print_constr env0 (mkApp (kn, Array.of_list args)))
			 pis (mt ())));
	       let rec aux pis acc = function
		   (id, kn, sum) :: tl ->
		     (match sum with 
			  None -> aux pis (kn :: acc) tl
			| Some (sumg, _, _) -> 
			    let (id, kn, sumg, pi), pis = List.hd pis, List.tl pis in
			    let args = Subtac_utils.destruct_ex pi sumg in
			    let args = 
			      List.map (fun c -> 
					  try Reductionops.whd_betadeltaiota (Global.env ()) Evd.empty c
					  with Not_found ->
					    trace (str "Not_found while reducing " ++
						   my_print_constr (Global.env ()) c);
					    c
				       ) args 				  
			    in
			    let _, newdef = decompose_lam_n (recdefs + List.length args) kn in
			    let constr = Term.substl (mkRel 1 :: List.rev args) newdef in
			      aux pis (constr :: acc) tl)
		 | [] -> List.rev acc
	       in
		 declare (aux pis [] defs)
	   with Environ.NotEvaluableConst cer ->
	     match cer with
		 Environ.NoBody -> trace (str "Constant has no body")
	       | Environ.Opaque -> trace (str "Constant is opaque")
      )
      
      
