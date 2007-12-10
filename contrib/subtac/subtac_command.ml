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
open Subtac_obligations

(*********************************************************************)
(* Functions to parse and interpret constructions *)

let evar_nf isevars c =
  isevars := Evarutil.nf_evar_defs !isevars;
  Evarutil.nf_isevar !isevars c

let interp_gen kind isevars env 
               ?(impls=([],[])) ?(allow_patvar=false) ?(ltacvars=([],[]))
               c =
  let c' = Constrintern.intern_gen (kind=IsType) ~impls ~allow_patvar ~ltacvars (Evd.evars_of !isevars) env c in
(*     (try trace (str "Pretyping " ++ my_print_constr_expr c) with _ -> ()); *)
  let c' = SPretyping.pretype_gen isevars env ([],[]) kind c' in
    evar_nf isevars c'
    
let interp_constr isevars env c =
  interp_gen (OfType None) isevars env c 

let interp_type isevars env ?(impls=([],[])) c =
  interp_gen IsType isevars env ~impls c

let interp_casted_constr isevars env ?(impls=([],[])) c typ =
  interp_gen (OfType (Some typ)) isevars env ~impls c 

let interp_open_constr isevars env c =
    msgnl (str "Pretyping " ++ my_print_constr_expr c);
  let c = Constrintern.intern_constr (Evd.evars_of !isevars) env c in
  let c' = SPretyping.pretype_gen isevars env ([], []) (OfType None) c in
    evar_nf isevars c'

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
      | LocalRawAssum ([_,na],k,(CHole _ as t)) ->
	  let t = interp_binder sigma env na t in
	  let d = (na,None,t) in
	  (push_rel d env, d::params)
      | LocalRawAssum (nal,k,t) ->
	  let t = interp_type sigma env t in
	  let ctx = list_map_i (fun i (_,na) -> (na,None,lift i t)) 0 nal in
	  let ctx = List.rev ctx in
	  (push_rel_context ctx env, ctx@params)
      | LocalRawDef ((_,na),k,c) ->
	  let c = interp_constr_judgment sigma env c in
	  let d = (na, Some c.uj_val, c.uj_type) in
	  (push_rel d env,d::params))
    (env,[]) params

(* try to find non recursive definitions *)

let list_chop_hd i l = match list_chop i l with
  | (l1,x::l2) -> (l1,x,l2)
  | (x :: [], l2) -> ([], x, [])
  | _ -> assert(false)

let collect_non_rec env = 
  let rec searchrec lnonrec lnamerec ldefrec larrec nrec = 
    try
      let i = 
        list_try_find_i
          (fun i f ->
             if List.for_all (fun (_, def) -> not (occur_var env f def)) ldefrec
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

let list_of_local_binders l = 
  let rec aux acc = function
      Topconstr.LocalRawDef (n, k, c) :: tl -> aux ((n, Some c, None) :: acc) tl
    | Topconstr.LocalRawAssum (nl, k, c) :: tl -> 
	aux (List.fold_left (fun acc n -> (n, None, Some c) :: acc) acc nl) tl
    | [] -> List.rev acc
  in aux [] l

let lift_binders k n l =
  let rec aux n = function
    | (id, t, c) :: tl -> (id, Option.map (liftn k n) t, liftn k n c) :: aux (pred n) tl
    | [] -> []
  in aux n l

let rec gen_rels = function
    0 -> []
  | n -> mkRel n :: gen_rels (pred n)

let split_args n rel = match list_chop ((List.length rel) - n) rel with
    (l1, x :: l2) -> l1, x, l2
  | _ -> assert(false)

let build_wellfounded (recname, n, bl,arityc,body) r measure notation boxed =
  let sigma = Evd.empty in
  let isevars = ref (Evd.create_evar_defs sigma) in
  let env = Global.env() in 
  let pr c = my_print_constr env c in
  let prr = Printer.pr_rel_context env in
  let _prn = Printer.pr_named_context env in
  let _pr_rel env = Printer.pr_rel_context env in
(*   let _ =  *)
(*     try debug 2 (str "In named context: " ++ prn (named_context env) ++ str "Rewriting fixpoint: " ++ Ppconstr.pr_id recname ++  *)
(* 		 Ppconstr.pr_binders bl ++ str " : " ++  *)
(* 		 Ppconstr.pr_constr_expr arityc ++ str " := " ++ spc () ++ *)
(* 		 Ppconstr.pr_constr_expr body) *)
(*     with _ -> () *)
    (*   in *)
  let env', binders_rel = interp_context isevars env bl in
  let after, ((argname, _, argtyp) as arg), before = split_args (succ n) binders_rel in
  let before_length, after_length = List.length before, List.length after in
  let argid = match argname with Name n -> n | _ -> assert(false) in
  let liftafter = lift_binders 1 after_length after in
  let envwf = push_rel_context before env in
  let wf_rel, wf_rel_fun, measure_fn = 
    let rconstr_body, rconstr = 
      let app = mkAppC (r, [mkIdentC (id_of_name argname)]) in
       let env = push_rel_context [arg] envwf in
       let capp = interp_constr isevars env app in
 	 capp, mkLambda (argname, argtyp, capp)
     in
      trace (str"rconstr_body: " ++ pr rconstr_body);
       if measure then
 	let lt_rel = constr_of_global (Lazy.force lt_ref) in
 	let name s = Name (id_of_string s) in
 	let wf_rel_fun lift x y = (* lift to before_env *)
	  trace (str"lifter rconstr_body:" ++ pr (liftn lift 2 rconstr_body));
 	  mkApp (lt_rel, [| subst1 x (liftn lift 2 rconstr_body); 
 			    subst1 y (liftn lift 2 rconstr_body) |])
	in
 	let wf_rel = 
 	  mkLambda (name "x", argtyp,
 		    mkLambda (name "y", lift 1 argtyp,
 			      wf_rel_fun 0 (mkRel 2) (mkRel 1)))
 	in
 	  wf_rel, wf_rel_fun , Some rconstr
       else rconstr, (fun lift x y -> mkApp (rconstr, [|x; y|])), None
  in
  let wf_proof = mkApp (Lazy.force well_founded, [| argtyp ; wf_rel |])
  in
  let argid' = id_of_string (string_of_id argid ^ "'") in
  let wfarg len = (Name argid', None,
  		   mkSubset (Name argid') (lift len argtyp) 
		     (wf_rel_fun (succ len) (mkRel 1) (mkRel (len + 1))))
  in
  let top_bl = after @ (arg :: before) in
  let top_env = push_rel_context top_bl env in
  let top_arity = interp_type isevars top_env arityc in
  let intern_bl = wfarg 1 :: arg :: before in
  let intern_env = push_rel_context intern_bl env in
  let proj = (Lazy.force sig_).Coqlib.proj1 in
  let projection = 
    mkApp (proj, [| argtyp ;
		    (mkLambda (Name argid', argtyp,
			       (wf_rel_fun 1 (mkRel 1) (mkRel 3)))) ;
		    mkRel 1
		 |])
  in
  let intern_arity = it_mkProd_or_LetIn top_arity after in
    trace (str "After length: " ++ int after_length ++ str "Top env: " ++ prr top_bl ++ spc () ++ 
	      str "Intern arity: " ++ my_print_constr 
	      (push_rel_context (arg :: before) env) intern_arity);
  (* Intern arity is in top_env = arg :: before *)
  let intern_arity = liftn 2 2 intern_arity in
    trace (str "After lifting arity: " ++ 
	      my_print_constr (push_rel (Name argid', None, lift 2 argtyp) intern_env)
	      intern_arity);
  (* arity is now in something :: wfarg :: arg :: before 
     where what refered to arg now refers to something *)
  let intern_arity = substl [projection] intern_arity in
  (* substitute the projection of wfarg for something *)
  (try trace (str "Top arity after subst: " ++ my_print_constr intern_env intern_arity) with _ -> ());
(*   let intern_arity = liftn 1 (succ after_length) intern_arity in (\* back in after :: wfarg :: arg :: before (ie, jump over arg) *\) *)
(*   (try trace (str "Top arity after subst and lift: " ++ my_print_constr (Global.env ()) intern_arity) with _ -> ()); *)
  let intern_before_env = push_rel_context before env in
(*   let intern_fun_bl = liftafter @ [wfarg 1]  in (\* FixMe dependencies *\) *)
(*   (try debug 2 (str "Intern fun bl: " ++ prr intern_fun_bl) with _ -> ()); *)
  (try trace (str "Intern arity: " ++
		  my_print_constr intern_env intern_arity) with _ -> ());
  let intern_fun_arity_prod = it_mkProd_or_LetIn intern_arity [wfarg 1] in
  (try trace (str "Intern fun arity product: " ++
		  my_print_constr (push_rel_context [arg] intern_before_env) intern_fun_arity_prod) with _ -> ());
  let intern_fun_binder = (Name recname, None, intern_fun_arity_prod) in
  let fun_bl = liftafter @ (intern_fun_binder :: [arg]) in
(*   (try debug 2 (str "Fun bl: " ++ pr_rel intern_before_env fun_bl ++ spc ()) with _ -> ()); *)
  let fun_env = push_rel_context fun_bl intern_before_env in
  let fun_arity = interp_type isevars fun_env arityc in
  let intern_body = interp_casted_constr isevars fun_env body fun_arity in
  let intern_body_lam = it_mkLambda_or_LetIn intern_body fun_bl in
  let _ =
    try trace ((* str "Fun bl: " ++ prr fun_bl ++ spc () ++ *)
		 str "Intern bl" ++ prr intern_bl ++ spc ())
(* 		 str "Top bl" ++ prr top_bl ++ spc () ++ *)
(* 		 str "Intern arity: " ++ pr intern_arity ++ *)
(* 		 str "Top arity: " ++ pr top_arity ++ spc () ++ *)
(* 		   str "Intern body " ++ pr intern_body_lam) *)
    with _ -> ()
  in
  let _impl = 
    if Impargs.is_implicit_args()
    then Impargs.compute_implicits top_env top_arity
    else [] 
  in
  let prop = mkLambda (Name argid, argtyp, it_mkProd_or_LetIn top_arity after) in
    (* Lift to get to constant arguments *)
  let lift_cst = List.length after + 1 in
  let fix_def =
    match measure_fn with
	None ->
	  mkApp (constr_of_global (Lazy.force fix_sub_ref), 
		 [| argtyp ;
		    wf_rel ;
		    make_existential dummy_loc ~opaque:false env isevars wf_proof ;
		    lift lift_cst prop ;
		    lift lift_cst intern_body_lam |])
      | Some f ->
	  lift (succ after_length) 
	    (mkApp (constr_of_global (Lazy.force fix_measure_sub_ref), 
		    [| argtyp ; 
		       f ;
		       lift lift_cst prop ;
		       lift lift_cst intern_body_lam |]))
  in
  let def_appl = applist (fix_def, gen_rels (after_length + 1)) in
  let def = it_mkLambda_or_LetIn def_appl binders_rel in
  let typ = it_mkProd_or_LetIn top_arity binders_rel in
  let fullcoqc = Evarutil.nf_isevar !isevars def in
  let fullctyp = Evarutil.nf_isevar !isevars typ in
(*   let _ = try trace (str "After evar normalization: " ++ spc () ++ *)
(* 		 str "Coq term: " ++ my_print_constr env fullcoqc ++ spc () *)
(* 		     ++ str "Coq type: " ++ my_print_constr env fullctyp)  *)
(*      with _ -> ()  *)
(*   in *)
  let evm = evars_of_term (Evd.evars_of !isevars) Evd.empty fullctyp in
  let evm = evars_of_term (Evd.evars_of !isevars) evm fullcoqc in
  let evm = non_instanciated_map env isevars evm in

    (*   let _ = try trace (str "Non instanciated evars map: " ++ Evd.pr_evar_map evm)  with _ -> () in *)
  let evars, evars_def = Eterm.eterm_obligations env recname !isevars evm 0 fullcoqc (Some fullctyp) in
    (*     (try trace (str "Generated obligations : "); *)
(*        Array.iter *)
    (* 	 (fun (n, t, _) -> trace (str "Evar " ++ str (string_of_id n) ++ spc () ++ my_print_constr env t)) *)
    (* 	 evars; *)
    (*      with _ -> ());     *)
    Subtac_obligations.add_definition recname evars_def fullctyp evars

let nf_evar_context isevars ctx = 
  List.map (fun (n, b, t) -> 
    (n, Option.map (Evarutil.nf_isevar isevars) b, Evarutil.nf_isevar isevars t)) ctx
    
let build_mutrec lnameargsardef boxed = 
  let sigma = Evd.empty and env = Global.env () in 
  let lrecnames = List.map (fun ((f,_,_,_,_),_) -> f) lnameargsardef 
  and nv = List.map (fun ((_,n,_,_,_),_) -> n) lnameargsardef
  in
  let isevars = ref (Evd.create_evar_defs sigma) in	  
    (* Build the recursive context and notations for the recursive types *)
  let (rec_sign,rec_env,rec_impls,arityl) = 
    List.fold_left 
      (fun (sign,env,impls,arl) ((recname, n, bl,arityc,body),_) -> 
	 let arityc = Command.generalize_constr_expr arityc bl in
	 let arity = interp_type isevars env arityc in
	 let impl = 
	   if Impargs.is_implicit_args()
	   then Impargs.compute_implicits env arity
	   else [] in
	 let impls' =(recname,([],impl,compute_arguments_scope arity))::impls in
	   ((recname,None,arity) :: sign, Environ.push_named (recname,None,arity) env, impls', (None, arity)::arl))
      ([],env,[],[]) lnameargsardef in
  let arityl = List.rev arityl in
  let notations = 
    List.fold_right (fun (_,ntnopt) l -> Option.List.cons ntnopt l) 
      lnameargsardef [] in

  let recdef =
    (* Declare local notations *)
    let fs = States.freeze() in
    let def = 
      try
	List.iter (fun (df,c,scope) -> (* No scope for tmp notation *)
	 Metasyntax.add_notation_interpretation df rec_impls c None) notations;
	List.map2
	  (fun ((_,_,bl,_,def),_) (info, arity) ->
	     match info with
		 None ->
		   let def = abstract_constr_expr def bl in
		     info, interp_casted_constr isevars rec_env ~impls:([],rec_impls)
		       def arity
	       | Some (n, artyp, wfrel, fun_bl, intern_bl, intern_arity) ->
		   let rec_env = push_rel_context fun_bl rec_env in
		   let cstr = interp_casted_constr isevars rec_env ~impls:([],rec_impls)
				def intern_arity
		   in info, it_mkLambda_or_LetIn cstr fun_bl)
          lnameargsardef arityl
      with e ->
	States.unfreeze fs; raise e in
    States.unfreeze fs; def 
  in
  let (lnonrec,(namerec,defrec,arrec,nvrec)) = 
    collect_non_rec env lrecnames recdef arityl nv in
  if lnonrec <> [] then 
    errorlabstrm "Subtac_command.build_mutrec"
      (str "Non-recursive definitions not allowed in mutual fixpoint blocks");
  let recdefs = Array.length defrec in
    trace (str "built recursive definitions");
    (* Normalize all types and defs with respect to *all* evars *)
    Array.iteri 
      (fun i (info, def) ->
	let def = evar_nf isevars def in
	let y, typ = arrec.(i) in
	let typ = evar_nf isevars typ in
	  arrec.(i) <- (y, typ);
	  defrec.(i) <- (info, def))
      defrec;
    trace (str "normalized w.r.t. evars");
  (* Normalize rec_sign which was built earlier *)
  let rec_sign = nf_evar_context !isevars rec_sign in
    trace (str "normalized context");
  (* Get the interesting evars, those that were not instanciated *)
  let isevars = Evd.undefined_evars !isevars in
    trace (str "got undefined evars" ++ Evd.pr_evar_defs isevars);
  let evm = Evd.evars_of isevars in
  trace (str "got the evm, recdefs is " ++ int recdefs);
  (* Solve remaining evars *)
  let rec collect_evars i acc = 
    if i < recdefs then
      let (info, def) = defrec.(i) in
      let y, typ = arrec.(i) in
	trace (str "got the def" ++ int i);
      let _ = try trace (str "In collect evars, isevars is: " ++ Evd.pr_evar_defs isevars) with _ -> () in
      let id = namerec.(i) in
	(* Generalize by the recursive prototypes  *)
      let def = 
	Termops.it_mkNamedLambda_or_LetIn def rec_sign
      and typ = 
	Termops.it_mkNamedProd_or_LetIn typ rec_sign
      in
      let evm = Subtac_utils.evars_of_term evm Evd.empty def in
      let evars, def = Eterm.eterm_obligations env id isevars evm recdefs def (Some typ) in
	collect_evars (succ i) ((id, def, typ, evars) :: acc)
    else acc
  in 
  let defs = collect_evars 0 [] in
    Subtac_obligations.add_mutual_definitions (List.rev defs) nvrec
    
      
let out_n = function
    Some n -> n
  | None -> 0

let build_recursive (lnameargsardef:(fixpoint_expr * decl_notation) list) boxed =
  match lnameargsardef with
    | ((id, (n, CWfRec r), bl, typ, body), no) :: [] -> 
	ignore(build_wellfounded (id, out_n n, bl, typ, body) r false no boxed)
    | ((id, (n, CMeasureRec r), bl, typ, body), no) :: [] -> 
	ignore(build_wellfounded (id, out_n n, bl, typ, body) r true no boxed)
    | l -> 
	let lnameargsardef = 
	  List.map (fun ((id, (n, ro), bl, typ, body), no) ->
		 match ro with
		     CStructRec -> (id, out_n n, bl, typ, body), no
		   | CWfRec _ | CMeasureRec _ -> 
		       errorlabstrm "Subtac_command.build_recursive"
			 (str "Well-founded fixpoints not allowed in mutually recursive blocks"))
	    lnameargsardef
	in build_mutrec lnameargsardef boxed
	  
      
      
