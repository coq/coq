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
open Evd
open Evarutil

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

let interp_type_evars isevars env ?(impls=([],[])) c =
  interp_gen IsType isevars env ~impls c

let interp_casted_constr isevars env ?(impls=([],[])) c typ =
  interp_gen (OfType (Some typ)) isevars env ~impls c 

let interp_casted_constr_evars isevars env ?(impls=([],[])) c typ =
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
    SPretyping.pretype_gen sigma env ([], []) IsType (locate_if_isevar (loc_of_rawconstr t) na t)
      
let interp_context_evars sigma env params = 
  List.fold_left
    (fun (env,params) d -> match d with
      | LocalRawAssum ([_,na],k,(CHole _ as t)) ->
	  let t = interp_binder sigma env na t in
	  let d = (na,None,t) in
	  (push_rel d env, d::params)
      | LocalRawAssum (nal,k,t) ->
	  let t = interp_type_evars sigma env t in
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
      Topconstr.LocalRawDef (n, c) :: tl -> aux ((n, Some c, None) :: acc) tl
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
  let env', binders_rel = interp_context_evars isevars env bl in
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
  let top_arity = interp_type_evars isevars top_env arityc in
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
  let fun_arity = interp_type_evars isevars fun_env arityc in
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
	  mkApp (constr_of_global (Lazy.force fix_measure_sub_ref), 
		[| lift lift_cst argtyp ; 
		   lift lift_cst f ;
		   lift lift_cst prop ;
		   lift lift_cst intern_body_lam |])
  in
  let def_appl = applist (fix_def, gen_rels (after_length + 1)) in
  let def = it_mkLambda_or_LetIn def_appl binders_rel in
  let typ = it_mkProd_or_LetIn top_arity binders_rel in
  let fullcoqc = Evarutil.nf_isevar !isevars def in
  let fullctyp = Evarutil.nf_isevar !isevars typ in
  let evm = evars_of_term (Evd.evars_of !isevars) Evd.empty fullctyp in
  let evm = evars_of_term (Evd.evars_of !isevars) evm fullcoqc in
  let evm = non_instanciated_map env isevars evm in
  let evars, evars_def, evars_typ = Eterm.eterm_obligations env recname !isevars evm 0 fullcoqc fullctyp in
    Subtac_obligations.add_definition recname evars_def evars_typ evars

let nf_evar_context isevars ctx = 
  List.map (fun (n, b, t) -> 
    (n, Option.map (Evarutil.nf_isevar isevars) b, Evarutil.nf_isevar isevars t)) ctx
    
let interp_fix_context evdref env fix =
  interp_context_evars evdref env fix.Command.fix_binders

let interp_fix_ccl evdref (env,_) fix =
  interp_type_evars evdref env fix.Command.fix_type

let interp_fix_body evdref env_rec impls (_,ctx) fix ccl =
  let env = push_rel_context ctx env_rec in
  let body = interp_casted_constr_evars evdref env ~impls fix.Command.fix_body ccl in
  it_mkLambda_or_LetIn body ctx

let build_fix_type (_,ctx) ccl = it_mkProd_or_LetIn ccl ctx

let prepare_recursive_declaration fixnames fixtypes fixdefs =
  let defs = List.map (subst_vars (List.rev fixnames)) fixdefs in
  let names = List.map (fun id -> Name id) fixnames in
  (Array.of_list names, Array.of_list fixtypes, Array.of_list defs)

let compute_possible_guardness_evidences (n,_) fixtype =
  match n with 
  | Some n -> [n] 
  | None -> 
      (* If recursive argument was not given by user, we try all args.
	 An earlier approach was to look only for inductive arguments,
	 but doing it properly involves delta-reduction, and it finally 
         doesn't seem to worth the effort (except for huge mutual 
	 fixpoints ?) *)
      let m = Term.nb_prod fixtype in
      let ctx = fst (Sign.decompose_prod_n_assum m fixtype) in
	list_map_i (fun i _ -> i) 0 ctx

let push_named_context = List.fold_right push_named

let interp_recursive fixkind l boxed =
  let env = Global.env() in
  let fixl, ntnl = List.split l in
  let fixnames = List.map (fun fix -> fix.Command.fix_name) fixl in

  (* Interp arities allowing for unresolved types *)
  let evdref = ref (Evd.create_evar_defs Evd.empty) in
  let fiximps = 
    List.map 
      (fun x -> Implicit_quantifiers.implicits_of_binders x.Command.fix_binders) 
      fixl 
  in
  let fixctxs = List.map (interp_fix_context evdref env) fixl in
  let fixccls = List.map2 (interp_fix_ccl evdref) fixctxs fixl in
  let fixtypes = List.map2 build_fix_type fixctxs fixccls in
  let rec_sign = 
    List.fold_left2 (fun env id t -> (id,None,t) :: env)
      [] fixnames fixtypes
  in
  let env_rec = push_named_context rec_sign env in

  (* Get interpretation metadatas *)
  let impls = Command.compute_interning_datas env [] fixnames fixtypes in
  let notations = List.fold_right Option.List.cons ntnl [] in

  (* Interp bodies with rollback because temp use of notations/implicit *)
  let fixdefs = 
    States.with_heavy_rollback (fun () -> 
      List.iter (Command.declare_interning_data impls) notations;
      list_map3 (interp_fix_body evdref env_rec impls) fixctxs fixl fixccls)
      () in

  (* Instantiate evars and check all are resolved *)
  let evd,_ = Evarconv.consider_remaining_unif_problems env_rec !evdref in
  let fixdefs = List.map (nf_evar (evars_of evd)) fixdefs in
  let fixtypes = List.map (nf_evar (evars_of evd)) fixtypes in
  let rec_sign = nf_named_context_evar (evars_of evd) rec_sign in
  let recdefs = List.length rec_sign in
(*   List.iter (check_evars env_rec Evd.empty evd) fixdefs; *)
(*   List.iter (check_evars env Evd.empty evd) fixtypes; *)
(*   check_mutuality env kind (List.combine fixnames fixdefs); *)

  (* Russell-specific code *)

  (* Get the interesting evars, those that were not instanciated *)
  let isevars = Evd.undefined_evars evd in
  trace (str "got undefined evars" ++ Evd.pr_evar_defs isevars);
  let evm = Evd.evars_of isevars in
  trace (str "got the evm, recdefs is " ++ int recdefs);
  (* Solve remaining evars *)
  let rec collect_evars id def typ imps = 
    let _ = try trace (str "In collect evars, isevars is: " ++ Evd.pr_evar_defs isevars) with _ -> () in
      (* Generalize by the recursive prototypes  *)
    let def = 
      Termops.it_mkNamedLambda_or_LetIn def rec_sign
    and typ =
      Termops.it_mkNamedProd_or_LetIn typ rec_sign
    in
    let evm' = Subtac_utils.evars_of_term evm Evd.empty def in
    let evm' = Subtac_utils.evars_of_term evm evm' typ in
    let evars, def, typ = Eterm.eterm_obligations env id isevars evm' recdefs def typ in
      (id, def, typ, imps, evars)
  in 
  let defs = list_map4 collect_evars fixnames fixdefs fixtypes fiximps in
    (match fixkind with
      | Command.IsFixpoint wfl ->
	  let possible_indexes =
	    List.map2 compute_possible_guardness_evidences wfl fixtypes in
	  let fixdecls = Array.of_list (List.map (fun x -> Name x) fixnames), 
	    Array.of_list fixtypes, Array.of_list (List.map (subst_vars fixnames) fixdefs)
	  in
	  let indexes = Pretyping.search_guard dummy_loc (Global.env ()) possible_indexes fixdecls in
	    list_iter_i (fun i _ -> Inductive.check_fix env ((indexes,i),fixdecls)) l
      | Command.IsCoFixpoint -> ());
    Subtac_obligations.add_mutual_definitions defs notations fixkind

let out_n = function
    Some n -> n
  | None -> 0

let build_recursive l b =
  let g = List.map (fun ((_,wf,_,_,_),_) -> wf) l in
    match g, l with
	[(n, CWfRec r)], [((id,_,bl,typ,def),ntn)] ->
	  ignore(build_wellfounded (id, out_n n, bl, typ, def) r false ntn false)

      | [(n, CMeasureRec r)], [((id,_,bl,typ,def),ntn)] ->
	  ignore(build_wellfounded (id, out_n n, bl, typ, def) r true ntn false)

      | _, _ when List.for_all (fun (n, ro) -> ro = CStructRec) g ->
	  let fixl = List.map (fun ((id,_,bl,typ,def),ntn) -> 
	    ({Command.fix_name = id; Command.fix_binders = bl; Command.fix_body = def; Command.fix_type = typ},ntn)) l 
	  in interp_recursive (Command.IsFixpoint g) fixl b
      | _, _ -> 
	  errorlabstrm "Subtac_command.build_recursive"
	    (str "Well-founded fixpoints not allowed in mutually recursive blocks")

let build_corecursive l b =
  let fixl = List.map (fun ((id,bl,typ,def),ntn) -> 
    ({Command.fix_name = id; Command.fix_binders = bl; Command.fix_body = def; Command.fix_type = typ},ntn))
    l in
  interp_recursive Command.IsCoFixpoint fixl b
