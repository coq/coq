open Term
open Evarutil
open Evd
open Libnames
open Global
open Names
open Scoq
open Coqlib
open Pp
open Printer
open Subtac_errors
open Util
open Rawterm
open Context
open Eterm

(*  match t with
    | RRef(loc, gr) ->
    | RVar(loc, id) ->
    | REvar(loc, e_key, arglopt) ->
    | RPatVar(loc, (b * pvar)) ->
    | RApp(loc, fn, args) ->
    | RLambda(loc, name, typ, body) ->
    | RProd(loc, name, dom, codom) ->
    | RLetIn(loc, var, def, body) ->
    | RLetTuple(loc, names, (name, expr), def, body) ->
    | RIf(loc, cond, (name, expr), bodyl, bodyr) ->
    | RRec(loc, fix_kind, identifiersarr, rawdecllistarray,
	   rawconstrarray, rawconstrarray) ->
    | RSort(loc, rsort) ->
    | RHole(loc, hole_kind) ->
    | RCast(loc, expr, cast_kind, toexpr) ->
    | RCases _ (* of loc * rawconstr option *
	(rawconstr * (name * (loc * inductive * name list) option)) list * 
	(loc * identifier list * cases_pattern list * rawconstr) list *) ->
    | RDynamic(loc, dynobj) ->
	*)


type recursion_info = {
  arg_name: identifier;
  arg_type: types; (* A *)
  wf_relation: constr; (* R : A -> A -> Prop *)
  wf_proof: constr; (* : well_founded R *)
  f_type: types; (* f: A -> Set *)
  f_fulltype: types; (* Type with argument and wf proof product first *)
}

type prog_info = {
  evd : evar_defs ref;
  mutable evm: evar_map;
  rec_info: recursion_info option;
}

let my_print_constr env ctx term =
  Termops.print_constr_env (env_of_ctx env ctx) term

let my_print_context env ctx = 
  Termops.print_rel_context (env_of_ctx env ctx)

let my_print_rawconstr env ctx term =
  Printer.pr_rawconstr_env (env_of_ctx env ctx) term

let filter_defs l = List.filter (fun (_, c, _) -> c = None) l

let evar_args ctx = 
  let rec aux acc i = function
      (_, c, _) :: tl ->
	(match c with
	   | None -> aux (mkRel i :: acc) (succ i) tl
	   | Some _ -> aux acc (succ i) tl)
    | [] -> acc
  in Array.of_list (aux [] 1 ctx)
      
let evar_ctx prog_info ctx = 
  let ctx' = 
    match prog_info.rec_info with
      Some ri ->
	let len = List.length ctx in
	assert(len >= 2);
	let rec aux l acc = function
	    0 ->
	      (match l with
		   (id, _, recf) :: arg :: [] -> arg :: (id, None, ri.f_fulltype) :: acc
		 | _ -> assert(false))
	  | n -> (match l with
		      hd :: tl -> aux tl (hd :: acc) (pred n)
		    | _ -> assert(false))
	in
	  List.rev (aux ctx [] (len - 2))	    
    | None -> ctx
  in filter_defs ctx'


let lookup_local env ctx (loc, id) = 
  try 
    let name = Name id in
    let index, term, typ = Context.assoc_and_index name ctx in
    let index = succ index in
    let typ' = lift index typ in
      debug 3 (str "Resolved " ++ str (string_of_id id) ++ str " locally as rel " ++ int index ++ str " : " ++ 
	      my_print_constr env ctx typ' ++ str " in context: " ++ 
	      my_print_context env ctx);
      mkRel index, typ'
  with Not_found ->
  try 
    let (n,typ) = Termops.lookup_rel_id id (Environ.rel_context env) in
    let index = List.length ctx + n in
      mkRel index, (lift index) typ
  with Not_found ->
  try
    let (_,_,typ) = Environ.lookup_named id env in
      mkVar id, typ
  with Not_found ->
    Pretype_errors.error_var_not_found_loc loc id
    
let pair_of_array a = (a.(0), a.(1))
let make_name s = Name (id_of_string s)

let app_opt c e = 
  match c with
      Some constr -> constr e
    | None -> e	

let rec disc_subset x = 
  match kind_of_term x with
    | App (c, l) ->
	(match kind_of_term c with
	     Ind i ->
	       let len = Array.length l in
	       let sig_ = Lazy.force sig_ in
		 if len = 2 && i = Term.destInd sig_.typ
		 then
		   let (a, b) = pair_of_array l in
		     Some (a, b)
		 else None
	   | _ -> None)
    | _ -> None
	
and disc_exist env ctx x =
  trace (str "Disc_exist: " ++ my_print_constr env ctx x);
  match kind_of_term x with
    | App (c, l) ->
	(match kind_of_term c with
	     Construct c ->	       
	       if c = Term.destConstruct (Lazy.force sig_).intro
	       then Some (l.(0), l.(1), l.(2), l.(3))
	       else None
	   | _ -> None)
    | _ -> None


let disc_proj_exist env ctx x =
  trace (str "disc_proj_exist: " ++ my_print_constr env ctx x);
  match kind_of_term x with
    | App (c, l) ->
	(if Term.eq_constr c (Lazy.force sig_).proj1 
	   && Array.length l = 3 
	 then disc_exist env ctx l.(2)
	 else None)
    | _ -> None


let sort_rel s1 s2 = 
  match s1, s2 with
      Prop Pos, Prop Pos -> Prop Pos
    | Prop Pos, Prop Null -> Prop Null
    | Prop Null, Prop Null -> Prop Null
    | Prop Null, Prop Pos -> Prop Pos
    | Type _, Prop Pos -> Prop Pos
    | Type _, Prop Null -> Prop Null
    | _, Type _ -> s2

let rec mu prog_info env ctx t = 
  match disc_subset t with
      Some (u, p) -> 
	let f, ct = mu prog_info env ctx u in
	  (Some (fun x ->		   
		   app_opt f (mkApp ((Lazy.force sig_).proj1, 
				     [| u; p; x |]))),
	   ct)
    | None -> (None, t)

and coerce prog_info env ctx (x : Term.constr) (y : Term.constr) 
    : (Term.constr -> Term.constr) option 
  =
  let rec coerce_unify ctx etyp argtyp =
    match kind_of_term etyp, kind_of_term argtyp with
	Evar (ev, args), _ -> 
	  let evm = evars_of !(prog_info.evd) in
	    (*if is_defined evm ev then
	      coerce' ctx etyp (existential_value evm (ev, args))
	    else ( *)
	      prog_info.evd := evar_define ev argtyp !(prog_info.evd);
	      debug 1 (str "Defining evar (evar to type) " ++ int ev ++ str " := " ++ my_print_constr env ctx argtyp);
	      None
      | _, Evar (ev, args) ->
	  let evm = evars_of !(prog_info.evd) in
	    if is_defined evm ev then
	      coerce' ctx etyp (existential_value evm (ev, args))
	    else (
	      debug 1 (str "Defining evar (term to evar)" ++ int ev ++ str " := " ++ my_print_constr env ctx etyp);
	      prog_info.evd := evar_define ev etyp !(prog_info.evd);
	      None)
      | _, _ -> coerce' ctx etyp argtyp
  and coerce' ctx x y : (Term.constr -> Term.constr) option =
    let subco () = subset_coerce ctx x y in
      trace (str "Coercion from " ++ (my_print_constr env ctx x) ++ 
	     str " to "++ my_print_constr env ctx y);
      match (kind_of_term x, kind_of_term y) with
	| Sort s, Sort s' -> 
	    (match s, s' with
		 Prop x, Prop y when x = y -> None
	       | Prop _, Type _ -> None
	       | Type x, Type y when x = y -> None (* false *)
	       | _ -> subco ())
	| Prod (name, a, b), Prod (name', a', b') ->
	    let c1 = coerce_unify ctx a' a in
	    let c2 = coerce_unify ((name', None, a') :: ctx) b b' in
	      (match c1, c2 with
		   None, None -> None
		 | _, _ ->
		     Some
		       (fun f -> 
			  mkLambda (name', a',
				    app_opt c2
				      (mkApp (Term.lift 1 f, 
					      [| app_opt c1 (mkRel 1) |])))))
		
	| App (c, l), App (c', l') ->
	    (match kind_of_term c, kind_of_term c' with
		 Ind i, Ind i' ->
		   let len = Array.length l in
		   let existS = Lazy.force existS in
		     if len = Array.length l' && len = 2
		       && i = i' && i = Term.destInd existS.typ 
		     then
		       begin (* Sigma types *)
			 debug 1 (str "In coerce sigma types");
			 let (a, pb), (a', pb') = 
			   pair_of_array l, pair_of_array l' 
			 in
			 let c1 = coerce_unify ctx a a' in
			 let remove_head c = 
			   let (_, _, x) = Term.destProd c in
			     x
			 in
			 let b, b' = remove_head pb, remove_head pb' in
			 let ctx' = (make_name "x", None, a) :: ctx in
			 let c2 = coerce_unify ctx' b b' in
			   match c1, c2 with
			       None, None -> None
			     | _, _ ->
				 Some 
				   (fun x ->
				      let x, y = 
					app_opt c1 (mkApp (existS.proj1,
							   [| a; pb; x |])),
					app_opt c2 (mkApp (existS.proj2, 
							   [| a; pb'; x |]))
				      in
					mkApp (existS.intro, [| x ; y |]))
		       end
		     else subco ()
	       | _ ->  subco ())
	| _, _ ->  subco ()

  and subset_coerce ctx x y =
    match disc_subset x with
	Some (u, p) -> 
	  let c = coerce_unify ctx u y in
	  let f x = 
	    app_opt c (mkApp ((Lazy.force sig_).proj1, 
			      [| u; p; x |]))
	  in Some f
      | None ->
	  match disc_subset y with
	    Some (u, p) ->
	      let c = coerce_unify ctx x u in
	      let evarinfo x =
		let cx = app_opt c x in
		let pcx = mkApp (p, [| cx |]) in
		let ctx', pcx' = subst_ctx ctx pcx in
		  cx, {
		    Evd.evar_concl = pcx';
		    Evd.evar_hyps = 
			 Environ.val_of_named_context (evar_ctx prog_info ctx');
		    Evd.evar_body = Evd.Evar_empty;
		  }
	      in
		Some 
		  (fun x ->
		     let key = mknewexist () in
		     let cx, evi = evarinfo x in
		       prog_info.evm <- Evd.add prog_info.evm key evi;
		       (mkApp 
			  ((Lazy.force sig_).intro, 
			   [| u; p; cx; 
		  	      mkEvar (key, evar_args ctx) |])))
	  | None -> 
	      (try 
		 let cstrs = Reduction.conv (Global.env ()) x y 
		 in
		   ignore(Univ.merge_constraints cstrs (Global.universes ()));
		   Some (fun x ->
			   mkCast (x, DEFAULTcast, y))
	       with 
		   Reduction.NotConvertible ->	
		     subtyping_error 
		       (UncoercibleRewrite (my_print_constr env ctx x,
					    my_print_constr env ctx y))
		 | e -> raise e)


  in
    try ignore(Reduction.conv_leq (Global.env ()) x y); None
    with Reduction.NotConvertible -> coerce_unify ctx x y (* head recutions needed *)
    

and interp prog_info env ctx t : constr * constr (* The term -> its coq translation, its coq (not algorithmic) type *) =
  let error s = anomaly ("subtac.interp: " ^ s) in
    debug 1 (str "Interpreting term: " ++ my_print_rawconstr env ctx t ++ str " in env : " ++
	     my_print_context env ctx);

  let rec type_app ctx (locf, coqf, ftyp) (e : rawconstr) = 
    let coercef, support = mu prog_info env ctx ftyp in
    let narg, argtyp, restyp =
      try 
	match decompose_prod_n 1 support with
	    [x, y], z -> x, y, z
	  | _ -> typing_error (NonFunctionalApp (locf, my_print_constr env ctx coqf, my_print_constr env ctx support,
						my_print_rawconstr env ctx e))
      with _ -> typing_error (NonFunctionalApp (locf, my_print_constr env ctx coqf, my_print_constr env ctx support,
					       my_print_rawconstr env ctx e))
    in
    let coqe, etyp = aux ctx e in
    let _ = debug 2 (str "Coercion for application: " ++
		     my_print_constr env ctx coqf ++ str " : " ++ 
		     my_print_constr env ctx ftyp ++ str " and " ++
		     my_print_constr env ctx coqe ++ str " : " ++
		     my_print_constr env ctx etyp)
    in
    let coercee = coerce prog_info env ctx etyp argtyp in
    let coqe' = app_opt coercee coqe in
    let restype' = Term.subst1 coqe' restyp in
    let call =
      let len = List.length ctx in
      let cf = app_opt coercef coqf in
	match prog_info.rec_info with 
	    Some r ->
	      (match kind_of_term cf with
		   Rel i when i = (pred len) ->
		     debug 3 (str "Spotted recursive call!");
		     let ctx', proof = 
		       subst_ctx ctx (mkApp (r.wf_relation, 
					     [| coqe'; mkRel len |]))
		     in 
		     let evarinfo = 
		       { 
			 Evd.evar_concl = proof;
			 Evd.evar_hyps = 
			   Environ.val_of_named_context 
			     (evar_ctx prog_info ctx');
			 Evd.evar_body = Evd.Evar_empty;
		       }
		     in
		     let key = mknewexist () in
		       prog_info.evm <- Evd.add prog_info.evm key evarinfo;
		       mkApp (cf, [| coqe'; mkEvar(key, evar_args ctx) |])
		 | _ -> mkApp (cf, [| coqe' |]))
	  | None -> mkApp (cf, [| coqe' |])
    in
      debug 2 (str "Term obtained after coercion (at application): " ++
	       Termops.print_constr_env (env_of_ctx env ctx) call);
      call, restype'
  
  and aux ctx = function
    | RRef(loc, gr) -> 
	(match gr with
	   | VarRef var ->
	       let coqt = type_of_global gr in
		 mkVar var, coqt
	   | ConstRef const -> 
	       let coqt = type_of_global gr in 
	      	 mkConst const, coqt
	   | IndRef ind ->
 	       let coqt = type_of_global gr in 
	      	 mkInd ind, coqt
	   | ConstructRef constr ->
 	       let coqt = type_of_global gr in 
	      	 mkConstruct constr, coqt)

    | RVar(loc, id) -> lookup_local env ctx (loc, id)
	
    | RApp(loc, fn, args) as x ->
	let loc = loc_of_rawconstr fn in
	  debug 1 (str "Interpreting application: " ++ my_print_rawconstr env ctx x);
	let coqfn, fntyp = aux ctx fn in
(*	let coqfn, fntyp, args = 
	  match kind_of_term coqfn with 
	      Ind i ->
		let len = List.length args in
		  debug 1 (my_print_constr env ctx coqfn ++ str " inductive applied to " ++ int len ++ str " arguments: " ++
			   List.fold_left (fun acc arg -> acc ++ str " " ++ my_print_rawconstr env ctx arg) (str "") args
			  );
		let sig_ = Lazy.force sig_ in
		  if len = 2 && i = Term.destInd sig_.typ
		  then		    
		    let b = match args with [a;b] -> b | _ -> error "Partially applied subset type constructor" in
		    let coqb, btyp = aux ctx b in
		      (match kind_of_term coqb with 
			 | Lambda (n, t, b) ->
			     mkApp (coqfn, [|t; coqb|]), mkSort (mk_Set), []
			 | _ -> 
			     debug 1 (my_print_constr env ctx btyp ++ str " is not a lambda") ;
			     error "Ill-typed subset type: ")
		  else if len = 3 && i = Term.destInd (Lazy.force eqind)
		  then		    
		    let b,c = match args with [a;b;c] -> b,c | _ -> error "Partially applied eq type constructor" in
		    let coqb, btyp = aux ctx b in
		      mkApp (coqfn, [|btyp; coqb|]), mkProd (Anonymous, btyp, mkSort (mk_Prop)), [c]
		  else (
		    debug 1 (str "Not an eq or sig: " ++ my_print_constr env ctx coqfn);
		    coqfn, fntyp, args)
	    | x -> 
		debug 1 (str "Not an inductive: " ++ my_print_constr env ctx coqfn);
		coqfn, fntyp, args
	in*)
	let _, term, typ = 
	  List.fold_left (fun (loc, coqfn, fntyp) (e : rawconstr) -> 
			    let coqfn', fntyp' = type_app ctx (loc, coqfn, fntyp) e in
			      join_loc loc (loc_of_rawconstr e), coqfn', fntyp') 
	    (loc, coqfn, fntyp) args 
	in term, typ

    | RLambda(loc, name, argtyp, body) ->
    	let coqargtyp, argtyptyp = aux ctx argtyp in
	let coqbody, bodytyp = aux ((name, None, coqargtyp) :: ctx) body in
	let prod = mkProd (name, coqargtyp, bodytyp) in
	  (* Check it is well sorted *)
	(*let coqprod, prodtyp = aux ctx prod in
	  if not (isSort prodtyp) then
	    typing_error (IllSorted (loc, my_print_constr env ctx prodtyp));*)
	let coqlambda = mkLambda (name, coqargtyp, coqbody) in
	  (coqlambda, prod)
	      	      
    | RProd(loc, name, dom, codom) -> 
	let coqdom, domtyp = aux ctx dom in
	let coqcodom, codomtyp = aux ((name, None, coqdom) :: ctx) codom in
	let s1, s2 = destSort domtyp, destSort codomtyp in
	let s3 = sort_rel s1 s2 in
	  mkProd (name, coqdom, coqcodom), mkSort s3
	    
    | RLetIn(loc, var, def, body) ->
	let coqdef, deftyp = aux ctx def in
	let coqbody, bodytyp = aux ((var, Some coqdef, deftyp) :: ctx) body in
	  mkLetIn (var, coqdef, deftyp, coqbody), 
	  Term.subst1 coqdef bodytyp

    | RLetTuple(loc, names, (name, expr), def, body) -> error "Let tuple : Not implemented"

    | RIf(loc, cond, (name, expr), bodyl, bodyr) ->
	error "If: not implemented"

    | RRec(loc, fix_kind, identifiersarr, rawdecllistarray,
	   rawconstrarray, rawconstrarray2) ->
	error "Rec : Not implemented"

    | RSort(loc, rsort) -> 
	let x, y =
	  (match rsort with
	       RProp Pos -> mk_Set, type_0
	     | RProp Null -> mk_Prop, type_0
	     | RType None -> type_0, type_0
	     | RType (Some u) -> Type u, type_0)
	in mkSort x, mkSort y

    | RHole(loc, k) -> 
	let ty = Evarutil.e_new_evar prog_info.evd env ~src:(loc,InternalHole) (Termops.new_Type ()) in
	  (Evarutil.e_new_evar prog_info.evd env ~src:(loc,k) ty), ty

    | RCast(loc, expr, cast_kind, toexpr) -> 
	let coqexpr, exprtyp = aux ctx expr in
	let coqtoexpr, toexprtyp = aux ctx toexpr in
	  mkCast (coqexpr, cast_kind, coqtoexpr), toexprtyp


    | RCases _ (* of loc * rawconstr option *
	(rawconstr * (name * (loc * inductive * name list) option)) list * 
	(loc * identifier list * cases_pattern list * rawconstr) list *) ->
	anomaly "Not implemented"

    | REvar(loc, e_key, arglopt) -> 
	let evm = evars_of !(prog_info.evd) in
	let evi = map evm e_key in
	let args = 
	  match arglopt with 
	      Some l -> Array.of_list (List.map (fun e -> fst (aux ctx e)) l)
	    | None -> [||]
	in
	  (match evi.evar_body with
	       Evar_defined v -> mkApp (v, args), evi.evar_concl
	     | _ -> 
		 mkEvar (e_key, args), evi.evar_concl)

    | RPatVar(loc, (b, pvar)) -> error "Found a pattern variable in a term to be typed"
    | RDynamic(loc, d) -> 
	if (Dyn.tag d) = "constr" then
	  let c = Pretyping.constr_out d in
	  let j = (Retyping.get_type_of env Evd.empty c) in
	    j, c
	else
	  user_err_loc (loc,"subtac.interp",(str "Not a constr tagged Dynamic"))
  in aux ctx t

	    
let global_kind = Decl_kinds.IsDefinition Decl_kinds.Definition
let goal_kind = Decl_kinds.Global, Decl_kinds.DefinitionBody Decl_kinds.Definition
  
let make_fixpoint t id term = 
  let term' = mkLambda (Name id, t.f_fulltype, term) in
    mkApp (Lazy.force fix, 
	   [| t.arg_type; t.wf_relation; t.wf_proof; t.f_type; 
	      mkLambda (Name t.arg_name, t.arg_type, term') |])       

let merge_evms x y = 
  Evd.fold (fun ev evi evm -> Evd.add evm ev evi) x y

let subtac' recursive id env (s, t) =
  check_required_library ["Coq";"Init";"Datatypes"];
  check_required_library ["Coq";"Init";"Specif"];
  try
    let evm = Evd.empty in
    let coqintern = Constrintern.intern_constr evm env in
    let coqinterp = Constrintern.interp_constr evm env in
    let s, t = coqintern s, coqintern t in
    let prog_info = { evd = ref (Evd.create_evar_defs evm); evm = evm; rec_info = None } in
    trace (str "Begin infer_type of given spec");
      let (evs, coqs) = Pretyping.understand_tcc evm env s and (evt, coqt) = Pretyping.understand_tcc evm env t in
	debug 1 (str "Coq understands as : " ++ my_print_constr env [] coqs ++ str " : " ++ my_print_constr env [] coqt);
	

    let coqtype, prog_info, ctx =
      match recursive with
	  Some (n, t, rel, proof) -> 
	    let coqrel = coqinterp rel in
	    let t', ttyp = interp prog_info env [] (coqintern t) in
	    let namen = Name n in
	    let coqs, styp = interp prog_info env [namen, None, t'] s in
	    let ftype = mkProd (namen, t', coqs) in
	    let fulltype =
	      mkProd (namen, t',
		      mkProd(Anonymous,
			     mkApp (coqrel, [| mkRel 1; mkRel 2 |]),
			     Term.subst1 (mkRel 2) coqs))
	    in
	    let proof = 
	      match proof with
		  ManualProof p -> (* TODO: Check that t is a proof of well_founded rel *)
		    coqinterp p
		| AutoProof ->
		    (try Lazy.force (Hashtbl.find wf_relations coqrel)
		     with Not_found ->
		       msg_warning
			 (str "No proof found for relation " 
			  ++ my_print_constr env [] coqrel);
		       raise Not_found)
		| ExistentialProof ->
		    let wf_rel = mkApp (Lazy.force well_founded, [| t'; coqrel |]) in
		    let key = mknewexist () in
		      prog_info.evm <- Evd.add prog_info.evm key 
			{ Evd.evar_concl = wf_rel;
			  Evd.evar_hyps = Environ.empty_named_context_val;
			  Evd.evar_body = Evd.Evar_empty };
		      mkEvar (key, [| |])
	    in
	    let prog_info = 
	      let rec_info = 
		{ arg_name = n;
		  arg_type = t';
		  wf_relation = coqrel;
		  wf_proof = proof;
		  f_type = ftype;
		  f_fulltype = fulltype;
		}
	      in { prog_info with rec_info = Some rec_info }
	    in
	    let coqctx = 
	      [(Name id, None, ftype); (namen, None, t')] 
	    in coqs, prog_info, coqctx
	| None ->
	    let coqs, _ = interp prog_info env [] s in
	      coqs, prog_info, []
    in
    trace (str "Rewrite of spec done:" ++ my_print_constr env ctx coqtype);
    let coqt, ttyp = interp prog_info env ctx t in
    trace (str "Interpretation done:" ++ spc () ++
	   str "Interpreted term: " ++ my_print_constr env ctx coqt ++ spc () ++
	   str "Infered type: " ++ my_print_constr env ctx ttyp);
    
    let coercespec = coerce prog_info env ctx ttyp coqtype in
    trace (str "Specs coercion successfull");
    let realt = app_opt coercespec coqt in
    trace (str "Term Specs coercion successfull" ++ 
	     my_print_constr env ctx realt);
    let realt = 
      match prog_info.rec_info with
	  Some t -> make_fixpoint t id realt
	| None -> realt
    in
    let realt = Evarutil.whd_ise (evars_of !(prog_info.evd)) realt in
    trace (str "Coq term" ++ my_print_constr env [] realt);
    trace (str "Coq type" ++ my_print_constr env [] coqtype);
    let evm = prog_info.evm in
      (try trace (str "Original evar map: " ++ Evd.pr_evar_map evm);
       with Not_found -> trace (str "Not found in pr_evar_map"));
    let tac = Eterm.etermtac (evm, realt) in 
    msgnl (str "Starting proof");
    Command.start_proof id goal_kind coqtype (fun _ _ -> ());
    msgnl (str "Started proof");
    Pfedit.by tac
  with 
    | Typing_error e ->
	msg_warning (str "Type error in Program tactic:");
	let cmds = 
	  (match e with
	     | NonFunctionalApp (loc, x, mux, e) ->
		 str "non functional application of term " ++ 
		 e ++ str " to function " ++ x ++ str " of (mu) type " ++ mux
	     | NonSigma (loc, t) ->
		 str "Term is not of Sigma type: " ++ t
	     | NonConvertible (loc, x, y) ->
		 str "Unconvertible terms:" ++ spc () ++
		   x ++ spc () ++ str "and" ++ spc () ++ y
	     | IllSorted (loc, t) ->
		 str "Term is ill-sorted:" ++ spc () ++ t
	  )
	in msg_warning cmds
	     
    | Subtyping_error e ->
	msg_warning (str "(Program tactic) Subtyping error:");
	let cmds = 
	  match e with
	    | UncoercibleInferType (loc, x, y) ->
		str "Uncoercible terms:" ++ spc ()
		++ x ++ spc () ++ str "and" ++ spc () ++ y
	    | UncoercibleInferTerm (loc, x, y, tx, ty) ->
		str "Uncoercible terms:" ++ spc ()
		++ tx ++ spc () ++ str "of" ++ spc () ++ str "type" ++ spc () ++ x
		++ str "and" ++ spc() ++ ty ++ spc () ++ str "of" ++ spc () ++ str "type" ++ spc () ++ y
	    | UncoercibleRewrite (x, y) ->
		str "Uncoercible terms:" ++ spc ()
		++ x ++ spc () ++ str "and" ++ spc () ++ y
	in msg_warning cmds

    | e -> 
	msg_warning (str "Uncatched exception: " ++ str (Printexc.to_string e))
	(*raise e*)

let subtac recursive id env (s, t) =
  subtac' recursive id (Global.env ()) (s, t)
