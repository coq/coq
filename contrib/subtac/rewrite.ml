open Evd
open Libnames
open Coqlib
open Natural
open Infer
open Term
open Names
open Scoq
open Pp
open Ppconstrnew
open Util

type recursion_info = {
  arg_name: identifier;
  arg_type: types; (* A *)
  wf_relation: constr; (* R : A -> A -> Prop *)
  wf_proof: constr; (* : well_founded R *)
  f_type: types; (* f: A -> Set *)
}

let id_of_name = function
    Name id -> id
  | Anonymous -> raise (Invalid_argument "id_of_name")

let rel_to_vars ctx constr =
  let rec aux acc = function
      (n, _, _) :: ctx -> 
	aux (Term.subst1 (mkVar n) acc) ctx
    | [] -> acc
  in aux constr ctx

let subst_ctx ctx c = 
  let rec aux ((ctx, n, c) as acc) = function
      (name, None, typ) :: tl -> 
	aux (((id_of_name name, None, rel_to_vars ctx typ) :: ctx), 
	     pred n, c) tl
    | (name, Some term, typ) :: tl ->
	let t' = Term.substnl [term] n c in
	  aux (ctx, n, t') tl
    | [] -> acc
  in 
  let (x, _, z) = aux ([], pred (List.length ctx), c) (List.rev ctx) in 
    (x, rel_to_vars x z)
	
(* Anotation needed for failed generalization *)
let named_context_of_ctx ctx : Sign.named_context = 
  List.fold_right 
    (fun (name, x, t) ctx -> 
       let x' = match x with 
	   Some e -> Some (rel_to_vars ctx e)
	 | None -> None
       and t' = rel_to_vars ctx t in
	 (id_of_name name, x', t') :: ctx) 
    ctx []
    
let env_of_ctx ctx : Environ.env =
  Environ.push_rel_context ctx (Global.env ())

let rels_of_ctx ctx = 
  let n = List.length ctx in
  Array.init n (fun i -> mkRel (n - i)) 

type prog_info = {
  mutable evm: evar_map;
  rec_info: recursion_info option;
}

let my_print_constr ctx term =
  Termops.print_constr_env (env_of_ctx ctx) term

let my_print_context ctx = 
  Termops.print_rel_context (env_of_ctx ctx)
      
let pair_of_array a = (a.(0), a.(1))
let make_name s = Name (id_of_string s)

let app_opt c e = 
  match c with
      Some constr -> constr e
    | None -> e	

(* Standard ? *)
let unlift n c = 
  let rec aux n acc =
    if n = 0 then acc
    else aux (pred n) (Termops.pop acc)
  in aux n c

let evar_args ctx = 
  let len = List.length ctx in
    Array.init len (fun i -> mkRel (succ i))

let if_branches c = 
  match kind_of_term c with
    | App (c, l) ->
	(match kind_of_term c with
	     Ind i ->
	       let len = Array.length l in
		 if len = 2
		 then
		   let (a, b) = pair_of_array l in
		     Some (i, (a,b))
		 else None
	   | _ -> None)
    | _ -> None

let disc_proj_exist ctx x =
  trace (str "disc_proj_exist: " ++ my_print_constr ctx x);
  match kind_of_term x with
    | App (c, l) ->
	(if Term.eq_constr c (Lazy.force sig_).proj1 
	   && Array.length l = 3 
	 then
	   (match kind_of_term l.(2) with
	        App (c, l) ->
		  (match kind_of_term c with
		       Construct c ->
			 if c = Term.destConstruct (Lazy.force sig_).intro
			   && Array.length l = 4
			 then
			   Some (l.(0), l.(1), l.(2), l.(3))
			 else None
		     | _ -> None)
	       | _ -> None)
	 else None)
    | _ -> None
      
let rec rewrite_type prog_info ctx ((loc, t) as lt) : Term.types * Term.types =
  trace (str "rewrite_type: " ++ print_dtype_loc [] lt);
  trace (str "context: " ++ my_print_context ctx);
  let aux prog_info ctx x = fst (rewrite_type prog_info ctx x) in
    match t with
	DTPi ((name, a), b, s) -> 
	  let ta = aux prog_info ctx a in
	  let ctx' = (snd name, None, ta) :: ctx in
	    (mkProd (snd name, ta, aux prog_info ctx' b)), mkSort (snd s)
	    
      | DTSigma ((name, a), b, s) ->
	  let ta = aux prog_info ctx a in
	  let ctx' = (snd name, None, ta) :: ctx in
	    mkApp ((Lazy.force existS).typ, 
		   [| ta; 
		      mkLambda 
			(snd name, ta, aux prog_info ctx' b) |]),
	  mkSort (snd s)
	    
      | DTSubset ((name, a), b, s) -> 
	  let ta = aux prog_info ctx a in
	  let name = Name (snd name) in
	  let ctx' = (name, None, ta) :: ctx in
	    (mkApp ((Lazy.force sig_).typ, 
		    [| ta; mkLambda (name, ta, aux prog_info ctx' b) |])),
	  mkSort (snd s)
	      
      | DTRel i -> 
	  let (_, term, typ) = List.nth ctx i in
	  let t = 
	    (*match term with
		Some t -> Term.lift (succ i) t
	      | None -> *)mkRel (succ i)
	  in t, Term.lift (succ i) typ
	    
      | DTApp (x, y, t, _) -> 
	  let (cx, tx), (cy, ty) = 
	    rewrite_type prog_info ctx x, rewrite_type prog_info ctx y 
	  in
	  let coercex, coqx = mutype prog_info ctx tx in
	  let narg, targ, tres =
	    match decompose_prod_n 1 coqx with
		[x, y], z -> x, y, z
	      | _ -> assert(false)
	  in	    
	    debug 2 (str "Coercion for type application: " ++
		       my_print_constr ctx cx ++ spc () 
		     ++ my_print_constr ctx cy);
	  let coercey = coerce prog_info ctx ty targ in
	  let t' = Term.subst1 (app_opt coercey cy) tres in
	  let term = mkApp (app_opt coercex cx, [|app_opt coercey cy|]) in
	    debug 1 (str "Term obtained after coercion (at application): " ++
		       my_print_constr ctx term);
	    term, t'
	      
      | DTCoq (t, dt, _) -> 
	  (* type should be equivalent to 'aux prog_info ctx dt' *)
	  t, Typing.type_of (env_of_ctx ctx) prog_info.evm t 
      | DTTerm (t, dt, _) -> rewrite_term prog_info ctx t
      | DTSort s -> mkSort (snd s), mkSort type_0 (* false *)
      | DTInd (_, t, i, s) -> 
	  let (_, ind) = Inductive.lookup_mind_specif (Global.env ()) i in
	    mkInd i, ind.Declarations.mind_nf_arity
	  
and mutype prog_info ctx t = 
  match disc_subset t with
      Some (u, p) -> 
	let f, ct = mutype prog_info ctx u in
	  (Some (fun x ->		   
		   app_opt f (mkApp ((Lazy.force sig_).proj1, 
				     [| u; p; x |]))),
	   ct)
    | None -> (None, t)

and muterm prog_info ctx t = mutype prog_info ctx t

and coerce' prog_info ctx x y : (Term.constr -> Term.constr) option =
  let subco () = subset_coerce prog_info ctx x y in
    trace (str "Coercion from " ++ (my_print_constr ctx x) ++ 
	     str " to "++ my_print_constr ctx y);
  match (kind_of_term x, kind_of_term y) with
    | Sort s, Sort s' -> 
	(match s, s' with
	     Prop x, Prop y when x = y -> None
	   | Prop _, Type _ -> None
	   | Type x, Type y when x = y -> None (* false *)
	   | _ -> subco ())
    | Prod (name, a, b), Prod (name', a', b') ->
	let c1 = coerce prog_info ctx a' a in
	let bsubst = Term.subst1 (app_opt c1 (mkRel 1)) b in
	let c2 = coerce prog_info ((name', None, a') :: ctx) bsubst b' in
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
	       let existS = Lazy.force existS and sig_ = Lazy.force sig_ in
		 if len = Array.length l' && len = 2
		   && i = i' && i = Term.destInd existS.typ 
		 then
		   begin (* Sigma types *)
		     debug 1 (str "In coerce sigma types");
		     let (a, pb), (a', pb') = 
		       pair_of_array l, pair_of_array l' 
		     in
		     let c1 = coerce prog_info ctx a a' in
		     let remove_head c = 
		       let (_, _, x) = Term.destProd c in
			 x
		     in
		     let b, b' = remove_head pb, remove_head pb' in
		     let b'subst = 
		       match c1 with
			   None -> b' 
			 | Some c1 -> Term.subst1 (c1 (mkRel 1)) b' 
		     in
		     let ctx' = (make_name "x", None, a) :: ctx in
		     let c2 = coerce prog_info ctx' b b'subst in
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

and coerce prog_info ctx (x : Term.constr) (y : Term.constr) 
    : (Term.constr -> Term.constr) option 
    =
  try let cstrs = Reduction.conv_leq (Global.env ()) x y in None
  with Reduction.NotConvertible -> coerce' prog_info ctx x y
      
and disc_subset x = 
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
	
and disc_exist ctx x =
  trace (str "Disc_exist: " ++ my_print_constr ctx x);
  match kind_of_term x with
    | App (c, l) ->
	(match kind_of_term c with
	     Construct c ->	       
	       if c = Term.destConstruct (Lazy.force sig_).intro
	       then Some (l.(0), l.(1), l.(2), l.(3))
	       else None
	   | _ -> None)
    | _ -> None
       
and subset_coerce prog_info ctx x y =
  match disc_subset x with
      Some (u, p) -> 
	let c = coerce prog_info ctx u y in
	let f x = 
	  app_opt c (mkApp ((Lazy.force sig_).proj1, 
			    [| u; p; x |]))
	in Some f
    | None ->
	match disc_subset y with
	    Some (u, p) ->
	      let c = coerce prog_info ctx x u in
	      let t = id_of_string "t" in
	      let evarinfo x =
		let cx = app_opt c x in
		let pcx = mkApp (p, [| cx |]) in
		let ctx', pcx' = subst_ctx ctx pcx in
		  cx, {
		    Evd.evar_concl = pcx';
		    Evd.evar_hyps = ctx';
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
			   mkCast (x, y))
	       with 
		   Reduction.NotConvertible ->	
		     subtyping_error 
		       (UncoercibleRewrite (my_print_constr ctx x,
					    my_print_constr ctx y))
		 | e -> raise e)
		
and rewrite_term prog_info ctx (t : dterm_loc) : Term.constr * Term.types =
  let rec aux ctx (loc, t) =
    match t with 
      | DRel i -> 
	  let (_, term, typ) = List.nth ctx i in
	  let t = mkRel (succ i) in
	    t, Term.lift (succ i) typ
	  
      | DLambda ((name, targ), e, t) -> 
	  let argt, argtt = rewrite_type prog_info ctx targ in
	  let coqe, et = 
	    rewrite_term prog_info ((snd name, None, argt) :: ctx) e 
	  in
	  let coqt = mkLambda (snd name, argt, coqe) 
	  and t = mkProd (snd name, argt, et) in
	    (coqt, t)
	    
      | DApp (f, e, t) -> 
	  let cf, ft = rewrite_term prog_info ctx f in
	  let coercef, coqt = muterm prog_info ctx ft in
	  let narg, targ, tres =
	    match decompose_prod_n 1 coqt with
		[x, y], z -> x, y, z
	      | _ -> assert(false)
	  in
	  let ce, te = rewrite_term prog_info ctx e in
	  debug 2 (str "Coercion for application" ++
		     my_print_constr ctx cf ++ spc () 
		   ++ my_print_constr ctx ce);
	  let call x = 
	    let len = List.length ctx in
	    let cf = app_opt coercef cf in
	      match prog_info.rec_info with 
		  Some r ->
		    (match kind_of_term cf with
			 Rel i when i = (pred len) ->
			   debug 3 (str "Spotted recursive call!");
			   let ctx', proof = 
			     subst_ctx ctx (mkApp (r.wf_relation, 
						   [| x; mkRel len |]))
			   in 
			   let evarinfo = 
			     { 
			       Evd.evar_concl = proof;
			       Evd.evar_hyps = ctx';
			       Evd.evar_body = Evd.Evar_empty;
			     }
			   in
			   let key = mknewexist () in
			     prog_info.evm <- Evd.add prog_info.evm key evarinfo;
			     mkApp (cf, [| x; mkEvar(key, evar_args ctx') |])
		       | _ -> mkApp (cf, [| x |]))
		| None -> mkApp (cf, [| x |])
	  in
	  let coercee = coerce prog_info ctx te targ in
	  let t' = Term.subst1 (app_opt coercee ce) tres in
	  let t = call (app_opt coercee ce) in
	    debug 2 (str "Term obtained after coercion (at application): " ++
		       Termops.print_constr_env (env_of_ctx ctx) t);
	    t, t'
	      
      | DSum ((x, t), (t', u), stype) ->
	  let ct, ctt = rewrite_term prog_info ctx t in
	  let ctxterm = (snd x, Some ct, ctt) :: ctx in
	  let ctxtype = (snd x, None, ctt) :: ctx in
	  let ct', tt' = rewrite_term prog_info ctxterm t' in
	  let cu, _ = rewrite_type prog_info ctxtype u in
	  let coercet' = coerce prog_info ctxtype tt' cu in
	  let lam = Term.subst1 ct (app_opt coercet' ct') in
	    debug 1 (str "Term obtained after coercion: " ++
		     Termops.print_constr_env (env_of_ctx ctx) lam);
	    
	  let t' = 
	    mkApp ((Lazy.force existS).typ, 
		   [| ctt; mkLambda (snd x, ctt, cu) |])
	  in
	    mkApp ((Lazy.force existS).intro, 
		   [| ctt ; mkLambda (snd x, ctt, cu);
		      ct; lam |]), t'
	      
      | DLetIn (x, e, e', t) ->
	  let ce, et' = rewrite_term prog_info ctx e in
	  let ce', t' = aux ((snd x, (Some ce), et') :: ctx) e' in
	    mkLetIn (snd x, ce, et', ce'), t'
	      
      | DLetTuple (l, e, e', t) ->
	  (* let (a, b) = e in e', l = [b, a] *)
	  let ce, et = rewrite_term prog_info ctx e in
	    debug 1 (str "Let tuple, e = " ++ 
		       my_print_constr ctx ce ++
		       str "type of e: " ++ my_print_constr ctx et);
	    let l, ctx' = 
	      let rec aux acc ctx = function
		  (x, t, t') :: tl ->
		    let tx, _ = rewrite_type prog_info ctx t in
		    let trest, _ = rewrite_type prog_info ctx t' in
		    let ctx' = (snd x, None, tx) :: ctx in
		      aux ((x, tx, trest) :: acc) ctx' tl
		| [] -> (acc), ctx
	      in aux [] ctx (List.rev l)
	    in
	      let ce', et' = aux ctx' e' in
	      let et' = unlift (pred (List.length l)) 
		(mkLambda (Anonymous, et, et')) in
		debug 1 (str "Let tuple, type of e': " ++
		       my_print_constr ctx' et');

	  let ind = destInd (Lazy.force existSind) in
	  let ci = Inductiveops.make_default_case_info 
	    (Global.env ()) RegularStyle ind 
	  in
	  let lambda = 
	    let rec aux acc = function
		(x, t, tt) :: (_ :: _) as tl ->
		  let lam = mkLambda (snd x, t, acc) in
		  let term = 
		    mkLambda (make_name "dummy", tt,
			      mkCase (ci, et', mkRel 1, [| lam |]))
		  in aux term tl
	      | (x, t, _) :: [] ->
		  let lam = mkLambda (snd x, t, acc) in
		    mkCase (ci, et', ce, [| lam |])
	      | _ -> assert(false)
	    in
	      match l with
		  (x, t, t') :: tl -> 
		    aux (mkLambda (snd x, t, ce')) tl
		| [] -> failwith "DLetTuple with empty list!"
	  in 
	    debug 1 (str "Let tuple term: " ++ my_print_constr ctx lambda);
	    lambda, et'
	      
      | DIfThenElse (b, e, e', t) ->
	  let name = Name (id_of_string "H") in
	  let (cb, tb) = aux ctx b in
	    (match if_branches tb with
		 Some (ind, (t, f)) ->
		   let ci = Inductiveops.make_default_case_info 
		     (Global.env ()) IfStyle ind 
		   in
		   let (ce, te), (ce', te') =
		     aux ((name, None, t) :: ctx) e, 
		     aux ((name, None, f) :: ctx) e'
		   in
		   let lam = mkLambda (Anonymous, tb, te) in
		   let true_case = 
		     mkLambda (name, t, ce)
		   and false_case = 
		     mkLambda (name, f, ce')
		   in
		     (mkCase (ci, lam, cb, [| true_case; false_case |])), 
		   (Termops.pop te)
	       | None -> failwith ("Ill-typed if"))
	       

      | DCoq (constr, t) -> constr, 
	  Typing.type_of (env_of_ctx ctx) prog_info.evm constr	  
      
  in aux ctx t

let global_kind :  Decl_kinds.global_kind = Decl_kinds.IsDefinition
let goal_kind = Decl_kinds.IsGlobal Decl_kinds.DefinitionBody
  
let make_fixpoint t id term = 
  let typ =
    mkProd (Name t.arg_name, t.arg_type,
	    mkProd(Anonymous,
		   mkApp (t.wf_relation, [| mkRel 1; mkRel 2 |]),
		   mkApp (t.f_type, [| mkRel 2 |])))
  in
  let term' = 
    mkLambda (Name id, typ, term)
  in
  let fix = mkApp (Lazy.force fix, 
		   [| t.arg_type; t.wf_relation; t.wf_proof;
		      t.f_type; 
		      mkLambda (Name t.arg_name, t.arg_type,
				term')
		   |]) 
  in fix

let subtac recursive id (s, t) =
  check_required_library ["Coq";"Init";"Datatypes"];
  check_required_library ["Coq";"Init";"Specif"];
  try
    let prog_info = { evm = Evd.empty; rec_info = None } in
    trace (str "Begin infer_type of given spec");
    let coqtype, coqtype', coqtype'', prog_info, ctx, coqctx =
      match recursive with
	  Some (n, t, rel, proof) -> 
	    let t' = infer_type [] t in
	    let namen = Name n in
	    let coqt = infer_type [namen, t'] s in
	    let t'', _ = rewrite_type prog_info [] t' in
	    let coqt', _ = rewrite_type prog_info [namen, None, t''] coqt in
	    let ftype = mkLambda (namen, t'', coqt') in
	    let proof = 
	      match proof with
		  ManualProof p -> p (* Check that t is a proof of well_founded rel *)
		| AutoProof ->
		    (try Lazy.force (Hashtbl.find wf_relations rel)
		     with Not_found ->
		       msg_warning
			 (str "No proof found for relation " 
			  ++ my_print_constr [] rel);
		       raise Not_found)
		| ExistentialProof ->
		    let wf_rel = mkApp (Lazy.force well_founded, [| t''; rel |]) in
		    let key = mknewexist () in
		      prog_info.evm <- Evd.add prog_info.evm key 
			{ Evd.evar_concl = wf_rel;
			  Evd.evar_hyps = [];
			  Evd.evar_body = Evd.Evar_empty };
		      mkEvar (key, [| |])
	    in
	    let prog_info = 
	      let rec_info = 
		{ arg_name = n;
		  arg_type = t'';
		  wf_relation = rel;
		  wf_proof = proof;
		  f_type = ftype;
		}
	      in { prog_info with rec_info = Some rec_info }
	    in
	    let coqtype = dummy_loc,
	      DTPi (((dummy_loc, namen), t'), coqt, 
		    sort_of_dtype_loc [] coqt)
	    in
	    let coqtype' = mkProd (namen, t'', coqt') in
	    let ctx = [(Name id, coqtype); (namen, t')] 
	    and coqctx = 
	      [(Name id, None, coqtype'); (namen, None, t'')] 
	    in coqt, coqt', coqtype', prog_info, ctx, coqctx
	| None ->
	    let coqt = infer_type [] s in
	    let coqt', _ = rewrite_type prog_info [] coqt in
	      coqt, coqt', coqt', prog_info, [], []
    in
    trace (str "Rewrite of coqtype done" ++ 
	     str "coqtype' = " ++ pr_term coqtype');
    let dterm, dtype = infer ctx t in
    trace (str "Inference done" ++ spc () ++
	     str "Infered term: " ++ print_dterm_loc ctx dterm ++ spc () ++
	     str "Infered type: " ++ print_dtype_loc ctx dtype);
    let dterm', dtype' = 
      fst (rewrite_term prog_info coqctx dterm),
      fst (rewrite_type prog_info coqctx dtype)
    in
    trace (str "Rewrite done" ++ spc () ++
	     str "Inferred Coq term:" ++ pr_term dterm' ++ spc () ++
	     str "Inferred Coq type:" ++ pr_term dtype' ++ spc () ++
	     str "Rewritten Coq type:" ++ pr_term coqtype');
    let coercespec = coerce prog_info coqctx dtype' coqtype' in
    trace (str "Specs coercion successfull");
    let realt = app_opt coercespec dterm' in
    trace (str "Term Specs coercion successfull" ++ 
	     my_print_constr coqctx realt);
    let realt = 
      match prog_info.rec_info with
	  Some t -> make_fixpoint t id realt
	| None -> realt
    in
    trace (str "Term after reduction" ++ my_print_constr coqctx realt);
    let evm = prog_info.evm in
    (try trace (str "Original evar map: " ++ Evd.pr_evar_map evm);
     with Not_found -> trace (str "Not found in pr_evar_map"));
    let tac = Refine.refine (evm, realt) in 
    msgnl (str "Starting proof");
    Command.start_proof id goal_kind coqtype'' (fun _ _ -> ());
    msgnl (str "Started proof");
    Pfedit.by tac
  with 
    | Typing_error e ->
	msg_warning (str "Type error in Program tactic:");
	let cmds = 
	  (match e with
	     | NonFunctionalApp (loc, x, mux) ->
		 str "non functional type app of term " ++ 
		   x ++ str " of (mu) type " ++ mux
	     | NonSigma (loc, t) ->
		 str "Term is not of Sigma type: " ++ t
	     | NonConvertible (loc, x, y) ->
		 str "Unconvertible terms:" ++ spc () ++
		   x ++ spc () ++ str "and" ++ spc () ++ y
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

    | e -> raise e
