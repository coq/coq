
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

open Tacinterp
open Vernacexpr
open Notation

module SPretyping = Subtac_pretyping.Pretyping
open Subtac_utils
open Pretyping

(*********************************************************************)
(* Functions to parse and interpret constructions *)

let interp_gen kind isevars env 
               ?(impls=([],[])) ?(allow_soapp=false) ?(ltacvars=([],[]))
               c =
  let c' = Constrintern.intern_gen (kind=IsType) ~impls ~allow_soapp ~ltacvars (Evd.evars_of !isevars) env c in
  let c'' = Subtac_interp_fixpoint.rewrite_cases c' in
    Evd.evars_of !isevars, SPretyping.pretype_gen isevars env ([],[]) kind c''
    
let interp_constr isevars env c =
  interp_gen (OfType None) isevars env c 

let interp_type isevars env ?(impls=([],[])) c =
  interp_gen IsType isevars env ~impls c

let interp_casted_constr isevars env ?(impls=([],[])) c typ =
  interp_gen (OfType (Some typ)) isevars env ~impls c 

let interp_open_constr isevars env c =
  SPretyping.pretype_gen isevars env ([], []) (OfType None) 
    (Constrintern.intern_constr (Evd.evars_of !isevars) env c)

let interp_constr_judgment isevars env c =
  let s, j = SPretyping.understand_judgment_tcc (Evd.evars_of !isevars) env
    (Constrintern.intern_constr (Evd.evars_of !isevars) env c)
  in 
    Evd.create_evar_defs s, j

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

let recursive_message v =
  match Array.length v with
    | 0 -> error "no recursive definition"
    | 1 -> (Printer.pr_global v.(0) ++ str " is recursively defined")
    | _ -> hov 0 (prvect_with_sep pr_coma Printer.pr_global v ++
		    spc () ++ str "are recursively defined")

let build_recursive (lnameargsardef:(fixpoint_expr * decl_notation) list) boxed =
  let sigma = Evd.empty
  and env0 = Global.env()
  and protos = List.map (fun ((f, n, _, _, _),_) -> f,n) lnameargsardef
  in 
  let lnameargsardef = 
    List.map (fun (f, d) -> Subtac_interp_fixpoint.rewrite_fixpoint env0 protos (f, d))
      lnameargsardef
  in
  let lrecnames = List.map (fun ((f,_,_,_,_),_) -> f) lnameargsardef 
  and nv = List.map (fun ((_,n,_,_,_),_) -> n) lnameargsardef
  in
  (* Build the recursive context and notations for the recursive types *)
  let (rec_sign,rec_impls,arityl) = 
    List.fold_left 
      (fun (env,impls,arl) ((recname,_,bl,arityc,_),_) -> 
        let arityc = Command.generalize_constr_expr arityc bl in
	let isevars = ref (Evd.create_evar_defs sigma) in
        let isevars, arity = interp_type isevars env0 arityc in
	let impl = 
	  if Impargs.is_implicit_args()
	  then Impargs.compute_implicits env0 arity
	  else [] in
	let impls' =(recname,([],impl,compute_arguments_scope arity))::impls in
          (Environ.push_named (recname,None,arity) env, impls', (isevars, arity)::arl))
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
	  (fun ((_,_,bl,_,def),_) (evm, arity) ->
             let def = abstract_constr_expr def bl in
               interp_casted_constr (ref (Evd.create_evar_defs evm)) rec_sign ~impls:([],rec_impls)
		def arity)
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
      trace (str "Declaring: " ++ pr_id fi);
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
      (*  (* The others are declared as normal definitions *)
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
    and arrec = Array.map snd arrec
    in declare arrec recvec
  in
  let recdefs = Array.length defrec in
    trace (int recdefs ++ str " recursive definitions");
    (* Solve remaining evars *)
  let rec solve_evars i acc = 
    if i < recdefs then
      let (evm, def) = defrec.(i) in
	if Evd.dom evm = [] then 
	  solve_evars (succ i) (def :: acc)
	else
	  let _,typ = arrec.(i) in
	  let id = namerec.(i) in
	    (* Generalize by the recursive prototypes  *)
	  let def = 
	    Termops.it_mkNamedLambda_or_LetIn def (Environ.named_context rec_sign)
	  and typ = 
	    Termops.it_mkNamedProd_or_LetIn typ (Environ.named_context rec_sign) in
	  let tac = Eterm.etermtac (evm, def) in 
	  let _ =
	    trace (str "Starting proof of a fixpoint def:" ++ spc () ++ my_print_constr env0 def ++
		   spc () ++ str " with goal: " ++ my_print_constr env0 typ ++
		   spc () ++ str " with evar map = " ++ Evd.pr_evar_map evm)
	  in
	    begin
	      Command.start_proof (id_of_string (string_of_id id ^ "_evars"))  goal_kind typ
		(fun _ gr -> 
		   let _ = trace (str "Got a proof of: " ++ pr_global gr) in
		   let constant = match gr with Libnames.ConstRef c -> c
		     | _ -> assert(false)
		   in
		     try 
		       let def = Environ.constant_value (Global.env ()) constant in
		       let _ = trace (str "Got constant value") in		 
		       let _, c = decompose_lam_n recdefs def in
		       let _ = trace (str "Fixpoint body is: " ++ spc () ++ my_print_constr (Global.env ()) c) in
			 solve_evars (succ i) (c :: acc)
		     with Environ.NotEvaluableConst cer ->
		       match cer with
			   Environ.NoBody -> trace (str "Constant has no body")
			 | Environ.Opaque -> trace (str "Constant is opaque")
		);
	      trace (str "Started proof");
	      Pfedit.by tac;
	      trace (str "Applied eterm tac");
	    end
    else declare (List.rev acc)
  in solve_evars 0 []

    
