open Printer
open Util
open Term
open Termops 
open Names 
open Declarations
open Pp
open Entries
open Hiddentac
open Evd
open Tacmach
open Proof_type
open Tacticals
open Tactics
open Indfun_common
open Libnames

let msgnl = Pp.msgnl

let do_observe () = 
  Tacinterp.get_debug () <> Tactic_debug.DebugOff  


let observe strm =
  if do_observe ()
  then Pp.msgnl strm
  else ()

let observennl strm =
  if do_observe ()
  then begin Pp.msg strm;Pp.pp_flush () end
  else ()




let do_observe_tac s tac g =
 try let v = tac g in (* msgnl (goal ++ fnl () ++ (str s)++(str " ")++(str "finished")); *) v
 with e ->
   let goal = begin try (Printer.pr_goal (sig_it g)) with _ -> assert false end in
   msgnl (str "observation "++ s++str " raised exception " ++ 
	    Cerrors.explain_exn e ++ str " on goal " ++ goal ); 
   raise e;;


let observe_tac s tac g =
  if do_observe ()
  then do_observe_tac (str s) tac g
  else tac g


let tclTRYD tac = 
  if  !Options.debug  || do_observe ()
  then (fun g -> try (* do_observe_tac ""  *)tac g with _ -> tclIDTAC g)
  else tac


let list_chop ?(msg="") n l = 
  try 
    list_chop n l 
  with Failure (msg') -> 
    failwith (msg ^ msg')
  

let make_refl_eq type_of_t t  =
  let refl_equal_term = Lazy.force refl_equal in
  mkApp(refl_equal_term,[|type_of_t;t|])


type pte_info = 
    { 
      proving_tac : (identifier list ->  Tacmach.tactic);
      is_valid : constr -> bool
    }

type ptes_info = pte_info Idmap.t

type 'a dynamic_info = 
    { 
      nb_rec_hyps : int;
      rec_hyps : identifier list ; 
      eq_hyps : identifier list;
      info : 'a
    }

type body_info = constr dynamic_info 
      

let finish_proof dynamic_infos g = 
  observe_tac "finish" 
    ( h_assumption)
    g
	  

let refine c = 
  Tacmach.refine_no_check c

let thin l = 
  Tacmach.thin_no_check l
  

let cut_replacing id t tac :tactic= 
  tclTHENS (cut t)
    [ tclTHEN (thin_no_check [id]) (introduction_no_check id);
      tac 
    ]

let intro_erasing id = tclTHEN (thin [id]) (introduction id)



let rec_hyp_id = id_of_string "rec_hyp"

let is_trivial_eq t = 
  match kind_of_term t with 
    | App(f,[|_;t1;t2|]) when eq_constr f (Lazy.force eq) -> 
	eq_constr t1 t2
    | _ -> false 


let rec incompatible_constructor_terms t1 t2 = 
  let c1,arg1 = decompose_app t1 
  and c2,arg2 = decompose_app t2 
  in 
  (not (eq_constr t1 t2)) &&
    isConstruct c1 && isConstruct c2 && 
    (
      not (eq_constr c1 c2) || 
	List.exists2 incompatible_constructor_terms arg1 arg2
    )

let is_incompatible_eq t = 
  match kind_of_term t with 
    | App(f,[|_;t1;t2|]) when eq_constr f (Lazy.force eq) -> 
	incompatible_constructor_terms t1 t2
    | _ -> false 

let change_hyp_with_using msg hyp_id t tac : tactic = 
  fun g -> 
    let prov_id = pf_get_new_id hyp_id g in 
    tclTHENS
      (observe_tac msg (forward (Some  (tclCOMPLETE tac)) (Genarg.IntroIdentifier prov_id) t))
      [tclTHENLIST 
      [	
	observe_tac "change_hyp_with_using thin" (thin [hyp_id]);
	observe_tac "change_hyp_with_using rename " (h_rename prov_id hyp_id)
      ]] g

exception TOREMOVE


let prove_trivial_eq h_id context (type_of_term,term) = 
  let nb_intros = List.length context in 
  tclTHENLIST
    [
      tclDO nb_intros intro; (* introducing context *)
      (fun g -> 
	 let context_hyps =  
	   fst (list_chop ~msg:"prove_trivial_eq : " nb_intros (pf_ids_of_hyps g)) 
	 in
	 let context_hyps' = 
	   (mkApp(Lazy.force refl_equal,[|type_of_term;term|]))::
	     (List.map mkVar context_hyps)
	 in
	 let to_refine = applist(mkVar h_id,List.rev context_hyps') in 
	 refine to_refine g
      )
    ]


let isAppConstruct t = 
  if isApp t 
  then isConstruct (fst (destApp t))
  else false 


let nf_betaiotazeta = Reductionops.local_strong Reductionops.whd_betaiotazeta 
  

let rec subst_rel_map sub t = 
  match kind_of_term t with
  | Rel k -> 
      begin 
	try 
	  Intmap.find (k+1) sub
	with Not_found -> 
	  t
      end
  | _ -> map_constr (subst_rel_map sub) t
     

let change_eq env sigma hyp_id (context:Sign.rel_context) x t end_of_type  = 
  let nochange msg  = 
    begin 
(*       observe (str ("Not treating ( "^msg^" )") ++ pr_lconstr t    ); *)
      failwith "NoChange"; 
    end
  in    
  if not (noccurn 1 end_of_type)
  then nochange "dependent"; (* if end_of_type depends on this term we don't touch it  *)
    if not (isApp t) then nochange "not an equality";
    let f_eq,args = destApp t in
    if not (eq_constr f_eq (Lazy.force eq)) then nochange "not an equality";
    let t1 = args.(1) 
    and t2 = args.(2) 
    and t1_typ = args.(0)
    in 
    if not (closed0 t1) then nochange "not a closed lhs";    
    let rec compute_substitution sub t1 t2 = 
      if isRel t2 
      then 
	let t2 = destRel t2  in 
	begin 
	  try 
	    let t1' = Intmap.find t2 sub in 
	    if not (eq_constr t1 t1') then nochange "twice bound variable";
	    sub
	  with Not_found -> 
	    assert (closed0 t1);
	    Intmap.add t2 t1 sub
	end
      else if isAppConstruct t1 && isAppConstruct t2 
      then 
	begin
	  let c1,args1 = destApp t1 
	  and c2,args2 = destApp t2 
	  in 
	  if not (eq_constr c1 c2) then anomaly "deconstructing equation";
	  array_fold_left2 compute_substitution sub args1 args2
	end
      else 
	if (eq_constr t1 t2) then sub else nochange "cannot solve"
    in
    let sub = compute_substitution Intmap.empty t1 t2 in 
    let end_of_type_with_pop = pop end_of_type in (*the equation will be removed *) 
    let new_end_of_type =
      Intmap.fold
	(fun i t end_of_type -> lift 1 (substnl  [t] (i-1) end_of_type))
	sub
	end_of_type_with_pop
    in
    let old_context_length = List.length context + 1 in
    let witness_fun = 
      mkLetIn(Anonymous,make_refl_eq t1_typ t1,t,
	       mkApp(mkVar hyp_id,Array.init old_context_length (fun i -> mkRel (old_context_length - i)))
	      )
    in
    let new_type_of_hyp,ctxt_size,witness_fun = 
      list_fold_left_i 
	(fun i (end_of_type,ctxt_size,witness_fun) ((x',b',t') as decl) -> 
	   try 
	     let witness = Intmap.find i sub in 
	     if b' <> None then anomaly "can not redefine a rel!";
	     (pop end_of_type,ctxt_size,mkLetIn(x',witness,t',witness_fun))
	   with Not_found  -> 
	     (mkProd_or_LetIn decl end_of_type, ctxt_size + 1, mkLambda_or_LetIn decl witness_fun)
	)
	1 
	(new_end_of_type,0,witness_fun)
	context
    in
    let new_type_of_hyp = Reductionops.nf_betaiota  new_type_of_hyp in 
    let new_ctxt,new_end_of_type = 
      Sign.decompose_prod_n_assum ctxt_size new_type_of_hyp 
    in 
    let prove_new_hyp : tactic = 
      tclTHEN
	(tclDO ctxt_size intro)
	(fun g ->
	   let all_ids = pf_ids_of_hyps g in 
	   let new_ids,_  = list_chop ctxt_size all_ids in 
	   let to_refine = applist(witness_fun,List.rev_map mkVar new_ids) in 
	   refine to_refine g
	)
    in
    let simpl_eq_tac = 
      change_hyp_with_using "prove_pattern_simplification" hyp_id new_type_of_hyp prove_new_hyp
    in
(*     observe (str "In " ++ Ppconstr.pr_id hyp_id ++  *)
(* 	       str "removing an equation " ++ fnl ()++  *)
(* 	       str "old_typ_of_hyp :=" ++ *)
(* 	       Printer.pr_lconstr_env *)
(* 	       env *)
(* 	       (it_mkProd_or_LetIn ~init:end_of_type ((x,None,t)::context)) *)
(* 	     ++ fnl () ++ *)
(* 	       str "new_typ_of_hyp := "++  *)
(* 	       Printer.pr_lconstr_env env new_type_of_hyp ++ fnl () *)
(* 	     ++ str "old context := " ++ pr_rel_context env context ++ fnl ()  *)
(* 	     ++ str "new context := " ++ pr_rel_context env new_ctxt ++ fnl ()  *)
(* 	     ++ str "old type  := " ++ pr_lconstr end_of_type ++ fnl ()  *)
(* 	     ++ str "new type := " ++ pr_lconstr new_end_of_type ++ fnl ()  *)
(* ); *)
    new_ctxt,new_end_of_type,simpl_eq_tac


let is_property ptes_info t_x full_type_of_hyp = 
  if isApp t_x 
  then 
    let pte,args = destApp t_x in 
    if isVar pte && array_for_all closed0 args 
    then 
      try 
	let info = Idmap.find (destVar pte) ptes_info in 
	info.is_valid full_type_of_hyp	  
      with Not_found -> false 
    else false 
  else false 

let isLetIn t = 
  match kind_of_term t with 
    | LetIn _ -> true 
    | _ -> false 


let h_reduce_with_zeta = 	 
  h_reduce 
    (Rawterm.Cbv
       {Rawterm.all_flags 
	with Rawterm.rDelta = false; 		 
       })
  


let rewrite_until_var arg_num eq_ids : tactic =
  let test_var g = 
    let _,args = destApp (pf_concl g) in 
    isVar args.(arg_num)
  in
  let rec do_rewrite eq_ids g  = 
    if test_var g 
    then tclIDTAC g
    else
      match eq_ids with 
	| [] -> anomaly "Cannot find a way to prove recursive property";
	| eq_id::eq_ids -> 
	    tclTHEN 
	      (tclTRY (Equality.rewriteRL (mkVar eq_id)))
	      (do_rewrite eq_ids)
	      g
  in
  do_rewrite eq_ids


let rec_pte_id = id_of_string "Hrec" 
let clean_hyp_with_heq ptes_infos eq_hyps hyp_id env sigma = 
  let coq_False = Coqlib.build_coq_False () in 
  let coq_True = Coqlib.build_coq_True () in 
  let coq_I = Coqlib.build_coq_I () in 
  let rec scan_type  context type_of_hyp : tactic = 
    if isLetIn type_of_hyp then 
      let real_type_of_hyp = it_mkProd_or_LetIn ~init:type_of_hyp context in
      let reduced_type_of_hyp = nf_betaiotazeta real_type_of_hyp in 
      (* length of context didn't change ? *)
      let new_context,new_typ_of_hyp = 
	 Sign.decompose_prod_n_assum (List.length context) reduced_type_of_hyp
      in
        tclTHENLIST 
	[
	  h_reduce_with_zeta
	    (Tacticals.onHyp hyp_id)
	  ;
	  scan_type new_context new_typ_of_hyp 
	  
	]
    else if isProd type_of_hyp 
    then 
      begin 
	let (x,t_x,t') = destProd type_of_hyp in	
	let actual_real_type_of_hyp = it_mkProd_or_LetIn ~init:t' context in 
	if is_property ptes_infos t_x actual_real_type_of_hyp then
	  begin
	    let pte,pte_args =  (destApp t_x) in 
	    let (* fix_info *) prove_rec_hyp = (Idmap.find (destVar pte) ptes_infos).proving_tac in 
	    let popped_t' = pop t' in 
	    let real_type_of_hyp = it_mkProd_or_LetIn ~init:popped_t' context in 
	    let prove_new_type_of_hyp = 
	      let context_length = List.length context in 
	      tclTHENLIST
		[ 
		  tclDO context_length intro; 
		  (fun g ->  
		     let context_hyps_ids = 
		       fst (list_chop ~msg:"rec hyp : context_hyps"
			      context_length (pf_ids_of_hyps g))
		     in
		     let rec_pte_id = pf_get_new_id rec_pte_id g in 
		     let to_refine = 
		       applist(mkVar hyp_id,
			       List.rev_map mkVar (rec_pte_id::context_hyps_ids)
			      )
		     in
		     observe_tac "rec hyp "
		       (tclTHENS
		       (assert_as true (Genarg.IntroIdentifier rec_pte_id) t_x)
		       [observe_tac "prove rec hyp" (prove_rec_hyp eq_hyps);
			observe_tac "prove rec hyp"
			  (refine to_refine)
		       ])
		       g
		  )
		]
	    in
	    tclTHENLIST 
	      [
		observe_tac "hyp rec" 
		  (change_hyp_with_using "rec_hyp_tac" hyp_id real_type_of_hyp prove_new_type_of_hyp);
		scan_type context popped_t'
	      ]
	  end
	else if eq_constr t_x coq_False then 
	  begin
(* 	    observe (str "Removing : "++ Ppconstr.pr_id hyp_id++  *)
(* 		       str " since it has False in its preconds " *)
(* 		    ); *)
	    raise TOREMOVE;  (* False -> .. useless *)
	  end
	else if is_incompatible_eq t_x then raise TOREMOVE (* t_x := C1 ... =  C2 ... *) 
	else if eq_constr t_x coq_True  (* Trivial => we remove this precons *)
	then 
(* 	    observe (str "In "++Ppconstr.pr_id hyp_id++  *)
(* 		       str " removing useless precond True" *)
(* 		    );  *)
	  let popped_t' = pop t' in
	  let real_type_of_hyp = 
	    it_mkProd_or_LetIn ~init:popped_t' context 
	  in 
	  let prove_trivial =  
	    let nb_intro = List.length context in 
	    tclTHENLIST [
	      tclDO nb_intro intro;
	      (fun g -> 
		 let context_hyps = 
		   fst (list_chop ~msg:"removing True : context_hyps "nb_intro (pf_ids_of_hyps g))
		 in
		 let to_refine = 
		   applist (mkVar hyp_id,
			    List.rev (coq_I::List.map mkVar context_hyps)
			   )
		 in
		 refine to_refine g
	      )
	    ]
	  in
	  tclTHENLIST[
	    change_hyp_with_using "prove_trivial" hyp_id real_type_of_hyp 
	      (observe_tac "prove_trivial" prove_trivial);
	    scan_type context popped_t'
	  ]
	else if is_trivial_eq t_x 
	then (*  t_x :=  t = t   => we remove this precond *) 
	  let popped_t' = pop t' in
	  let real_type_of_hyp =
	    it_mkProd_or_LetIn ~init:popped_t' context
	  in
	  let _,args = destApp t_x in
	  tclTHENLIST
	    [
	      change_hyp_with_using
		"prove_trivial_eq"
		hyp_id
		real_type_of_hyp
		(observe_tac "prove_trivial_eq" (prove_trivial_eq hyp_id context (args.(0),args.(1))));
	      scan_type context popped_t'
	    ] 
	else 
	  begin
	    try 
	      let new_context,new_t',tac = change_eq env sigma hyp_id context x t_x t' in 
	      tclTHEN
		tac 
		(scan_type new_context new_t')
	    with Failure "NoChange" -> 
	      (* Last thing todo : push the rel in the context and continue *) 
	      scan_type ((x,None,t_x)::context) t'
	  end
      end
    else
      tclIDTAC
  in 
  try 
    scan_type [] (Typing.type_of env sigma (mkVar hyp_id)), [hyp_id]
  with TOREMOVE -> 
    thin [hyp_id],[]


let clean_goal_with_heq ptes_infos continue_tac dyn_infos  = 
  fun g -> 
    let env = pf_env g 
    and sigma = project g 
    in
    let tac,new_hyps = 
      List.fold_left ( 
	fun (hyps_tac,new_hyps) hyp_id ->
	  let hyp_tac,new_hyp = 
	    clean_hyp_with_heq ptes_infos dyn_infos.eq_hyps hyp_id env sigma 
	  in
	  (tclTHEN hyp_tac hyps_tac),new_hyp@new_hyps
      )
	(tclIDTAC,[])
	dyn_infos.rec_hyps
    in
    let new_infos = 
      { dyn_infos with 
	  rec_hyps = new_hyps; 
	  nb_rec_hyps  = List.length new_hyps
      }
    in
    tclTHENLIST 
      [
	tac ;
	(continue_tac new_infos)
      ]
      g    

let heq_id = id_of_string "Heq"

let treat_new_case ptes_infos nb_prod continue_tac term dyn_infos = 
  fun g -> 
    let heq_id = pf_get_new_id heq_id g in 
    let nb_first_intro = nb_prod - 1 - dyn_infos.nb_rec_hyps in
    tclTHENLIST
      [ 
	(* We first introduce the variables *) 
	tclDO nb_first_intro (intro_avoiding dyn_infos.rec_hyps);
	(* Then the equation itself *)
	introduction_no_check heq_id;
	(* Then the new hypothesis *) 
	tclMAP introduction_no_check dyn_infos.rec_hyps;
	observe_tac "after_introduction" (fun g' -> 
	   (* We get infos on the equations introduced*)
	   let new_term_value_eq = pf_type_of g' (mkVar heq_id) in 
	   (* compute the new value of the body *)
	   let new_term_value =
	     match kind_of_term new_term_value_eq with
	       | App(f,[| _;_;args2 |]) -> args2
	       | _ ->
(* 		   observe (pr_gls g' ++ fnl () ++ str "last hyp is" ++ *)
(* 			      pr_lconstr_env (pf_env g') new_term_value_eq *)
(* 			   ); *)
		   anomaly "cannot compute new term value"
	   in
	 let fun_body =
	   mkLambda(Anonymous,
		    pf_type_of g' term,
		    replace_term term (mkRel 1) dyn_infos.info
		   )
	 in
	 let new_body = pf_nf_betaiota g' (mkApp(fun_body,[| new_term_value |])) in
	 let new_infos = 
	   {dyn_infos with 
	      info = new_body;
	      eq_hyps = heq_id::dyn_infos.eq_hyps
	   }
	 in 
	 clean_goal_with_heq ptes_infos continue_tac new_infos  g'
      )
    ]
      g


let instanciate_hyps_with_args (do_prove:identifier list -> tactic) hyps args_id = 
  let args = Array.of_list (List.map mkVar  args_id) in 
  let instanciate_one_hyp hid = 
    tclORELSE
      ( (* we instanciate the hyp if possible  *)
	fun g -> 
	  let prov_hid = pf_get_new_id hid g in
	  tclTHENLIST[
	    forward None (Genarg.IntroIdentifier prov_hid) (mkApp(mkVar hid,args));
	    thin [hid];
	    h_rename prov_hid hid
	  ] g
      )
      ( (*
	  if not then we are in a mutual function block 
	  and this hyp is a recursive hyp on an other function.
	  
	  We are not supposed to use it while proving this 
	  principle so that we can trash it 
	  
	*)
	(fun g -> 
(* 	   observe (str "Instanciation: removing hyp " ++ Ppconstr.pr_id hid); *)
	   thin [hid] g
	)
      )
  in
  if args_id = []  
  then 
    tclTHENLIST [
      tclMAP (fun hyp_id -> h_reduce_with_zeta (Tacticals.onHyp hyp_id)) hyps;
      do_prove hyps
    ]
  else
    tclTHENLIST
      [
	tclMAP (fun hyp_id -> h_reduce_with_zeta (Tacticals.onHyp hyp_id)) hyps;
	tclMAP instanciate_one_hyp hyps;
	(fun g ->  
	   let all_g_hyps_id = 
	     List.fold_right Idset.add (pf_ids_of_hyps g) Idset.empty
	   in 
	   let remaining_hyps = 
	     List.filter (fun id -> Idset.mem id all_g_hyps_id) hyps
	   in
	   do_prove remaining_hyps g
	  )
      ]

let build_proof 
    (interactive_proof:bool)
    (fnames:constant list)
    ptes_infos
    dyn_infos
    : tactic =
  let rec build_proof_aux do_finalize dyn_infos : tactic = 
    fun g -> 
      
(*      observe (str "proving on " ++ Printer.pr_lconstr_env (pf_env g) term);*)
	match kind_of_term dyn_infos.info with 
	  | Case(_,_,t,_) -> 
	      let g_nb_prod = nb_prod (pf_concl g) in
	      let type_of_term = pf_type_of g t in
	      let term_eq =
		make_refl_eq type_of_term t
	      in
  	      tclTHENSEQ
		[
		  h_generalize (term_eq::List.map mkVar dyn_infos.rec_hyps);
		  thin dyn_infos.rec_hyps;
		  pattern_option [[-1],t] None;
		  h_simplest_case t;
		  (fun g' -> 
		     let g'_nb_prod = nb_prod (pf_concl g') in 
		     let nb_instanciate_partial = g'_nb_prod - g_nb_prod in 
		     observe_tac "treat_new_case" 
		       (treat_new_case  
		       ptes_infos
		       nb_instanciate_partial 
		       (build_proof do_finalize) 
		       t 
		       dyn_infos)
		       g'
		  )
		  
		] g
	  | Lambda(n,t,b) ->
	      begin
		match kind_of_term( pf_concl g) with
		  | Prod _ ->
		      tclTHEN
			intro
			(fun g' ->
			   let (id,_,_) = pf_last_hyp g' in
			   let new_term = 
			     pf_nf_betaiota g' 
			       (mkApp(dyn_infos.info,[|mkVar id|])) 
			   in
			   let new_infos = {dyn_infos with info = new_term} in
			   let do_prove new_hyps = 
			     build_proof do_finalize 
			       {new_infos with
			       	  rec_hyps = new_hyps; 
				  nb_rec_hyps  = List.length new_hyps
			       }
			   in 
			   observe_tac "Lambda" (instanciate_hyps_with_args do_prove new_infos.rec_hyps [id]) g'
			     (* 			   build_proof do_finalize new_infos g' *)
			) g
		  | _ ->
		      do_finalize dyn_infos g 
	      end
	  | Cast(t,_,_) -> 
	      build_proof do_finalize {dyn_infos with info = t} g
	  | Const _ | Var _ | Meta _ | Evar _ | Sort _ | Construct _ | Ind _ ->
	      do_finalize dyn_infos g
	  | App(_,_) ->
	      let f,args = decompose_app dyn_infos.info in
	      begin
		match kind_of_term f with
		  | App _ -> assert false (* we have collected all the app in decompose_app *)
		  | Var _ | Construct _ | Rel _ | Evar _ | Meta _  | Ind _ | Sort _ | Prod _ ->
		      let new_infos = 
			{ dyn_infos with 
			    info = (f,args)
			}
		      in
		      build_proof_args do_finalize new_infos  g
		  | Const c when not (List.mem c fnames) ->
		      let new_infos = 
			{ dyn_infos with 
			    info = (f,args)
			}
		      in
(* 		      Pp.msgnl (str "proving in " ++ pr_lconstr_env (pf_env g) dyn_infos.info); *)
		      build_proof_args do_finalize new_infos g
		  | Const _ ->
		      do_finalize dyn_infos  g
		  | Lambda _ -> 
		      let new_term = Reductionops.nf_beta dyn_infos.info in 
		      build_proof do_finalize {dyn_infos with info = new_term} 
			g
		  | LetIn _ -> 
		      let new_infos = 
			{ dyn_infos with info = nf_betaiotazeta dyn_infos.info } 
		      in 

		      tclTHENLIST 
			[tclMAP 
			   (fun hyp_id -> h_reduce_with_zeta (Tacticals.onHyp hyp_id)) 
			   dyn_infos.rec_hyps;
			 h_reduce_with_zeta Tacticals.onConcl;
			 build_proof do_finalize new_infos
			] 
			g
		  | Cast(b,_,_) -> 
		      build_proof do_finalize {dyn_infos with info = b } g
		  | Case _ | Fix _ | CoFix _ ->
		      let new_finalize dyn_infos = 
			let new_infos = 
			  { dyn_infos with 
			      info = dyn_infos.info,args
			  }
			in 
			build_proof_args do_finalize new_infos 
		      in 
		      build_proof new_finalize {dyn_infos  with info = f } g
	      end
	  | Fix _ | CoFix _ ->
	      error ( "Anonymous local (co)fixpoints are not handled yet")

	  | Prod _ -> error "Prod" 
	  | LetIn _ -> 
	      let new_infos = 
		{ dyn_infos with 
		    info = nf_betaiotazeta dyn_infos.info 
		}
	      in 

	      tclTHENLIST 
		[tclMAP 
		   (fun hyp_id -> h_reduce_with_zeta (Tacticals.onHyp hyp_id)) 
		   dyn_infos.rec_hyps;
		 h_reduce_with_zeta Tacticals.onConcl;
		 build_proof do_finalize new_infos
		] g
	  | Rel _ -> anomaly "Free var in goal conclusion !" 
  and build_proof do_finalize dyn_infos g =
(*     observe (str "proving with "++Printer.pr_lconstr term++ str " on goal " ++ pr_gls g); *)
     (build_proof_aux do_finalize dyn_infos) g
  and build_proof_args do_finalize dyn_infos (* f_args'  args *) :tactic =
    fun g ->
(*      if Tacinterp.get_debug () <> Tactic_debug.DebugOff  *)
(*      then msgnl (str "build_proof_args with "  ++  *)
(* 		   pr_lconstr_env (pf_env g) f_args' *)
(* 		); *)
      let (f_args',args) = dyn_infos.info in 
      let tac : tactic =
	fun g -> 
	match args with
	  | []  ->
	      do_finalize {dyn_infos with info = f_args'} g 
	  | arg::args ->
(* 		observe (str "build_proof_args with arg := "++ pr_lconstr_env (pf_env g) arg++ *)
(* 			fnl () ++  *)
(* 			pr_goal (Tacmach.sig_it g) *)
(* 			); *)
	      let do_finalize dyn_infos =
		let new_arg = dyn_infos.info in 
		(* 		tclTRYD *)
		(build_proof_args
		   do_finalize
		   {dyn_infos with info = (mkApp(f_args',[|new_arg|])), args}
		)
	      in
	      build_proof do_finalize 
		{dyn_infos with info = arg }
		g
      in
      observe_tac "build_proof_args" (tac ) g
   in
   let do_finish_proof dyn_infos = 
     (* tclTRYD *) (clean_goal_with_heq 
      ptes_infos
      finish_proof dyn_infos)
  in
  observe_tac "build_proof"
    (build_proof do_finish_proof dyn_infos) 












(* Proof of principles from structural functions *) 
let is_pte_type t =
  isSort (snd (decompose_prod t))
    
let is_pte (_,_,t) = is_pte_type t




type static_fix_info = 
    {
      idx : int;
      name : identifier;
      types : types;
      nb_realargs : int
    }

let prove_rec_hyp fix_info  =
  { proving_tac = 
      (fun  eq_hyps -> tclTHEN 
	(rewrite_until_var (fix_info.idx - 1) eq_hyps)
	(fun g -> 
	   let _,pte_args = destApp (pf_concl g) in 
	   let rec_hyp_proof = 
	     mkApp(mkVar fix_info.name,array_get_start pte_args) 
	   in
	   refine rec_hyp_proof g
	))
  ;
    is_valid = fun _ -> true 
  }


exception Not_Rec
    

let prove_princ_for_struct interactive_proof fun_num fnames all_funs _naprams : tactic =
   fun goal ->
(*      observe (str "Proving principle for "++ str (string_of_int fun_num) ++ str "th function : " ++  *)
(* 		pr_lconstr (mkConst fnames.(fun_num))); *)
     let princ_type = pf_concl goal in
     let princ_info = compute_elim_sig princ_type in
     let get_body const =
       match (Global.lookup_constant const ).const_body with
	 | Some b ->
	     let body = force b in
	     Tacred.cbv_norm_flags
	       (Closure.RedFlags.mkflags [Closure.RedFlags.fZETA])
	       (Global.env ())
	       (Evd.empty)
	       body
	 | None -> error ( "Cannot define a principle over an axiom ")
     in
     let fbody = get_body fnames.(fun_num) in
     let params : identifier list ref = ref [] in
     let predicates : identifier list ref = ref [] in
     let args : identifier list ref = ref [] in
     let branches : identifier list ref = ref [] in
     let pte_to_fix = ref Idmap.empty in
     let fbody_with_params = ref None in
     let intro_with_remembrance  ref number : tactic =
       tclTHEN
	 ( tclDO number intro )
	 (fun g ->
	    let last_n = list_chop number (pf_hyps g) in
	    ref :=  List.map (fun (id,_,_) -> id) (fst last_n)@ !ref;
	    tclIDTAC g
	 )
     in
     let rec partial_combine body params =
       match kind_of_term body,params with
	 | Lambda (x,t,b),param::params ->
	     partial_combine (subst1 param b) params
	 | Fix(infos),_ ->
	     body,params, Some (infos)
	 | _ -> body,params,None
     in
     let build_pte_to_fix (offset:int) params predicates
	 ((idxs,fix_num),(na,typearray,ca))  (avoid,_) =
(*        let true_params,_ =  list_chop offset params  in  *)
       let true_params = List.rev params in
       let avoid = ref avoid in
       let res = list_fold_left_i
	 (fun i acc pte_id  ->
	    let this_fix_id = fresh_id !avoid "fix___" in
	    avoid := this_fix_id::!avoid;
(* 	    let this_body = substl (List.rev fnames_as_constr) ca.(i) in  *)
	    let realargs,_ = decompose_lam ca.(i) in 
	    let n_realargs = List.length realargs - List.length params in 
(* 	    observe (str "n_realargs := " ++ str (string_of_int n_realargs)); *)
(* 	    observe (str "n_fix := " ++ str (string_of_int(Array.length ca))); *)
(* 	    observe (str "body := " ++ pr_lconstr ca.(i)); *)

	    let new_type = prod_applist typearray.(i) true_params in
	    let new_type_args,_ = decompose_prod new_type in
	    let nargs = List.length new_type_args in
	    let pte_args =
	      (* 	      let rev_args = List.rev_map (fun (id,_,_) -> mkVar id) new_type_args in  *)
	      let f = applist((* all_funs *)mkConst fnames.(i),true_params) in
	      let app_f = mkApp(f,Array.init nargs (fun i -> mkRel(nargs - i))) in
	      (Array.to_list (Array.init nargs (fun i -> mkRel(nargs - i))))@[app_f]
	    in
	    let app_pte = applist(mkVar pte_id,pte_args) in
	    let new_type = compose_prod new_type_args app_pte in
	    
	    let fix_info = 
	      {
		idx = idxs.(i) - offset + 1;
		name = this_fix_id; 
		types = new_type;
		nb_realargs = n_realargs
	      }
	    in
	    pte_to_fix := Idmap.add  pte_id fix_info !pte_to_fix;
	    fix_info::acc
	 )
	 0
	 []
	 predicates
       in
       !avoid,List.rev res
     in
     let mk_fixes : tactic =
       fun g ->
	 let body_p,params',fix_infos =
	   partial_combine fbody (List.rev_map mkVar  !params)
	 in
	 fbody_with_params := Some body_p;
	 let offset  = List.length params' in
	 let not_real_param,true_params =
	   list_chop
	     ((List.length !params ) - offset)
	     !params
	 in
	 params := true_params; args := not_real_param;
(* 	 observe (str "mk_fixes : params are "++  *)
(* 		    prlist_with_sep spc *)
(* 		    (fun id -> pr_lconstr (mkVar id)) *)
(* 		    !params *)
(* 		 ); *)
	 let new_avoid,infos =
	   option_fold_right
	     (build_pte_to_fix
		offset
		(List.map mkVar !params)
		(List.rev !predicates)
	     )
	     fix_infos
	     ((pf_ids_of_hyps g),[])
	 in
	 let pre_info,infos = list_chop fun_num infos in
	 match pre_info,infos with
	   | [],[] -> tclIDTAC g
	   | _,this_fix_info::infos' ->
	       let other_fix_info =
		 List.map 
		   (fun fix_info -> fix_info.name,fix_info.idx,fix_info.types) 
		   (pre_info@infos')
	       in
	       if other_fix_info = []
		  then h_fix (Some this_fix_info.name) this_fix_info.idx g
		  else h_mutual_fix this_fix_info.name this_fix_info.idx other_fix_info g
	   | _,[] -> anomaly "Not a valid information"
     in
     let do_prove ptes_to_fixes args branches : tactic =
       fun g ->
	 let nb_intros_to_do = List.length (fst (Sign.decompose_prod_assum (pf_concl g))) in 
(* 	 observe (str "nb_intros_to_do " ++ str (string_of_int nb_intros_to_do)); *)
	 tclTHEN 
	   (tclDO nb_intros_to_do intro)
	   (fun g -> 
	      match kind_of_term (pf_concl g) with
		| App(pte,pte_args) when isVar pte ->
		    begin
		      let pte = destVar pte in
		      try
			if not (Idmap.mem pte ptes_to_fixes) then raise Not_Rec;
			let nparams = List.length !params in
			let args_as_constr = List.map mkVar  args in
			let other_args = fst (list_chop nb_intros_to_do (pf_ids_of_hyps g)) in 
			let other_args_as_constr = List.map mkVar  other_args in 
			let rec_num,new_body =
			  let idx' = list_index pte (List.rev !predicates)  - 1 in
			  let f = fnames.(idx') in
			  let body_with_params = match !fbody_with_params with Some f -> f | _ -> anomaly ""
			  in
			  let name_of_f = Name ( id_of_label (con_label f)) in
			  let ((rec_nums,_),(na,_,bodies)) = destFix body_with_params in
			  let idx'' = list_index name_of_f (Array.to_list na) - 1 in
			  let body = substl (List.rev (Array.to_list all_funs)) bodies.(idx'') in
			  let body = Reductionops.nf_beta (applist(body,(List.rev_map mkVar !params))) in
			  rec_nums.(idx'') - nparams ,body
			in
			let applied_body_with_real_args =
			  Reductionops.nf_betaiota
			    (applist(new_body,List.rev args_as_constr))
			in
			let applied_body = 
(* 			  Reductionops.nf_beta *)
			  Reductionops.nf_betaiota 
			    (applist(applied_body_with_real_args,List.rev other_args_as_constr))
			in
(* 			observe (str "applied_body_with_real_args := "++ pr_lconstr_env (pf_env g) applied_body_with_real_args); *)
(* 			observe (str "applied_body := "++ pr_lconstr_env (pf_env g) applied_body); *)
			let do_prove branches applied_body =
			  build_proof
			    interactive_proof
			    (Array.to_list fnames)
			    (Idmap.map prove_rec_hyp ptes_to_fixes)
			    branches
			    applied_body
			in
			let replace_and_prove =
			  tclTHENS
			    (fun g -> (Equality.replace (array_last pte_args) applied_body) g)
			    [
			      tclTHENLIST 
				[
				  generalize other_args_as_constr;
				  thin other_args;
				  clean_goal_with_heq 
				    (Idmap.map prove_rec_hyp ptes_to_fixes)
				    do_prove 
				    {
				      nb_rec_hyps = List.length branches;
				      rec_hyps = branches;
				      info = applied_body_with_real_args;
				      eq_hyps = [];
				    } ];
			      let id = try List.nth (List.rev args_as_constr) (rec_num) with _ -> anomaly ("Cannot find recursive argument of function ! ") in
			      let id_as_induction_constr = Tacexpr.ElimOnConstr id in 
			      (tclTHENSEQ
				 [new_destruct [id_as_induction_constr] None Genarg.IntroAnonymous;(* (h_simplest_case id) *)
				  intros_reflexivity
				 ])
			    ]
			in
			(observe_tac "doing replacement" ( replace_and_prove)) g
		      with Not_Rec ->
			let fname = destConst (fst (decompose_app (array_last pte_args))) in
			tclTHEN
		     (unfold_in_concl [([],Names.EvalConstRef fname)])
			  (observe_tac "" 
			     (fun g' ->
				let body = array_last (snd (destApp (pf_concl g'))) in 
				let dyn_infos = 
				  { nb_rec_hyps = List.length branches;
				    rec_hyps = branches;
				    info = body;
				    eq_hyps = []
				  }
				in
				let do_prove = 
				  build_proof
				    interactive_proof
				    (Array.to_list fnames)
				    (Idmap.map prove_rec_hyp ptes_to_fixes)
				in
				clean_goal_with_heq (Idmap.map prove_rec_hyp ptes_to_fixes)
				  do_prove dyn_infos g'
			     )
			  )
			  g
		    end
		| _ -> assert false
	   ) g
     in
     tclTHENSEQ
       [
	 (fun g -> observe_tac "introducing params" (intro_with_remembrance  params princ_info.nparams) g);
	 (fun g -> observe_tac "introducing predicate" (intro_with_remembrance predicates  princ_info.npredicates) g);
	 (fun g -> observe_tac "introducing branches" (intro_with_remembrance branches princ_info.nbranches) g);
	 (fun g -> observe_tac "declaring fix(es)" mk_fixes g);
	 (fun g -> 
	    let nb_real_args = 
	      let pte_app = snd (Sign.decompose_prod_assum (pf_concl g)) in 
	      let pte = fst (decompose_app pte_app) in
	      try 
		let fix_info = Idmap.find (destVar pte) !pte_to_fix in
		fix_info.nb_realargs
	      with Not_found -> (* Not a recursive function *) 
		nb_prod (pf_concl g)
	    in 
	    observe_tac "" (tclTHEN
	      (tclDO nb_real_args (observe_tac "intro" intro)) 
	      (fun g' -> 
		 let realargs_ids = fst (list_chop ~msg:"args" nb_real_args (pf_ids_of_hyps g')) in 
		 let do_prove_on_branches branches : tactic =
		   observe_tac "proving" (do_prove !pte_to_fix ( realargs_ids) branches)
		 in
		 observe_tac "instanciating rec hyps"
		   (instanciate_hyps_with_args do_prove_on_branches !branches  (List.rev realargs_ids))
		   g'
	      ))
	      g
	 )
       ]
       goal



(* Proof of principles of general functions *) 
let h_id = Recdef.h_id
and hrec_id = Recdef.hrec_id
and acc_inv_id = Recdef.acc_inv_id
and ltof_ref = Recdef.ltof_ref
and acc_rel = Recdef.acc_rel
and well_founded = Recdef.well_founded
and delayed_force = Recdef.delayed_force
and h_intros = Recdef.h_intros
and list_rewrite = Recdef.list_rewrite
and evaluable_of_global_reference = Recdef.evaluable_of_global_reference

let prove_with_tcc tcc_lemma_constr eqs : tactic =
  match !tcc_lemma_constr with
    | None -> anomaly "No tcc proof !!"
    | Some lemma ->
	fun gls ->
	  let hid = next_global_ident_away true h_id (pf_ids_of_hyps gls) in
	  tclTHENSEQ
	    [
	      generalize [lemma];
	      h_intro hid;
	      Elim.h_decompose_and (mkVar hid);
	      tclTRY(list_rewrite true eqs);
	      Eauto.gen_eauto false (false,5) [] (Some [])
	    ]
	    gls


let backtrack_eqs_until_hrec hrec eqs : tactic = 
  fun gls -> 
    let rewrite = 
      tclFIRST (List.map Equality.rewriteRL eqs )
    in 
    let _,hrec_concl  = decompose_prod (pf_type_of gls (mkVar hrec)) in 
    let f_app = array_last (snd (destApp hrec_concl)) in 
    let f =  (fst (destApp f_app)) in 
    let rec backtrack : tactic = 
      fun g -> 
	let f_app = array_last (snd (destApp (pf_concl g))) in 
	match kind_of_term f_app with 
	  | App(f',_) when eq_constr f' f -> tclIDTAC g
	  | _ -> tclTHEN rewrite backtrack g
    in
    backtrack gls

    
    
  

let new_prove_with_tcc is_mes acc_inv hrec tcc_lemma_constr eqs : tactic = 
  match !tcc_lemma_constr with 
    | None -> tclIDTAC_MESSAGE (str "No tcc proof !!")
    | Some lemma -> 
	fun gls ->
	  let hid = next_global_ident_away true Recdef.h_id (pf_ids_of_hyps gls) in 
	    (tclTHENSEQ 
	    [
	      generalize [lemma];
	      h_intro hid;
	      Elim.h_decompose_and (mkVar hid); 
	      backtrack_eqs_until_hrec hrec eqs;
	      tclCOMPLETE (tclTHENS  (* We must have exactly ONE subgoal !*)
		(apply (mkVar hrec))
		[ tclTHENSEQ 
		    [
			 thin [hrec];
			 apply (Lazy.force acc_inv);
			 (fun g -> 
			    if is_mes 
			    then 
			      unfold_in_concl [([], evaluable_of_global_reference (delayed_force ltof_ref))] g 
			    else tclIDTAC g
			 );
			 tclTRY(Recdef.list_rewrite true eqs);
			 observe_tac "finishing"  (tclCOMPLETE (Eauto.gen_eauto false (false,5) [] (Some [])))
		       ]
		]
			  )
	    ])
	    gls


let is_valid_hypothesis predicates_name =
  let predicates_name = List.fold_right Idset.add predicates_name Idset.empty in
  let is_pte typ =
    if isApp typ
    then
      let pte,_ = destApp typ in
      if isVar pte
      then Idset.mem (destVar pte) predicates_name
      else false
    else false
  in
  let rec is_valid_hypothesis typ =
    is_pte typ ||
      match kind_of_term typ with 
	| Prod(_,pte,typ') -> is_pte pte && is_valid_hypothesis typ'
	| _ -> false 
  in
  is_valid_hypothesis 

let fresh_id avoid na = 
  let id =  
    match na with 
      | Name id -> id 
      | Anonymous -> h_id 
  in 
  next_global_ident_away true id avoid


let prove_principle_for_gen
    (f_ref,functional_ref,eq_ref) tcc_lemma_ref is_mes
    rec_arg_num rec_arg_type relation = 
  fun g -> 
    let type_of_goal = pf_concl g in 
    let goal_ids = pf_ids_of_hyps g in 
    let goal_elim_infos = compute_elim_sig type_of_goal in 
    let params_names,ids = List.fold_left 
      (fun (params_names,avoid) (na,_,_) -> 
	 let new_id = fresh_id avoid na in 
	 (new_id::params_names,new_id::avoid)
      )
      ([],goal_ids)
      goal_elim_infos.params
    in
    let predicates_names,ids = 
      List.fold_left 
	(fun (predicates_names,avoid) (na,_,_) -> 
	   let new_id = fresh_id avoid na in 
	   (new_id::predicates_names,new_id::avoid)
	)
	([],ids)
	goal_elim_infos.predicates
    in
    let branches_names,ids = 
      List.fold_left 
	(fun (branches_names,avoid) (na,_,_) -> 
	   let new_id = fresh_id avoid na in 
	   (new_id::branches_names,new_id::avoid)
	)
	([],ids)
	goal_elim_infos.branches
    in
    let to_intro = params_names@predicates_names@branches_names in 
    let nparams = List.length params_names in 
    let rec_arg_num = rec_arg_num - nparams in 
    let tac_intro_static = h_intros to_intro in 
    let args_info = ref None in 
    let arg_tac g =  (* introducing args *)
      let ids = pf_ids_of_hyps g in 
      let func_body = def_of_const (mkConst functional_ref) in
      (* 	      let _ = Pp.msgnl (Printer.pr_lconstr func_body) in  *)
      let (f_name, _, body1) = destLambda func_body in
      let f_id =
	match f_name with
	  | Name f_id -> next_global_ident_away true f_id ids
	  | Anonymous -> anomaly "anonymous function"
      in
      let n_names_types,_ = decompose_lam body1 in 
      let n_ids,ids = 
	List.fold_left 
	  (fun (n_ids,ids) (n_name,_) -> 
	     match n_name with 
	       | Name id -> 
		   let n_id = next_global_ident_away true id ids in 
		   n_id::n_ids,n_id::ids
	       | _ -> anomaly "anonymous argument"
	  )
	  ([],(f_id::ids))
	  n_names_types
      in
      let rec_arg_id = List.nth n_ids (rec_arg_num - 1 ) in
      let args_ids = snd (list_chop nparams n_ids) in
      args_info := Some (ids,args_ids,rec_arg_id);
      h_intros args_ids g
    in
    let wf_tac = 
      if is_mes 
      then 
	Recdef.tclUSER_if_not_mes 
      else fun _ -> prove_with_tcc tcc_lemma_ref []
    in
    let start_tac g = 
      let ids,args_ids,rec_arg_id = out_some !args_info in
      let nargs = List.length args_ids in 
      let pre_rec_arg = 
	List.rev_map 
	  mkVar 
	  (fst (list_chop (rec_arg_num - 1) args_ids))
      in
      let args_before_rec = pre_rec_arg@(List.map mkVar params_names) in
      let relation = substl args_before_rec relation in 
      let input_type = substl args_before_rec rec_arg_type in 
      let wf_thm = next_global_ident_away true (id_of_string ("wf_R")) ids in 
      let wf_rec_arg = 
	next_global_ident_away true 
	  (id_of_string ("Acc_"^(string_of_id rec_arg_id)))
	  (wf_thm::ids) 
      in 
      let hrec = next_global_ident_away true hrec_id (wf_rec_arg::wf_thm::ids) in 
      let acc_inv = 
	lazy (
	  mkApp (
	    delayed_force acc_inv_id,
	    [|input_type;relation;mkVar rec_arg_id|]
	  )
	)
      in
      (tclTHENS
	   (observe_tac 
	      "first assert" 
	      (assert_tac 
		 true (* the assert thm is in first subgoal *)
		 (Name wf_rec_arg) 
		 (mkApp (delayed_force acc_rel,
			 [|input_type;relation;mkVar rec_arg_id|])
		 )
	      )
	   )
	   [
	     (* accesibility proof *) 
	     tclTHENS 
	       (observe_tac 
		  "second assert" 
		  (assert_tac 
		     true 
		     (Name wf_thm)
		     (mkApp (delayed_force well_founded,[|input_type;relation|]))
		  )
	       )
	       [ 
		 (* interactive proof of the well_foundness of the relation *) 
		 wf_tac is_mes;
		 (* well_foundness -> Acc for any element *)
		 observe_tac 
		   "apply wf_thm" 
		   (h_apply ((mkApp(mkVar wf_thm,
				    [|mkVar rec_arg_id |])),Rawterm.NoBindings)
		   )
	       ]
	     ;
	     (* rest of the proof *)
	     tclTHENSEQ
	       [
		 observe_tac "generalize" (fun g -> 
		    let to_thin = 
		      fst (list_chop ( nargs + 1) (pf_ids_of_hyps g))
		    in
		    let to_thin_c = List.rev_map mkVar to_thin in 
		    tclTHEN (generalize to_thin_c) (observe_tac "thin" (h_clear false to_thin)) g
		 );
		 observe_tac "h_fix" (h_fix (Some hrec) (nargs+1));
		h_intros args_ids;
		h_intro wf_rec_arg;
		Equality.rewriteLR (mkConst eq_ref);
		(fun g' -> 
		   let body = 
		     let _,args = destApp (pf_concl g') in 
		     array_last args
		   in
		   let body_info rec_hyps = 
		     {
		       nb_rec_hyps = List.length rec_hyps;
		       rec_hyps = rec_hyps;
		       eq_hyps = [];
		       info = body
		     }
		   in 
		   let acc_inv = lazy (mkApp(Lazy.force acc_inv, [|mkVar  wf_rec_arg|]) )  in
		   let pte_info = 
		     { proving_tac =
			 (fun eqs -> 
			    observe_tac "prove_with_tcc" 
			      (new_prove_with_tcc is_mes acc_inv hrec  tcc_lemma_ref (List.map mkVar eqs))
			 );
		       is_valid = is_valid_hypothesis predicates_names 
		     }
		   in
		   let ptes_info : pte_info Idmap.t = 
		     List.fold_left
		       (fun map pte_id -> 
			  Idmap.add pte_id 
			    pte_info			       
			    map
		       )
		       Idmap.empty
		       predicates_names
		   in
		   let make_proof rec_hyps = 
		     build_proof 
		       false 
		       [f_ref]
		       ptes_info
		       (body_info rec_hyps)
		   in
		   instanciate_hyps_with_args 
		     make_proof
		     branches_names
		     args_ids
		     g'
		     
		) 
	       ]
	   ]
	   g
      )
      in
      tclTHENSEQ 
	[tac_intro_static;
	 arg_tac;
	 start_tac
	] g















