open Printer
open CErrors
open Util
open Constr
open EConstr
open Vars
open Namegen
open Names
open Pp
open Tacmach
open Termops
open Tacticals
open Tactics
open Indfun_common
open Libnames
open Globnames
open Context.Rel.Declaration

module RelDecl = Context.Rel.Declaration

(* let msgnl = Pp.msgnl *)

(*
let observe strm =
  if do_observe ()
  then Pp.msg_debug strm
  else ()

let do_observe_tac s tac g =
 try let v = tac g in (* msgnl (goal ++ fnl () ++ (str s)++(str " ")++(str "finished")); *) v
 with e ->
   let e = ExplainErr.process_vernac_interp_error e in
   let goal = begin try (Printer.pr_goal g) with _ -> assert false end in
   msg_debug (str "observation "++ s++str " raised exception " ++
	    Errors.print e ++ str " on goal " ++ goal );
   raise e;;

let observe_tac_stream s tac g =
  if do_observe ()
  then do_observe_tac  s tac g
  else tac g

let observe_tac s tac g = observe_tac_stream (str s) tac g
  *)


let pr_leconstr_fp =
  let sigma, env = Pfedit.get_current_context () in
  Printer.pr_leconstr_env env sigma

let debug_queue = Stack.create ()

let rec print_debug_queue e = 
  if  not (Stack.is_empty debug_queue) 
  then
    begin
      let lmsg,goal = Stack.pop debug_queue in 
      let _ =
	match e with
	| Some e ->
	   Feedback.msg_debug (hov 0 (lmsg ++ (str " raised exception " ++ CErrors.print e) ++ str " on goal" ++ fnl() ++ goal))
	| None ->
	   begin
	     Feedback.msg_debug (str " from " ++ lmsg ++ str " on goal" ++ fnl() ++ goal);
	   end in
      print_debug_queue None ;
    end

let observe strm =
  if do_observe ()
  then Feedback.msg_debug strm
  else ()

let do_observe_tac s tac g = 
  let goal = Printer.pr_goal g in
  let lmsg = (str "observation : ") ++ s in 
  Stack.push (lmsg,goal) debug_queue;
  try 
    let v = tac g in
    ignore(Stack.pop debug_queue);
    v
  with reraise ->
    let reraise = CErrors.push reraise in
    if not (Stack.is_empty debug_queue)
    then print_debug_queue (Some (fst (ExplainErr.process_vernac_interp_error reraise)));
    iraise reraise

let observe_tac_stream s tac g =
  if do_observe ()
  then do_observe_tac s tac g
  else tac g

let observe_tac s = observe_tac_stream (str s)
  

let list_chop ?(msg="") n l =
  try
    List.chop n l
  with Failure (msg') ->
    failwith (msg ^ msg')

let pop t = Vars.lift (-1) t

let make_refl_eq constructor type_of_t t  =
(*   let refl_equal_term = Lazy.force refl_equal in *)
  mkApp(constructor,[|type_of_t;t|])


type pte_info =
    {
      proving_tac : (Id.t list -> Tacmach.tactic);
      is_valid : constr -> bool
    }

type ptes_info = pte_info Id.Map.t

type 'a dynamic_info =
    {
      nb_rec_hyps : int;
      rec_hyps : Id.t list ;
      eq_hyps : Id.t list;
      info : 'a
    }

type body_info = constr dynamic_info


let finish_proof dynamic_infos g =
  observe_tac "finish"
    (Proofview.V82.of_tactic assumption)
    g


let refine c = Refiner.refiner ~check:true EConstr.Unsafe.(to_constr c)

let thin l = Proofview.V82.of_tactic (Tactics.clear l)

let eq_constr sigma u v = EConstr.eq_constr_nounivs sigma u v

let is_trivial_eq sigma t =
  let res =   try
    begin
      match EConstr.kind sigma t with
	| App(f,[|_;t1;t2|]) when eq_constr sigma f (Lazy.force eq) ->
	    eq_constr sigma t1 t2
	| App(f,[|t1;a1;t2;a2|]) when eq_constr sigma f (jmeq ())  ->
	    eq_constr sigma t1 t2 && eq_constr sigma a1 a2
	| _ -> false
    end
  with e when CErrors.noncritical e -> false
  in
(*   observe (str "is_trivial_eq " ++ Printer.pr_lconstr t ++ (if res then str " true" else str " false")); *)
  res

let rec incompatible_constructor_terms sigma t1 t2 =
  let c1,arg1 = decompose_app sigma t1
  and c2,arg2 = decompose_app sigma t2
  in
  (not (eq_constr sigma t1 t2)) &&
    isConstruct sigma c1 && isConstruct sigma c2 &&
    (
      not (eq_constr sigma c1 c2) ||
	List.exists2 (incompatible_constructor_terms sigma) arg1 arg2
    )

let is_incompatible_eq sigma t =
  let res =
    try
      match EConstr.kind sigma t with
	| App(f,[|_;t1;t2|]) when eq_constr sigma f (Lazy.force eq) ->
	    incompatible_constructor_terms sigma t1 t2
	| App(f,[|u1;t1;u2;t2|]) when eq_constr sigma f (jmeq ()) ->
	    (eq_constr sigma u1 u2 &&
	       incompatible_constructor_terms sigma t1 t2)
	| _ -> false
    with e when CErrors.noncritical e -> false
  in
  if res then   observe (str "is_incompatible_eq " ++ pr_leconstr_fp t);
  res

let change_hyp_with_using msg hyp_id t tac : tactic =
  fun g ->
    let prov_id = pf_get_new_id hyp_id g in
    tclTHENS
      ((* observe_tac msg *) Proofview.V82.of_tactic (assert_by (Name prov_id) t (Proofview.V82.tactic (tclCOMPLETE tac))))
      [tclTHENLIST
      [
	(* observe_tac "change_hyp_with_using thin" *) (thin [hyp_id]);
	(* observe_tac "change_hyp_with_using rename " *) (Proofview.V82.of_tactic (rename_hyp [prov_id,hyp_id]))
      ]] g

exception TOREMOVE


let prove_trivial_eq h_id context (constructor,type_of_term,term) =
  let nb_intros = List.length context in
  tclTHENLIST
    [
      tclDO nb_intros (Proofview.V82.of_tactic intro); (* introducing context *)
      (fun g ->
	 let context_hyps =
	   fst (list_chop ~msg:"prove_trivial_eq : " nb_intros (pf_ids_of_hyps g))
	 in
	 let context_hyps' =
	   (mkApp(constructor,[|type_of_term;term|]))::
	     (List.map mkVar context_hyps)
	 in
	 let to_refine = applist(mkVar h_id,List.rev context_hyps') in
	 refine to_refine g
      )
    ]



let find_rectype env sigma c =
  let (t, l) = decompose_app sigma (Reductionops.whd_betaiotazeta sigma c) in
  match EConstr.kind sigma t with
  | Ind ind -> (t, l)
  | Construct _ -> (t,l)
  | _ -> raise Not_found


let isAppConstruct ?(env=Global.env ()) sigma t =
  try
    let t',l = find_rectype env sigma t in
    observe (str "isAppConstruct : " ++ Printer.pr_leconstr_env env sigma t ++ str " -> " ++
             Printer.pr_leconstr_env env sigma (applist  (t',l)));
    true
  with Not_found -> false

exception NoChange

let change_eq env sigma hyp_id (context:rel_context) x t end_of_type  =
  let nochange ?t' msg  =
    begin
      observe (str ("Not treating ( "^msg^" )") ++ pr_leconstr_env env sigma t  ++ str "    " ++
               match t' with None -> str "" | Some t -> Printer.pr_leconstr_env env sigma t );
      raise NoChange;
    end
  in
  let eq_constr c1 c2 = Option.has_some (Evarconv.conv env sigma c1 c2) in
  if not (noccurn sigma 1 end_of_type)
  then nochange "dependent"; (* if end_of_type depends on this term we don't touch it  *)
    if not (isApp sigma t) then nochange "not an equality";
    let f_eq,args = destApp sigma t in
    let constructor,t1,t2,t1_typ =
      try
	if (eq_constr f_eq (Lazy.force eq))
	then
	  let t1 = (args.(1),args.(0))
	  and t2 = (args.(2),args.(0))
	  and t1_typ = args.(0)
	  in
	  (Lazy.force refl_equal,t1,t2,t1_typ)
	else
	  if (eq_constr f_eq (jmeq ()))
	  then
	    (jmeq_refl (),(args.(1),args.(0)),(args.(3),args.(2)),args.(0))
	  else nochange "not an equality"
      with e when CErrors.noncritical e -> nochange "not an equality"
    in
    if not ((closed0 sigma (fst t1)) && (closed0 sigma (snd t1)))then nochange "not a closed lhs";
    let rec compute_substitution sub t1 t2 =
(*       observe (str "compute_substitution : " ++ pr_lconstr t1 ++ str " === " ++ pr_lconstr t2); *)
      if isRel sigma t2
      then
	let t2 = destRel sigma t2  in
	begin
	  try
	    let t1' = Int.Map.find t2 sub in
	    if not (eq_constr t1 t1') then nochange "twice bound variable";
	    sub
	  with Not_found ->
	    assert (closed0 sigma t1);
	    Int.Map.add t2 t1 sub
	end
      else if isAppConstruct sigma t1 && isAppConstruct sigma t2
      then
	begin
	  let c1,args1 =  find_rectype env sigma t1
	  and c2,args2 = find_rectype env sigma t2
	  in
	  if not (eq_constr c1 c2) then nochange "cannot solve (diff)";
	  List.fold_left2 compute_substitution sub args1 args2
	end
      else
	if (eq_constr t1 t2) then sub else nochange ~t':(make_refl_eq constructor (Reductionops.whd_all env sigma t1) t2)  "cannot solve (diff)"
    in
    let sub = compute_substitution Int.Map.empty (snd t1) (snd t2) in
    let sub = compute_substitution sub (fst t1) (fst t2) in
    let end_of_type_with_pop = pop end_of_type in (*the equation will be removed *)
    let new_end_of_type =
      (* Ugly hack to prevent Map.fold order change between ocaml-3.08.3 and ocaml-3.08.4
	 Can be safely replaced by the next comment for Ocaml >= 3.08.4
      *)
      let sub = Int.Map.bindings sub in
      List.fold_left (fun end_of_type (i,t)  -> liftn 1 i (substnl  [t] (i-1) end_of_type))
	end_of_type_with_pop
	sub
    in
    let old_context_length = List.length context + 1 in
    let witness_fun =
      mkLetIn(Anonymous,make_refl_eq constructor t1_typ (fst t1),t,
	       mkApp(mkVar hyp_id,Array.init old_context_length (fun i -> mkRel (old_context_length - i)))
	      )
    in
    let new_type_of_hyp,ctxt_size,witness_fun =
      List.fold_left_i
	(fun i (end_of_type,ctxt_size,witness_fun) decl ->
	   try
	     let witness = Int.Map.find i sub in
	     if is_local_def decl then anomaly (Pp.str "can not redefine a rel!");
	     (pop end_of_type,ctxt_size,mkLetIn (RelDecl.get_name decl, witness, RelDecl.get_type decl, witness_fun))
	   with Not_found  ->
	     (mkProd_or_LetIn decl end_of_type, ctxt_size + 1, mkLambda_or_LetIn decl witness_fun)
	)
	1
	(new_end_of_type,0,witness_fun)
	context
    in
    let new_type_of_hyp =
      Reductionops.nf_betaiota env sigma new_type_of_hyp in
    let new_ctxt,new_end_of_type =
      decompose_prod_n_assum sigma ctxt_size new_type_of_hyp
    in
    let prove_new_hyp : tactic =
      tclTHEN
	(tclDO ctxt_size (Proofview.V82.of_tactic intro))
	(fun g ->
	   let all_ids = pf_ids_of_hyps g in
	   let new_ids,_  = list_chop ctxt_size all_ids in
	   let to_refine = applist(witness_fun,List.rev_map mkVar new_ids) in
	   let evm, _ = pf_apply Typing.type_of g to_refine in
	     tclTHEN (Refiner.tclEVARS evm) (refine to_refine) g
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


let is_property sigma (ptes_info:ptes_info) t_x full_type_of_hyp =
  if isApp sigma t_x
  then
    let pte,args = destApp sigma t_x in
    if isVar sigma pte && Array.for_all (closed0 sigma) args
    then
      try
	let info = Id.Map.find (destVar sigma pte) ptes_info in
	info.is_valid full_type_of_hyp
      with Not_found -> false
    else false
  else false

let isLetIn sigma t =
  match EConstr.kind sigma t with
    | LetIn _ -> true
    | _ -> false


let h_reduce_with_zeta cl =
  Proofview.V82.of_tactic (reduce
    (Genredexpr.Cbv
       {Redops.all_flags
	with Genredexpr.rDelta = false;
       }) cl)



let rewrite_until_var arg_num eq_ids : tactic =
  (* tests if the declares recursive argument is neither a Constructor nor
     an applied Constructor since such a form for the recursive argument
     will break the Guard when trying to save the Lemma.
  *)
  let test_var g =
    let sigma = project g in
    let _,args = destApp sigma (pf_concl g) in
    not ((isConstruct sigma args.(arg_num)) || isAppConstruct sigma args.(arg_num))
  in
  let rec do_rewrite eq_ids g  =
    if test_var g
    then tclIDTAC g
    else
      match eq_ids with
	| [] -> anomaly (Pp.str "Cannot find a way to prove recursive property.");
	| eq_id::eq_ids ->
	    tclTHEN
	      (tclTRY (Proofview.V82.of_tactic (Equality.rewriteRL (mkVar eq_id))))
	      (do_rewrite eq_ids)
	      g
  in
  do_rewrite eq_ids


let rec_pte_id = Id.of_string "Hrec"
let clean_hyp_with_heq ptes_infos eq_hyps hyp_id env sigma =
  let coq_False = EConstr.of_constr (UnivGen.constr_of_monomorphic_global @@ Coqlib.lib_ref "core.False.type") in
  let coq_True = EConstr.of_constr (UnivGen.constr_of_monomorphic_global @@ Coqlib.lib_ref "core.True.type") in
  let coq_I = EConstr.of_constr (UnivGen.constr_of_monomorphic_global @@ Coqlib.lib_ref "core.True.I") in
  let rec scan_type  context type_of_hyp : tactic =
    if isLetIn sigma type_of_hyp then
      let real_type_of_hyp = it_mkProd_or_LetIn type_of_hyp context in
      let reduced_type_of_hyp = Reductionops.nf_betaiotazeta env sigma real_type_of_hyp in
      (* length of context didn't change ? *)
      let new_context,new_typ_of_hyp =
	 decompose_prod_n_assum sigma (List.length context) reduced_type_of_hyp
      in
        tclTHENLIST
	[ h_reduce_with_zeta (Locusops.onHyp hyp_id);
	  scan_type new_context new_typ_of_hyp ]
    else if isProd sigma type_of_hyp
    then
      begin
	let (x,t_x,t') = destProd sigma type_of_hyp in
	let actual_real_type_of_hyp = it_mkProd_or_LetIn t' context in
	if is_property sigma ptes_infos t_x actual_real_type_of_hyp then
	  begin
	    let pte,pte_args =  (destApp sigma t_x) in
	    let (* fix_info *) prove_rec_hyp = (Id.Map.find (destVar sigma pte) ptes_infos).proving_tac in
	    let popped_t' = pop t' in
	    let real_type_of_hyp = it_mkProd_or_LetIn popped_t' context in
	    let prove_new_type_of_hyp =
	      let context_length = List.length context in
	      tclTHENLIST
		[
		  tclDO context_length (Proofview.V82.of_tactic intro);
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
(* 		     observe_tac "rec hyp " *)
		       (tclTHENS
		       (Proofview.V82.of_tactic (assert_before (Name rec_pte_id) t_x))
		       [
			 (* observe_tac "prove rec hyp" *) (prove_rec_hyp eq_hyps);
(* 			observe_tac "prove rec hyp" *)
			  (refine to_refine)
		       ])
		       g
		  )
		]
	    in
	    tclTHENLIST
	      [
(* 		observe_tac "hyp rec"  *)
		  (change_hyp_with_using "rec_hyp_tac" hyp_id real_type_of_hyp prove_new_type_of_hyp);
		scan_type context popped_t'
	      ]
	  end
	else if eq_constr sigma t_x coq_False then
	  begin
(* 	    observe (str "Removing : "++ Ppconstr.pr_id hyp_id++  *)
(* 		       str " since it has False in its preconds " *)
(* 		    ); *)
	    raise TOREMOVE;  (* False -> .. useless *)
	  end
	else if is_incompatible_eq sigma t_x then raise TOREMOVE (* t_x := C1 ... =  C2 ... *)
	else if eq_constr sigma t_x coq_True  (* Trivial => we remove this precons *)
	then
(* 	    observe (str "In "++Ppconstr.pr_id hyp_id++  *)
(* 		       str " removing useless precond True" *)
(* 		    );  *)
	  let popped_t' = pop t' in
	  let real_type_of_hyp =
	    it_mkProd_or_LetIn popped_t' context
	  in
	  let prove_trivial =
	    let nb_intro = List.length context in
	    tclTHENLIST [
	      tclDO nb_intro (Proofview.V82.of_tactic intro);
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
	      ((* observe_tac "prove_trivial" *) prove_trivial);
	    scan_type context popped_t'
	  ]
	else if is_trivial_eq sigma t_x
	then (*  t_x :=  t = t   => we remove this precond *)
	  let popped_t' = pop t' in
	  let real_type_of_hyp =
	    it_mkProd_or_LetIn popped_t' context
	  in
	  let hd,args = destApp sigma t_x in
	  let get_args hd args =
	    if eq_constr sigma hd (Lazy.force eq)
	    then (Lazy.force refl_equal,args.(0),args.(1))
	    else (jmeq_refl (),args.(0),args.(1))
	  in
	  tclTHENLIST
	    [
	      change_hyp_with_using
		"prove_trivial_eq"
		hyp_id
		real_type_of_hyp
		((* observe_tac "prove_trivial_eq" *)
		  (prove_trivial_eq hyp_id context (get_args hd args)));
	      scan_type context popped_t'
	    ]
	else
	  begin
	    try
	      let new_context,new_t',tac = change_eq env sigma hyp_id context x t_x t' in
	      tclTHEN
		tac
		(scan_type new_context new_t')
	    with NoChange ->
	      (* Last thing todo : push the rel in the context and continue *)
	      scan_type (LocalAssum (x,t_x) :: context) t'
	  end
      end
    else
      tclIDTAC
  in
  try
    scan_type [] (Typing.unsafe_type_of env sigma (mkVar hyp_id)), [hyp_id]
  with TOREMOVE ->
    thin [hyp_id],[]


let clean_goal_with_heq ptes_infos continue_tac (dyn_infos:body_info) =
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
	(* observe_tac "clean_hyp_with_heq continue" *) (continue_tac new_infos)
      ]
      g

let heq_id = Id.of_string "Heq"

let treat_new_case ptes_infos nb_prod continue_tac term dyn_infos =
  fun g ->
    let nb_first_intro = nb_prod - 1 - dyn_infos.nb_rec_hyps in
    tclTHENLIST
      [
	(* We first introduce the variables *)
	tclDO nb_first_intro (Proofview.V82.of_tactic (intro_avoiding (Id.Set.of_list dyn_infos.rec_hyps)));
	(* Then the equation itself *)
	Proofview.V82.of_tactic (intro_using heq_id);
	onLastHypId (fun heq_id -> tclTHENLIST [
	(* Then the new hypothesis *)
        tclMAP (fun id -> Proofview.V82.of_tactic (introduction id)) dyn_infos.rec_hyps;
	observe_tac "after_introduction" (fun g' ->
	   (* We get infos on the equations introduced*)
	   let new_term_value_eq = pf_unsafe_type_of g' (mkVar heq_id) in
	   (* compute the new value of the body *)
	   let new_term_value =
	     match EConstr.kind (project g') new_term_value_eq with
	       | App(f,[| _;_;args2 |]) -> args2
	       | _ ->
		   observe (str "cannot compute new term value : " ++ pr_gls g' ++ fnl () ++ str "last hyp is" ++
			      pr_leconstr_env (pf_env g') (project g') new_term_value_eq
			   );
		   anomaly (Pp.str "cannot compute new term value.")
	   in
	 let fun_body =
	   mkLambda(Anonymous,
		    pf_unsafe_type_of g' term,
		    Termops.replace_term (project g') term (mkRel 1) dyn_infos.info
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
      )]) 
    ]
      g


let my_orelse tac1 tac2 g =
  try
    tac1 g
  with e when CErrors.noncritical e ->
(*     observe (str "using snd tac since : " ++ CErrors.print e); *)
    tac2 g

let instantiate_hyps_with_args (do_prove:Id.t list -> tactic) hyps args_id =
  let args = Array.of_list (List.map mkVar  args_id) in
  let instantiate_one_hyp hid =
    my_orelse
      ( (* we instantiate the hyp if possible  *)
	fun g ->
	  let prov_hid = pf_get_new_id hid g in
	  let c = mkApp(mkVar hid,args) in
	  let evm, _ = pf_apply Typing.type_of g c in
	  tclTHENLIST[
            Refiner.tclEVARS evm;
	    Proofview.V82.of_tactic (pose_proof (Name prov_hid) c);
	    thin [hid];
	    Proofview.V82.of_tactic (rename_hyp [prov_hid,hid])
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
  if List.is_empty args_id
  then
    tclTHENLIST [
      tclMAP (fun hyp_id -> h_reduce_with_zeta (Locusops.onHyp hyp_id)) hyps;
      do_prove hyps
    ]
  else
    tclTHENLIST
      [
	tclMAP (fun hyp_id -> h_reduce_with_zeta (Locusops.onHyp hyp_id)) hyps;
        tclMAP instantiate_one_hyp hyps;
	(fun g ->
	   let all_g_hyps_id =
	     List.fold_right Id.Set.add (pf_ids_of_hyps g) Id.Set.empty
	   in
	   let remaining_hyps =
	     List.filter (fun id -> Id.Set.mem id all_g_hyps_id) hyps
	   in
	   do_prove remaining_hyps g
	  )
      ]

let build_proof
    (interactive_proof:bool)
    (fnames:Constant.t list)
    ptes_infos
    dyn_infos
    : tactic =
  let rec build_proof_aux do_finalize dyn_infos : tactic =
    fun g ->
        let env = pf_env g in
        let sigma = project g in
(*      observe (str "proving on " ++ Printer.pr_lconstr_env (pf_env g) term);*)
	match EConstr.kind sigma dyn_infos.info with
	  | Case(ci,ct,t,cb) ->
	      let do_finalize_t dyn_info' =
		fun g ->
		  let t = dyn_info'.info in
		  let dyn_infos = {dyn_info' with info =
		      mkCase(ci,ct,t,cb)} in
		  let g_nb_prod = nb_prod (project g) (pf_concl g) in
		  let type_of_term = pf_unsafe_type_of g t in
		  let term_eq =
		    make_refl_eq (Lazy.force refl_equal) type_of_term t
		  in
		  tclTHENLIST
		    [
		      Proofview.V82.of_tactic (generalize (term_eq::(List.map mkVar dyn_infos.rec_hyps)));
		      thin dyn_infos.rec_hyps;
		      Proofview.V82.of_tactic (pattern_option [Locus.AllOccurrencesBut [1],t] None);
		      (fun g -> observe_tac "toto" (
			 tclTHENLIST [Proofview.V82.of_tactic (Simple.case t);
				     (fun g' ->
					let g'_nb_prod = nb_prod (project g') (pf_concl g') in
                                        let nb_instantiate_partial = g'_nb_prod - g_nb_prod in
			 		observe_tac "treat_new_case"
					  (treat_new_case
					     ptes_infos
                                             nb_instantiate_partial
					     (build_proof do_finalize)
					     t
					     dyn_infos)
					  g'
				     )

				    ]) g
		      )
		    ]
		    g
	      in
	      build_proof do_finalize_t {dyn_infos with info = t} g
	  | Lambda(n,t,b) ->
	      begin
		match EConstr.kind sigma (pf_concl g) with
		  | Prod _ ->
		      tclTHEN
			(Proofview.V82.of_tactic intro)
			(fun g' ->
                           let open Context.Named.Declaration in
			   let id = pf_last_hyp g' |> get_id in
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
(* 			   observe_tac "Lambda" *) (instantiate_hyps_with_args do_prove new_infos.rec_hyps [id]) g'
			     (* 			   build_proof do_finalize new_infos g' *)
			) g
		  | _ ->
		      do_finalize dyn_infos g
	      end
	  | Cast(t,_,_) ->
	      build_proof do_finalize {dyn_infos with info = t} g
          | Const _ | Var _ | Meta _ | Evar _ | Sort _ | Construct _ | Ind _ | Int _ ->
	      do_finalize dyn_infos g
	  | App(_,_) ->
	      let f,args = decompose_app sigma dyn_infos.info in
	      begin
		match EConstr.kind sigma f with
      | Int _ -> user_err Pp.(str "integer cannot be applied")
		  | App _ -> assert false (* we have collected all the app in decompose_app *)
		  | Proj _ -> assert false (*FIXME*)
		  | Var _ | Construct _ | Rel _ | Evar _ | Meta _  | Ind _ | Sort _ | Prod _ ->
		      let new_infos =
			{ dyn_infos with
			    info = (f,args)
			}
		      in
		      build_proof_args do_finalize new_infos  g
		  | Const (c,_) when not (List.mem_f Constant.equal c fnames) ->
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
		      let new_term =
                        Reductionops.nf_beta env sigma dyn_infos.info in
		      build_proof do_finalize {dyn_infos with info = new_term}
			g
		  | LetIn _ ->
		      let new_infos =
                        { dyn_infos with info = Reductionops.nf_betaiotazeta env sigma dyn_infos.info }
		      in

		      tclTHENLIST
			[tclMAP
			   (fun hyp_id ->
			     h_reduce_with_zeta (Locusops.onHyp hyp_id))
			   dyn_infos.rec_hyps;
			 h_reduce_with_zeta Locusops.onConcl;
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
	      user_err Pp.(str ( "Anonymous local (co)fixpoints are not handled yet"))


	  | Proj _ -> user_err Pp.(str "Prod")
	  | Prod _ -> do_finalize dyn_infos g
	  | LetIn _ ->
	      let new_infos =
		{ dyn_infos with
                    info = Reductionops.nf_betaiotazeta env sigma dyn_infos.info
		}
	      in

	      tclTHENLIST
		[tclMAP
		   (fun hyp_id -> h_reduce_with_zeta (Locusops.onHyp hyp_id))
		   dyn_infos.rec_hyps;
		 h_reduce_with_zeta Locusops.onConcl;
		 build_proof do_finalize new_infos
		] g
	  | Rel _ -> anomaly (Pp.str "Free var in goal conclusion!")
  and build_proof do_finalize dyn_infos g =
(*     observe (str "proving with "++Printer.pr_lconstr dyn_infos.info++ str " on goal " ++ pr_gls g); *)
    observe_tac_stream (str "build_proof with " ++ pr_leconstr_fp dyn_infos.info ) (build_proof_aux do_finalize dyn_infos) g
  and build_proof_args do_finalize dyn_infos (* f_args'  args *) :tactic =
    fun g ->
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
      (* observe_tac "build_proof_args" *) (tac ) g
  in
  let do_finish_proof dyn_infos =
     (* tclTRYD *) (clean_goal_with_heq
		      ptes_infos
		      finish_proof dyn_infos)
  in
    (* observe_tac "build_proof" *)
  (build_proof (clean_goal_with_heq ptes_infos do_finish_proof) dyn_infos)












(* Proof of principles from structural functions *)

type static_fix_info =
    {
      idx : int;
      name : Id.t;
      types : types;
      offset : int;
      nb_realargs : int;
      body_with_param : constr;
      num_in_block : int
    }



let prove_rec_hyp_for_struct fix_info =
      (fun  eq_hyps -> tclTHEN
	(rewrite_until_var (fix_info.idx) eq_hyps)
	(fun g ->
	   let _,pte_args = destApp (project g) (pf_concl g) in
	   let rec_hyp_proof =
	     mkApp(mkVar fix_info.name,array_get_start pte_args)
	   in
	   refine rec_hyp_proof g
	))

let prove_rec_hyp fix_info  =
  { proving_tac = prove_rec_hyp_for_struct fix_info
  ;
    is_valid = fun _ -> true
  }

let generalize_non_dep hyp g =
(*   observe (str "rec id := " ++ Ppconstr.pr_id hyp); *)
  let hyps = [hyp] in
  let env = Global.env () in
  let hyp_typ = pf_unsafe_type_of g (mkVar hyp) in
  let to_revert,_ =
    let open Context.Named.Declaration in
    Environ.fold_named_context_reverse (fun (clear,keep) decl ->
      let decl = map_named_decl EConstr.of_constr decl in
      let hyp = get_id decl in
      if Id.List.mem hyp hyps
        || List.exists (Termops.occur_var_in_decl env (project g) hyp) keep
	|| Termops.occur_var env (project g) hyp hyp_typ
	|| Termops.is_section_variable hyp (* should be dangerous *)
      then (clear,decl::keep)
      else (hyp::clear,keep))
      ~init:([],[]) (pf_env g)
  in
(*   observe (str "to_revert := " ++ prlist_with_sep spc Ppconstr.pr_id to_revert); *)
  tclTHEN
    ((* observe_tac "h_generalize" *) (Proofview.V82.of_tactic (generalize  (List.map mkVar to_revert) )))
    ((* observe_tac "thin" *) (thin to_revert))
    g

let id_of_decl = RelDecl.get_name %> Nameops.Name.get_id
let var_of_decl = id_of_decl %> mkVar
let revert idl =
  tclTHEN
    (Proofview.V82.of_tactic (generalize (List.map mkVar idl)))
    (thin idl)

let generate_equation_lemma evd fnames f fun_num nb_params nb_args rec_args_num =
(*   observe (str "nb_args := " ++ str (string_of_int nb_args)); *)
(*   observe (str "nb_params := " ++ str (string_of_int nb_params)); *)
(*   observe (str "rec_args_num := " ++ str (string_of_int (rec_args_num + 1) )); *)
  let f_def = Global.lookup_constant (fst (destConst evd f)) in
  let eq_lhs = mkApp(f,Array.init (nb_params + nb_args) (fun i -> mkRel(nb_params + nb_args - i))) in
  let (f_body, _) = Option.get (Global.body_of_constant_body f_def) in
  let f_body = EConstr.of_constr f_body in
  let params,f_body_with_params = decompose_lam_n evd nb_params f_body in
  let (_,num),(_,_,bodies) = destFix evd f_body_with_params in
  let fnames_with_params =
    let params = Array.init nb_params (fun i -> mkRel(nb_params - i)) in
    let fnames = List.rev (Array.to_list (Array.map (fun f -> mkApp(f,params)) fnames)) in
    fnames
  in
(*   observe (str "fnames_with_params " ++ prlist_with_sep fnl pr_lconstr fnames_with_params); *)
(*   observe (str "body " ++ pr_lconstr bodies.(num)); *)
  let f_body_with_params_and_other_fun  = substl fnames_with_params bodies.(num) in
(*   observe (str "f_body_with_params_and_other_fun " ++  pr_lconstr f_body_with_params_and_other_fun); *)
  let eq_rhs = Reductionops.nf_betaiotazeta (Global.env ()) evd (mkApp(compose_lam params f_body_with_params_and_other_fun,Array.init (nb_params + nb_args) (fun i -> mkRel(nb_params + nb_args - i)))) in
  (*   observe (str "eq_rhs " ++  pr_lconstr eq_rhs); *)
  let (type_ctxt,type_of_f),evd =
    let evd,t = Typing.type_of ~refresh:true (Global.env ()) evd f
    in 
    decompose_prod_n_assum evd
      (nb_params + nb_args) t,evd
  in
  let eqn = mkApp(Lazy.force eq,[|type_of_f;eq_lhs;eq_rhs|]) in
  let lemma_type = it_mkProd_or_LetIn eqn type_ctxt in
  (* Pp.msgnl (str "lemma type " ++ Printer.pr_lconstr lemma_type ++ fnl () ++ str "f_body " ++ Printer.pr_lconstr f_body); *)
  let f_id = Label.to_id (Constant.label (fst (destConst evd f))) in
  let prove_replacement =
    tclTHENLIST
      [
	tclDO (nb_params + rec_args_num + 1) (Proofview.V82.of_tactic intro);
	observe_tac "" (fun g ->
	   let rec_id = pf_nth_hyp_id g 1 in
	   tclTHENLIST
	     [observe_tac "generalize_non_dep in generate_equation_lemma" (generalize_non_dep rec_id);
	      observe_tac "h_case" (Proofview.V82.of_tactic (simplest_case (mkVar rec_id)));
	      (Proofview.V82.of_tactic intros_reflexivity)] g
	)
      ]
  in
  (* Pp.msgnl (str "lemma type (2) " ++ Printer.pr_lconstr_env (Global.env ()) evd lemma_type); *)
  Lemmas.start_proof
    (*i The next call to mk_equation_id is valid since we are constructing the lemma
      Ensures by: obvious
      i*)
    (mk_equation_id f_id)
    (Decl_kinds.Global, false, (Decl_kinds.Proof Decl_kinds.Theorem))
    evd
  lemma_type;
  ignore (Pfedit.by (Proofview.V82.tactic prove_replacement));
  Lemmas.save_proof (Vernacexpr.(Proved(Proof_global.Transparent,None)));
  evd




let do_replace (evd:Evd.evar_map ref) params rec_arg_num rev_args_id f fun_num all_funs g =
  let equation_lemma =
    try
      let finfos = find_Function_infos (fst (destConst !evd f)) (*FIXME*) in
      mkConst (Option.get finfos.equation_lemma)
    with (Not_found | Option.IsNone as e) ->
      let f_id = Label.to_id (Constant.label (fst (destConst !evd f))) in
      (*i The next call to mk_equation_id is valid since we will construct the lemma
	Ensures by: obvious
	i*)
      let equation_lemma_id = (mk_equation_id f_id) in
      evd := generate_equation_lemma !evd all_funs  f fun_num (List.length params) (List.length rev_args_id) rec_arg_num;
      let _ =
	match e with
	  | Option.IsNone ->
	      let finfos = find_Function_infos (fst (destConst !evd f)) in
	      update_Function
		{finfos with
		   equation_lemma = Some (match Nametab.locate (qualid_of_ident equation_lemma_id) with
					      ConstRef c -> c
					    | _ -> CErrors.anomaly (Pp.str "Not a constant.")
					 )
		}
	  | _ -> ()
      in
      (* let res = Constrintern.construct_reference (pf_hyps g) equation_lemma_id in *)
      let evd',res =
	Evd.fresh_global
	  (Global.env ()) !evd
	  (Constrintern.locate_reference (qualid_of_ident equation_lemma_id))
      in
      evd:=evd';
      let sigma, _ = Typing.type_of ~refresh:true (Global.env ()) !evd res in
      evd := sigma;
      res
  in
  let nb_intro_to_do = nb_prod (project g) (pf_concl g) in
    tclTHEN
      (tclDO nb_intro_to_do (Proofview.V82.of_tactic intro))
      (
	fun g' ->
	  let just_introduced = nLastDecls nb_intro_to_do g' in
          let open Context.Named.Declaration in
	  let just_introduced_id = List.map get_id just_introduced in
	  tclTHEN (Proofview.V82.of_tactic (Equality.rewriteLR equation_lemma))
		  (revert just_introduced_id) g'
      )
      g

let prove_princ_for_struct (evd:Evd.evar_map ref) interactive_proof fun_num fnames all_funs _nparams : tactic =
  fun g ->
  let princ_type = pf_concl g in
  (* Pp.msgnl (str "princ_type " ++ Printer.pr_lconstr princ_type); *)
  (* Pp.msgnl (str "all_funs "); *)
  (* Array.iter (fun c -> Pp.msgnl (Printer.pr_lconstr c)) all_funs; *)
    let princ_info = compute_elim_sig (project g) princ_type in
    let fresh_id =
      let avoid = ref (pf_ids_of_hyps g) in
      (fun na ->
	 let new_id =
	   match na with
	       Name id -> fresh_id !avoid (Id.to_string id)
	     | Anonymous -> fresh_id !avoid "H"
	 in
	 avoid := new_id :: !avoid;
	 (Name new_id)
      )
    in
    let fresh_decl = RelDecl.map_name fresh_id in
    let princ_info : elim_scheme =
      { princ_info with
	  params = List.map fresh_decl princ_info.params;
	  predicates = List.map fresh_decl princ_info.predicates;
	  branches = List.map fresh_decl princ_info.branches;
	  args = List.map fresh_decl princ_info.args
      }
    in
    let get_body const =
      match Global.body_of_constant const with
	| Some (body, _) ->
          let env = Global.env () in
          let sigma = Evd.from_env env in
	     Tacred.cbv_norm_flags
	       (CClosure.RedFlags.mkflags [CClosure.RedFlags.fZETA])
               env
               sigma
	       (EConstr.of_constr body)
	| None -> user_err Pp.(str "Cannot define a principle over an axiom ")
    in
    let fbody = get_body fnames.(fun_num) in
    let f_ctxt,f_body = decompose_lam (project g) fbody in
    let f_ctxt_length = List.length f_ctxt in
    let diff_params = princ_info.nparams - f_ctxt_length in
    let full_params,princ_params,fbody_with_full_params =
      if diff_params > 0
      then
	let princ_params,full_params =
	  list_chop  diff_params princ_info.params
	in
	(full_params, (* real params *)
	 princ_params, (* the params of the principle which are not params of the function *)
         substl (* function instantiated with real params *)
	   (List.map var_of_decl full_params)
	   f_body
	)
      else
	let f_ctxt_other,f_ctxt_params =
	  list_chop (- diff_params) f_ctxt in
	let f_body = compose_lam f_ctxt_other f_body in
	(princ_info.params, (* real params *)
	 [],(* all params are full params *)
         substl (* function instantiated with real params *)
	   (List.map var_of_decl princ_info.params)
	   f_body
	)
    in
    observe (str "full_params := " ++
	       prlist_with_sep spc (RelDecl.get_name %> Nameops.Name.get_id %> Ppconstr.pr_id)
	       full_params
	    );
    observe (str "princ_params := " ++
	       prlist_with_sep spc (RelDecl.get_name %> Nameops.Name.get_id %> Ppconstr.pr_id)
	       princ_params
	    );
    observe (str "fbody_with_full_params := " ++
               pr_leconstr_env (Global.env ()) !evd fbody_with_full_params
	    );
    let all_funs_with_full_params =
      Array.map (fun f -> applist(f, List.rev_map var_of_decl full_params)) all_funs
    in
    let fix_offset = List.length princ_params in
    let ptes_to_fix,infos =
      match EConstr.kind (project g) fbody_with_full_params with
	| Fix((idxs,i),(names,typess,bodies)) ->
	    let bodies_with_all_params =
	      Array.map
		(fun body ->
                   Reductionops.nf_betaiota (pf_env g) (project g)
		     (applist(substl (List.rev (Array.to_list all_funs_with_full_params)) body,
			      List.rev_map var_of_decl princ_params))
		)
		bodies
	    in
	    let info_array =
	      Array.mapi
		(fun i types ->
		   let types = prod_applist (project g) types (List.rev_map var_of_decl princ_params) in
		   { idx = idxs.(i)  - fix_offset;
		     name = Nameops.Name.get_id (fresh_id names.(i));
		     types = types;
		     offset = fix_offset;
		     nb_realargs =
		       List.length
			 (fst (decompose_lam (project g) bodies.(i))) - fix_offset;
		     body_with_param = bodies_with_all_params.(i);
		     num_in_block = i
		   }
		)
		typess
	    in
	    let pte_to_fix,rev_info =
	      List.fold_left_i
		(fun i (acc_map,acc_info) decl ->
		   let pte = RelDecl.get_name decl in
		   let infos = info_array.(i) in
		   let type_args,_ = decompose_prod (project g) infos.types in
		   let nargs = List.length type_args in
		   let f = applist(mkConst fnames.(i), List.rev_map var_of_decl princ_info.params) in
		   let first_args = Array.init nargs (fun i -> mkRel (nargs -i)) in
		   let app_f = mkApp(f,first_args) in
		   let pte_args = (Array.to_list first_args)@[app_f] in
		   let app_pte = applist(mkVar (Nameops.Name.get_id pte),pte_args) in
		   let body_with_param,num =
		     let body = get_body fnames.(i) in
		     let body_with_full_params =
                       Reductionops.nf_betaiota (pf_env g) (project g) (
			 applist(body,List.rev_map var_of_decl full_params))
		     in
		     match EConstr.kind (project g) body_with_full_params with
		       | Fix((_,num),(_,_,bs)) ->
                               Reductionops.nf_betaiota (pf_env g) (project g)
				 (
				   (applist
				      (substl
					 (List.rev
					    (Array.to_list all_funs_with_full_params))
					 bs.(num),
				       List.rev_map var_of_decl princ_params))
				 ),num
			 | _ -> user_err Pp.(str "Not a mutual block")
		   in
		   let info =
		     {infos with
			types = compose_prod type_args app_pte;
			 body_with_param = body_with_param;
			 num_in_block = num
		     }
		   in
(* 		   observe (str "binding " ++ Ppconstr.pr_id (Nameops.Name.get_id pte) ++  *)
(* 			      str " to " ++ Ppconstr.pr_id info.name); *)
		   (Id.Map.add (Nameops.Name.get_id pte) info acc_map,info::acc_info)
		   )
		0
		(Id.Map.empty,[])
		(List.rev princ_info.predicates)
	    in
	    pte_to_fix,List.rev rev_info
	| _ ->
	   Id.Map.empty,[]
    in
    let mk_fixes : tactic =
      let pre_info,infos = list_chop fun_num infos in
      match pre_info,infos with
	| _,[] -> tclIDTAC
	| _, this_fix_info::others_infos ->
	    let other_fix_infos =
	      List.map
		(fun fi -> fi.name,fi.idx + 1 ,fi.types)
		(pre_info@others_infos)
	    in
	    if List.is_empty other_fix_infos
	    then
	      if this_fix_info.idx + 1 = 0
	      then tclIDTAC (* Someone  tries to defined a principle on a fully parametric definition declared as a fixpoint (strange but ....) *)
	      else
                observe_tac_stream (str "h_fix " ++ int (this_fix_info.idx +1) ) (Proofview.V82.of_tactic (fix this_fix_info.name (this_fix_info.idx +1)))
	    else
	      Proofview.V82.of_tactic (Tactics.mutual_fix this_fix_info.name (this_fix_info.idx + 1)
		other_fix_infos 0)
    in
    let first_tac : tactic = (* every operations until fix creations *)
      tclTHENLIST
	[ observe_tac "introducing params" (Proofview.V82.of_tactic (intros_using (List.rev_map id_of_decl princ_info.params)));
	  observe_tac "introducing predictes" (Proofview.V82.of_tactic (intros_using (List.rev_map id_of_decl princ_info.predicates)));
	  observe_tac "introducing branches" (Proofview.V82.of_tactic (intros_using (List.rev_map id_of_decl princ_info.branches)));
	  observe_tac "building fixes" mk_fixes;
	]
    in
    let intros_after_fixes : tactic =
      fun gl ->
	let ctxt,pte_app =  (decompose_prod_assum (project gl) (pf_concl gl)) in
	let pte,pte_args = (decompose_app (project gl) pte_app) in
	try
	  let pte =
            try destVar (project gl) pte
            with DestKO -> anomaly (Pp.str "Property is not a variable.")
          in
	  let fix_info = Id.Map.find  pte ptes_to_fix in
	  let nb_args = fix_info.nb_realargs in
	  tclTHENLIST
	    [
	      (* observe_tac ("introducing args") *) (tclDO nb_args (Proofview.V82.of_tactic intro));
	      (fun g -> (* replacement of the function by its body *)
		 let args = nLastDecls nb_args g in
		 let fix_body = fix_info.body_with_param in
(* 		 observe (str "fix_body := "++ pr_lconstr_env (pf_env gl) fix_body); *)
                 let open Context.Named.Declaration in
		 let args_id = List.map get_id args in
		 let dyn_infos =
		   {
		     nb_rec_hyps = -100;
		     rec_hyps = [];
		     info =
                       Reductionops.nf_betaiota (pf_env g) (project g)
			 (applist(fix_body,List.rev_map mkVar args_id));
		     eq_hyps = []
		   }
		 in
		 tclTHENLIST
		   [
		     observe_tac "do_replace"
		       (do_replace evd
			  full_params
			  (fix_info.idx + List.length princ_params)
			  (args_id@(List.map (RelDecl.get_name %> Nameops.Name.get_id) princ_params))
			  (all_funs.(fix_info.num_in_block))
			  fix_info.num_in_block
			  all_funs
		       );
		     let do_prove =
		       build_proof
			 interactive_proof
			 (Array.to_list fnames)
			 (Id.Map.map prove_rec_hyp ptes_to_fix)
		     in
		     let prove_tac branches  =
		       let dyn_infos =
			 {dyn_infos with
			    rec_hyps = branches;
			    nb_rec_hyps = List.length branches
			 }
		       in
		       observe_tac "cleaning" (clean_goal_with_heq
			 (Id.Map.map prove_rec_hyp ptes_to_fix)
			 do_prove
			 dyn_infos)
		     in
(* 		     observe (str "branches := " ++ *)
(* 				prlist_with_sep spc (fun decl -> Ppconstr.pr_id (id_of_decl decl)) princ_info.branches ++  fnl () ++ *)
(* 			   str "args := " ++ prlist_with_sep spc Ppconstr.pr_id  args_id *)

(* 			   ); *)
                     (* observe_tac "instancing" *) (instantiate_hyps_with_args prove_tac
		       (List.rev_map id_of_decl princ_info.branches)
		       (List.rev args_id))
		   ]
		   g
	      );
	    ] gl
	with Not_found ->
	  let nb_args = min (princ_info.nargs) (List.length ctxt) in
	  tclTHENLIST
	    [
	      tclDO nb_args (Proofview.V82.of_tactic intro);
	      (fun g -> (* replacement of the function by its body *)
	         let args = nLastDecls nb_args g in
                 let open Context.Named.Declaration in
		 let args_id = List.map get_id args in
		 let dyn_infos =
		   {
		     nb_rec_hyps = -100;
		     rec_hyps = [];
		     info =
                       Reductionops.nf_betaiota (pf_env g) (project g)
			 (applist(fbody_with_full_params,
				  (List.rev_map var_of_decl princ_params)@
				    (List.rev_map mkVar args_id)
				 ));
		     eq_hyps = []
		   }
		 in
		 let fname = destConst (project g) (fst (decompose_app (project g) (List.hd (List.rev pte_args)))) in
		 tclTHENLIST
		   [Proofview.V82.of_tactic (unfold_in_concl [(Locus.AllOccurrences, Names.EvalConstRef (fst fname))]);
		    let do_prove =
		      build_proof
			interactive_proof
			(Array.to_list fnames)
			 (Id.Map.map prove_rec_hyp ptes_to_fix)
		    in
		    let prove_tac branches  =
		      let dyn_infos =
			 {dyn_infos with
			    rec_hyps = branches;
			    nb_rec_hyps = List.length branches
			 }
		      in
		       clean_goal_with_heq
			 (Id.Map.map prove_rec_hyp ptes_to_fix)
			 do_prove
			 dyn_infos
		    in
                    instantiate_hyps_with_args prove_tac
		       (List.rev_map id_of_decl princ_info.branches)
		      (List.rev args_id)
		   ]
		   g
	      )
	    ]
	  gl
    in
    tclTHEN
      first_tac
      intros_after_fixes
      g






(* Proof of principles of general functions *)
(* let  hrec_id = Recdef.hrec_id *)
(* and acc_inv_id = Recdef.acc_inv_id *)
(* and ltof_ref = Recdef.ltof_ref *)
(* and acc_rel = Recdef.acc_rel *)
(* and well_founded = Recdef.well_founded *)
(* and list_rewrite = Recdef.list_rewrite *)
(* and evaluable_of_global_reference = Recdef.evaluable_of_global_reference *)





let prove_with_tcc tcc_lemma_constr eqs : tactic =
  match !tcc_lemma_constr with
  | Undefined -> anomaly (Pp.str "No tcc proof !!")
  | Value lemma ->
	fun gls ->
(* 	  let hid = next_ident_away_in_goal h_id (pf_ids_of_hyps gls) in *)
(* 	  let ids = hid::pf_ids_of_hyps gls in  *)
	  tclTHENLIST
	    [
(* 	      generalize [lemma]; *)
(* 	      h_intro hid; *)
(* 	      Elim.h_decompose_and (mkVar hid); *)
	      tclTRY(list_rewrite true eqs);
(* 	      (fun g ->  *)
(* 		 let ids' = pf_ids_of_hyps g in  *)
(* 		 let ids = List.filter (fun id -> not (List.mem id ids)) ids' in  *)
(* 		 rewrite *)
(* 	      ) *)
	      Proofview.V82.of_tactic (Eauto.gen_eauto (false,5) [] (Some []))
	    ]
	    gls
  | Not_needed -> tclIDTAC

let backtrack_eqs_until_hrec hrec eqs : tactic =
  fun gls ->
    let eqs = List.map mkVar eqs in
    let rewrite =
      tclFIRST (List.map (fun x -> Proofview.V82.of_tactic (Equality.rewriteRL x)) eqs )
    in
    let _,hrec_concl  = decompose_prod (project gls) (pf_unsafe_type_of gls (mkVar hrec)) in
    let f_app = Array.last (snd (destApp (project gls) hrec_concl)) in
    let f =  (fst (destApp (project gls) f_app)) in
    let rec backtrack : tactic =
      fun g ->
	let f_app = Array.last (snd (destApp (project g) (pf_concl g))) in
	match EConstr.kind (project g) f_app with
	  | App(f',_) when eq_constr (project g) f' f -> tclIDTAC g
	  | _ -> tclTHEN rewrite backtrack g
    in
    backtrack gls


let rec rewrite_eqs_in_eqs eqs =
  match eqs with
    | [] -> tclIDTAC
    | eq::eqs ->

	  tclTHEN
	    (tclMAP
	       (fun id gl ->
		  observe_tac
		    (Format.sprintf "rewrite %s in %s " (Id.to_string eq) (Id.to_string id))
		    (tclTRY (Proofview.V82.of_tactic (Equality.general_rewrite_in true Locus.AllOccurrences
			       true (* dep proofs also: *) true id (mkVar eq) false)))
		    gl
	       )
	       eqs
	    )
	    (rewrite_eqs_in_eqs eqs)

let new_prove_with_tcc is_mes acc_inv hrec tcc_hyps eqs : tactic =
  fun gls ->
    (tclTHENLIST
       [
	 backtrack_eqs_until_hrec hrec eqs;
	 (* observe_tac ("new_prove_with_tcc ( applying "^(Id.to_string hrec)^" )" ) *)
	 (tclTHENS  (* We must have exactly ONE subgoal !*)
	    (Proofview.V82.of_tactic (apply (mkVar hrec)))
	    [ tclTHENLIST
		[
		  (Proofview.V82.of_tactic (keep (tcc_hyps@eqs)));
		  (Proofview.V82.of_tactic (apply (Lazy.force acc_inv)));
		  (fun g ->
		     if is_mes
		     then
		       Proofview.V82.of_tactic (unfold_in_concl [(Locus.AllOccurrences, evaluable_of_global_reference (delayed_force ltof_ref))]) g
		     else tclIDTAC g
		  );
		  observe_tac "rew_and_finish"
		    (tclTHENLIST
		       [tclTRY(list_rewrite false (List.map (fun v -> (mkVar v,true)) eqs));
			observe_tac "rewrite_eqs_in_eqs" (rewrite_eqs_in_eqs eqs);
			 (observe_tac "finishing using"
			   (
			    tclCOMPLETE(
				    Eauto.eauto_with_bases
				      (true,5)
				      [(fun _ sigma -> (sigma, Lazy.force refl_equal))]
                                      [Hints.Hint_db.empty TransparentState.empty false]
				  )
			   )
			)
		       ]
		    )
		]
	    ])
       ])
      gls


let is_valid_hypothesis sigma predicates_name =
  let predicates_name = List.fold_right Id.Set.add predicates_name Id.Set.empty in
  let is_pte typ =
    if isApp sigma typ
    then
      let pte,_ = destApp sigma typ in
      if isVar sigma pte
      then Id.Set.mem (destVar sigma pte) predicates_name
      else false
    else false
  in
  let rec is_valid_hypothesis typ =
    is_pte typ ||
      match EConstr.kind sigma typ with
	| Prod(_,pte,typ') -> is_pte pte && is_valid_hypothesis typ'
	| _ -> false
  in
  is_valid_hypothesis

let prove_principle_for_gen
    (f_ref,functional_ref,eq_ref) tcc_lemma_ref is_mes
    rec_arg_num rec_arg_type relation gl =
  let princ_type = pf_concl gl in
  let princ_info = compute_elim_sig (project gl) princ_type in
  let fresh_id =
    let avoid = ref (pf_ids_of_hyps gl) in
    fun na ->
      let new_id =
	  match na with
	    | Name id -> fresh_id !avoid (Id.to_string id)
	    | Anonymous -> fresh_id !avoid "H"
      in
      avoid := new_id :: !avoid;
      Name new_id
  in
  let fresh_decl = map_name fresh_id in
  let princ_info : elim_scheme =
    { princ_info with
	params = List.map fresh_decl princ_info.params;
	predicates = List.map fresh_decl princ_info.predicates;
	branches = List.map fresh_decl princ_info.branches;
	args = List.map fresh_decl princ_info.args
    }
  in
  let wf_tac =
    if is_mes
    then
      (fun b -> Recdef.tclUSER_if_not_mes tclIDTAC b None)
    else fun _ -> prove_with_tcc tcc_lemma_ref []
  in
  let real_rec_arg_num = rec_arg_num - princ_info.nparams in
  let npost_rec_arg = princ_info.nargs - real_rec_arg_num + 1 in
(*   observe ( *)
(*     str "princ_type := " ++ pr_lconstr  princ_type ++ fnl () ++ *)
(*     str "princ_info.nparams := " ++ int princ_info.nparams ++ fnl () ++  *)

(*       str "princ_info.nargs := " ++ int princ_info.nargs ++ fnl () ++  *)
(*     str "rec_arg_num := " ++ int rec_arg_num ++ fnl() ++  *)
(* 	     str "real_rec_arg_num := " ++ int real_rec_arg_num ++ fnl () ++ *)
(* 	     str "npost_rec_arg := " ++ int npost_rec_arg ); *)
  let (post_rec_arg,pre_rec_arg) =
    Util.List.chop npost_rec_arg princ_info.args
  in
  let rec_arg_id =
    match List.rev post_rec_arg with
      | (LocalAssum (Name id,_) | LocalDef (Name id,_,_)) :: _ -> id
      | _ -> assert false
  in
(*   observe (str "rec_arg_id := " ++ pr_lconstr (mkVar rec_arg_id)); *)
  let subst_constrs = List.map (get_name %> Nameops.Name.get_id %> mkVar) (pre_rec_arg@princ_info.params) in
  let relation = substl subst_constrs relation in
  let input_type = substl subst_constrs rec_arg_type in
  let wf_thm_id = Nameops.Name.get_id (fresh_id (Name (Id.of_string "wf_R"))) in
  let acc_rec_arg_id =
    Nameops.Name.get_id (fresh_id (Name (Id.of_string ("Acc_"^(Id.to_string rec_arg_id)))))
  in
  let revert l =
    tclTHEN (Proofview.V82.of_tactic (Tactics.generalize (List.map mkVar l))) (Proofview.V82.of_tactic (clear l))
  in
  let fix_id = Nameops.Name.get_id (fresh_id (Name hrec_id)) in
  let prove_rec_arg_acc g =
      ((* observe_tac "prove_rec_arg_acc"  *)
	 (tclCOMPLETE
	    (tclTHEN
	       (Proofview.V82.of_tactic (assert_by (Name wf_thm_id)
		  (mkApp (delayed_force well_founded,[|input_type;relation|]))
		  (Proofview.V82.tactic (fun g -> (* observe_tac "prove wf" *) (tclCOMPLETE (wf_tac is_mes)) g))))
	       (
		 (* observe_tac  *)
(* 		   "apply wf_thm"  *)
		 Proofview.V82.of_tactic (Tactics.Simple.apply (mkApp(mkVar wf_thm_id,[|mkVar rec_arg_id|])))
	       )
	    )
	 )
      )
      g
  in
  let args_ids = List.map (get_name %> Nameops.Name.get_id) princ_info.args in
  let lemma =
    match !tcc_lemma_ref with
     | Undefined -> user_err Pp.(str "No tcc proof !!")
     | Value lemma -> EConstr.of_constr lemma
     | Not_needed -> EConstr.of_constr (UnivGen.constr_of_monomorphic_global @@ Coqlib.lib_ref "core.True.I")
  in
(*   let rec list_diff del_list check_list = *)
(*     match del_list with *)
(*          [] -> *)
(*            [] *)
(*       | f::r -> *)
(*           if List.mem f check_list then *)
(*                list_diff r check_list *)
(*           else *)
(*                f::(list_diff r check_list) *)
(*   in *)
  let tcc_list = ref [] in
  let start_tac gls =
    let hyps = pf_ids_of_hyps gls in
      let hid =
	next_ident_away_in_goal
	  (Id.of_string "prov")
	  (Id.Set.of_list hyps)
      in
      tclTHENLIST
	[
	  Proofview.V82.of_tactic (generalize [lemma]);
	  Proofview.V82.of_tactic (Simple.intro hid);
	  Proofview.V82.of_tactic (Elim.h_decompose_and (mkVar hid));
	  (fun g ->
	     let new_hyps = pf_ids_of_hyps g in
	     tcc_list := List.rev (List.subtract Id.equal new_hyps (hid::hyps));
	     if List.is_empty !tcc_list
	     then
	       begin
		 tcc_list := [hid];
		 tclIDTAC g
	       end
	     else thin [hid] g
	  )
	  ]
	  gls
  in
  tclTHENLIST
    [
      observe_tac "start_tac" start_tac;
      h_intros
	(List.rev_map (get_name %> Nameops.Name.get_id)
	   (princ_info.args@princ_info.branches@princ_info.predicates@princ_info.params)
	);
      (* observe_tac "" *) Proofview.V82.of_tactic (assert_by
	 (Name acc_rec_arg_id)
 	 (mkApp (delayed_force acc_rel,[|input_type;relation;mkVar rec_arg_id|]))
	 (Proofview.V82.tactic prove_rec_arg_acc)
      );
(*       observe_tac "reverting" *) (revert (List.rev (acc_rec_arg_id::args_ids)));
(*       (fun g -> observe (Printer.pr_goal (sig_it g) ++ fnl () ++  *)
(* 			   str "fix arg num" ++ int (List.length args_ids + 1) ); tclIDTAC g); *)
      (* observe_tac "h_fix " *) (Proofview.V82.of_tactic (fix fix_id (List.length args_ids + 1)));
(*       (fun g -> observe (Printer.pr_goal (sig_it g) ++ fnl() ++ pr_lconstr_env (pf_env g ) (pf_unsafe_type_of g (mkVar fix_id) )); tclIDTAC g); *)
      h_intros (List.rev (acc_rec_arg_id::args_ids));
      Proofview.V82.of_tactic (Equality.rewriteLR (mkConst eq_ref));
      (* observe_tac "finish" *) (fun gl' ->
	 let body =
	   let _,args = destApp (project gl') (pf_concl gl') in
	   Array.last args
	 in
	 let body_info rec_hyps =
	   {
	     nb_rec_hyps = List.length rec_hyps;
	     rec_hyps = rec_hyps;
	     eq_hyps = [];
	     info = body
	   }
	 in
	 let acc_inv =
	   lazy (
	     mkApp (
	       delayed_force acc_inv_id,
	       [|input_type;relation;mkVar rec_arg_id|]
	     )
	   )
	 in
	 let acc_inv = lazy (mkApp(Lazy.force acc_inv, [|mkVar  acc_rec_arg_id|])) in
	 let predicates_names =
	   List.map (get_name %> Nameops.Name.get_id) princ_info.predicates
	 in
	 let pte_info =
	   { proving_tac =
	       (fun eqs ->
(* 		  msgnl (str "tcc_list := "++ prlist_with_sep spc Ppconstr.pr_id  !tcc_list); *)
(* 		  msgnl (str "princ_info.args := "++ prlist_with_sep spc Ppconstr.pr_id  (List.map  (fun (na,_,_) -> (Nameops.Name.get_id na)) princ_info.args)); *)
(* 		  msgnl (str "princ_info.params := "++ prlist_with_sep spc Ppconstr.pr_id  (List.map  (fun (na,_,_) -> (Nameops.Name.get_id na)) princ_info.params)); *)
(* 		  msgnl (str "acc_rec_arg_id := "++  Ppconstr.pr_id acc_rec_arg_id); *)
(* 		  msgnl (str "eqs := "++ prlist_with_sep spc Ppconstr.pr_id  eqs); *)

		  (* observe_tac "new_prove_with_tcc"  *)
		    (new_prove_with_tcc
		       is_mes acc_inv fix_id

		       (!tcc_list@(List.map
			   (get_name %> Nameops.Name.get_id)
			   (princ_info.args@princ_info.params)
			)@ ([acc_rec_arg_id])) eqs
		    )

	       );
	     is_valid = is_valid_hypothesis (project gl') predicates_names
	   }
	 in
	 let ptes_info : pte_info Id.Map.t =
	   List.fold_left
	     (fun map pte_id ->
		Id.Map.add pte_id
		  pte_info
		  map
	     )
	     Id.Map.empty
	     predicates_names
	 in
	 let make_proof rec_hyps =
	   build_proof
	     false
	     [f_ref]
	     ptes_info
	     (body_info rec_hyps)
	 in
         (* observe_tac "instantiate_hyps_with_args"  *)
           (instantiate_hyps_with_args
	      make_proof
	      (List.map (get_name %> Nameops.Name.get_id) princ_info.branches)
	      (List.rev args_ids)
	   )
	   gl'
      )

    ]
    gl








