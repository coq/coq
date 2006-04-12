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
   msgnl (str "observation "++str s++str " raised exception " ++ 
	    Cerrors.explain_exn e ++ str "on goal " ++ goal ); 
   raise e;;


let observe_tac s tac g =
  if do_observe ()
  then do_observe_tac s tac g
  else tac g


let tclTRYD tac = 
  if  !Options.debug  || do_observe ()
  then (fun g -> try do_observe_tac "" tac g with _ -> tclIDTAC g)
  else tac


let list_chop ?(msg="") n l = 
  try 
    list_chop n l 
  with Failure (msg') -> 
    failwith (msg ^ msg')
  

let make_refl_eq type_of_t t  =
  let refl_equal_term = Lazy.force refl_equal in
  mkApp(refl_equal_term,[|type_of_t;t|])


type static_fix_info = 
    {
      idx : int;
      name : identifier;
      types : types
    }

type static_infos = 
    {
      fixes_ids : identifier list; 
      ptes_to_fixes : static_fix_info Idmap.t
    }

type 'a dynamic_info = 
    { 
      nb_rec_hyps : int;
      rec_hyps : identifier list ; 
      eq_hyps : identifier list;
      info : 'a
    }

let finish_proof dynamic_infos g = 
  observe_tac "finish" 
    h_assumption
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

let change_hyp_with_using hyp_id t tac = 
  fun g -> 
    let prov_id = pf_get_new_id hyp_id g in 
    tclTHENLIST 
      [
	forward (Some tac) (Genarg.IntroIdentifier prov_id) t;
	thin [hyp_id];
	h_rename prov_id hyp_id
      ] g

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


let nf_betaoiotazeta = Reductionops.local_strong Reductionops.whd_betaiotazeta 

let remove_useless_rel env sigma hyp_id (context:Sign.rel_context) t end_of_type t1 t2 =
    let rel_num = destRel t2 in

    let nb_kept = List.length context - rel_num 
    and nb_popped = rel_num - 1
    in

    (* We remove the equation *) 
    let new_end_of_type = pop end_of_type in
    
    let lt_relnum,ge_relnum = 
      list_chop  
	~msg:("removing useless variable "^(string_of_int rel_num)^" :")
	nb_popped
	context 
    in
    (* we rebuilt the type of hypothesis after the rel to remove *)
    let hyp_type_lt_relnum = 
      it_mkProd_or_LetIn ~init:new_end_of_type lt_relnum 
    in 
    (* we replace Rel 1 by t1 *) 
    let new_hyp_type_lt_relnum = subst1 t1 hyp_type_lt_relnum in 
    (* we resplit the type of hyp_type *)
    let new_lt_relnum,new_end_of_type = 
      Sign.decompose_prod_n_assum nb_popped new_hyp_type_lt_relnum 
    in
    (* and rebuilt new context of hyp *)
    let new_context = new_lt_relnum@(List.tl ge_relnum) in 
    let new_typ_of_hyp =
      nf_betaoiotazeta (it_mkProd_or_LetIn ~init:new_end_of_type new_context)
    in
    let prove_simpl_eq =
      tclTHENLIST
	[
	  tclDO (nb_popped + nb_kept) intro;
	  (fun g'  ->
	     let new_hyps_ids = pf_ids_of_hyps g' in
	     let popped_ids,others =
	       list_chop ~msg:"removing useless variable pop :"
		 nb_popped new_hyps_ids in
	     let kept_ids,_ =
	       list_chop ~msg: " removing useless variable kept : "
		 nb_kept others
	     in
	     let rev_to_apply =
	       (mkApp(Lazy.force refl_equal,[|Typing.type_of env sigma t1;t1|]))::
		 ((List.map mkVar popped_ids)@
		    (t1::
		       (List.map mkVar kept_ids)))
	       in
	     let to_refine = applist(mkVar hyp_id,List.rev rev_to_apply) in
	     refine to_refine g'
	  )
	]
    in
    let simpl_eq_tac = change_hyp_with_using hyp_id new_typ_of_hyp
      (observe_tac "prove_simpl_eq" prove_simpl_eq)
    in
    let new_end_of_type = nf_betaoiotazeta new_end_of_type in
    (new_context,new_end_of_type,simpl_eq_tac),new_typ_of_hyp,
  (str " removing useless variable " ++ str (string_of_int rel_num) )


let decompose_eq env sigma hyp_id (context:Sign.rel_context) t end_of_type t1 t2 = 
    let c1,args1 = destApp t1 
    and c2,args2 = destApp t2 
    in
    (* This tactic must be used after is_incompatible_eq *)
    assert (eq_constr c1 c2); 
    (* we remove this equation *)
    let new_end_of_type = pop end_of_type in 
    let new_eqs = 
      array_map2_i 
	(fun i arg1 arg2 -> 
	   let new_eq = 
	     let type_of_arg =  Typing.type_of env sigma arg1 in 
 	     mkApp(Lazy.force eq,[|type_of_arg;arg1;arg2|])
	   in
	    Anonymous,None,lift i new_eq
	)
	args1
	args2
    in
    let nb_new_eqs = Array.length new_eqs in 
    (* we add the new equation *) 
    let new_end_of_type = lift nb_new_eqs new_end_of_type in 
    let local_context = 
      List.rev (Array.to_list new_eqs) in 
    let new_end_of_type = it_mkProd_or_LetIn ~init:new_end_of_type local_context in
    let new_typ_of_hyp = 
      nf_betaoiotazeta (it_mkProd_or_LetIn ~init:new_end_of_type context) 
    in 
    let prove_pattern_simplification =
      let context_length = List.length context in
      tclTHENLIST 
	[
	  tclDO (context_length + nb_new_eqs) intro ;
	  (fun g -> 
	     let new_eqs,others = 
	       list_chop ~msg:"simplifying pattern : new_eqs" nb_new_eqs (pf_hyps g)
	     in
	     let context_hyps,_ = list_chop ~msg:"simplifying pattern : context_hyps" 
	       context_length others in
	     let eq_args = 
	       List.rev_map 
		 (fun (_,_, eq) -> let _,args = destApp eq in   args.(1),args.(2))
		 new_eqs 
	     in
	     let lhs_args,rhs_args = List.split eq_args in 
	     let lhs_eq = applist(c1,lhs_args) 
	     and rhs_eq = applist(c1,rhs_args) 
	     in 
	     let type_of_eq = pf_type_of g lhs_eq in 
	     let eq_to_assert = 
	       mkApp(Lazy.force eq,[|type_of_eq;lhs_eq;rhs_eq|])
	     in
	     let prove_new_eq = 
	       tclTHENLIST [
		 tclMAP 
		   (fun (id,_,_) -> 
		      (* The tclTRY here is used when trying to rewrite 
			 on Set 
			 eg (@cons A x l)=(@cons A x' l') generates 3 eqs 
			 A=A -> x=x' -> l = l' ...
			 
		      *)
		      tclTRY (Equality.rewriteLR (mkVar id))
		   )
		   new_eqs;
		 reflexivity
	       ]
	     in
	     let new_eq_id = pf_get_new_id  (id_of_string "H") g in 
	     let create_new_eq = 
	       forward         
		 (Some (observe_tac "prove_new_eq" (prove_new_eq)))
		 (Genarg.IntroIdentifier new_eq_id)        
		 eq_to_assert 
	     in
	     let to_refine =
	       applist (
		 mkVar hyp_id,
		 List.rev ((mkVar new_eq_id)::
			     (List.map (fun (id,_,_) -> mkVar id) context_hyps)))
	     in 
	     tclTHEN 
	       (observe_tac "create_new_eq" create_new_eq )
	       (observe_tac "refine in decompose_eq " (refine to_refine))
	       g
	  )
	]
    in
    let simpl_eq_tac = 
      change_hyp_with_using hyp_id new_typ_of_hyp (observe_tac "prove_pattern_simplification " prove_pattern_simplification)
    in 
    (context,nf_betaoiotazeta new_end_of_type,simpl_eq_tac),new_typ_of_hyp,
  str "simplifying an equation " 

let change_eq env sigma hyp_id (context:Sign.rel_context) x t end_of_type  = 
  if not (noccurn 1 end_of_type)
  then (* if end_of_type depends on this term we don't touch it  *)
    begin 
      observe (str "Not treating " ++ pr_lconstr t    );
      failwith "NoChange"; 
    end;
  let res,new_typ_of_hyp,msg = 
    if not (isApp t) then failwith "NoChange";
    let f,args = destApp t in 
    if not (eq_constr f (Lazy.force eq)) then failwith "NoChange"; 
      let t1 = args.(1) 
      and t2 = args.(2)
      in 
      if isRel t2 && closed0 t1 then (* closed_term = x with x bound in context *)
	begin
	  remove_useless_rel env sigma hyp_id (context:Sign.rel_context) t end_of_type t1 t2
	end 
      else if isAppConstruct t1 && isAppConstruct t2 (* C .... = C .... *) 
      then decompose_eq env sigma hyp_id context t end_of_type t1 t2
      else failwith "NoChange"
  in 
  observe (str "In " ++ Ppconstr.pr_id hyp_id ++ 
	     msg ++ fnl ()++ 
	     str "old_typ_of_hyp :=" ++
	     Printer.pr_lconstr_env
	     env
	       (it_mkProd_or_LetIn ~init:end_of_type ((x,None,t)::context))
	   ++ fnl () ++
	     str "new_typ_of_hyp := "++ 
	     Printer.pr_lconstr_env env new_typ_of_hyp ++ fnl ());
  (res:'a*'b*'c)
  



let is_property static_info t_x = 
  if isApp t_x 
  then 
    let pte,args = destApp t_x in 
    if isVar pte && array_for_all closed0 args 
    then Idmap.mem (destVar pte) static_info.ptes_to_fixes
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
  
(* 
let rewrite_until_var arg_num : tactic =
  let constr_eq =  Lazy.force eq in 
  let replace_if_unify arg (pat,cl,id,lhs)  : tactic =
    fun g ->
      try
	let (evd,matched) =
	  Unification.w_unify_to_subterm
	    (pf_env g) ~mod_delta:false (pat,arg) cl.Clenv.env
	in
	let cl' = {cl with Clenv.env = evd } in
	let c2 = Clenv.clenv_nf_meta cl' lhs in
	(Equality.replace matched c2) g
      with _ -> tclFAIL 0 (str "") g
  in
  let rewrite_on_step equalities : tactic =
    fun g ->
      match kind_of_term (pf_concl g) with
	| App(_,args) when (not (test_var args arg_num)) ->
(* 	    tclFIRST (List.map (fun a -> observe_tac (str "replace_if_unify") (replace_if_unify args.(arg_num) a)) equalities) g *)
	    tclFIRST (List.map (replace_if_unify args.(arg_num)) equalities) g
	| _ ->
	    raise (Util.UserError("", (str "No more rewrite" ++
					 pr_lconstr_env (pf_env g) (pf_concl g))))
  in
  fun g ->
    let equalities =
      List.filter
	(
	  fun (_,_,id_t) ->
	    match kind_of_term id_t with
	      | App(f,_) -> eq_constr f constr_eq
	      | _ -> false
	)
	(pf_hyps g)
    in
    let f (id,_,ctype)  =
      let c = mkVar id in
      let eqclause = Clenv.make_clenv_binding g (c,ctype) Rawterm.NoBindings in
      let clause_type = Clenv.clenv_type eqclause in
      let f,args = decompose_app (clause_type) in
      let rec split_last_two = function
	| [c1;c2] -> (c1, c2)
	| x::y::z ->
	    split_last_two (y::z)
	| _ ->
	    error ("The term provided is not an equivalence")
      in
      let (c1,c2) = split_last_two args in
      (c2,eqclause,id,c1)
    in
    let matching_hyps = List.map f equalities in
    tclTRY (tclREPEAT (tclPROGRESS (rewrite_on_step matching_hyps))) g

*)


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

let prove_rec_hyp eq_hyps fix_info =
  tclTHEN 
    (rewrite_until_var (fix_info.idx - 1) eq_hyps)
    (fun g -> 
       let _,pte_args = destApp (pf_concl g) in 
       let rec_hyp_proof = 
	 mkApp(mkVar fix_info.name,array_get_start pte_args) 
       in
       refine rec_hyp_proof g
    )

	 



let rec_pte_id = id_of_string "Hrec" 
let clean_hyp_with_heq static_infos eq_hyps hyp_id env sigma = 
  let coq_False = Coqlib.build_coq_False () in 
  let coq_True = Coqlib.build_coq_True () in 
  let coq_I = Coqlib.build_coq_I () in 
  let rec scan_type  context type_of_hyp : tactic = 
    if isLetIn type_of_hyp then 
      let real_type_of_hyp = it_mkProd_or_LetIn ~init:type_of_hyp context in
      let reduced_type_of_hyp = nf_betaoiotazeta real_type_of_hyp in 
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
	if is_property static_infos t_x then
	  begin
	    let pte,pte_args =  (destApp t_x) in 
	    let fix_info = Idmap.find (destVar pte) static_infos.ptes_to_fixes in 
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
		     tclTHENLIST
		       [ 
			 forward 
			   (Some (prove_rec_hyp eq_hyps fix_info))
			   (Genarg.IntroIdentifier rec_pte_id)
			   t_x;
			 refine to_refine
		       ]
		       g
		  )
		]
	    in
	    tclTHENLIST 
	      [
		observe_tac "hyp rec" 
		  (change_hyp_with_using hyp_id real_type_of_hyp prove_new_type_of_hyp);
		scan_type context popped_t'
	      ]
	  end
	else if eq_constr t_x coq_False then 
	  begin
	    observe (str "Removing : "++ Ppconstr.pr_id hyp_id++ 
		       str " since it has False in its preconds "
		    );
	    raise TOREMOVE;  (* False -> .. useless *)
	  end
	else if is_incompatible_eq t_x then raise TOREMOVE (* t_x := C1 ... =  C2 ... *) 
	else if eq_constr t_x coq_True  (* Trivial => we remove this precons *)
	then 
	  let _ = 
	    observe (str "In "++Ppconstr.pr_id hyp_id++ 
		       str " removing useless precond True"
		    ) 
	  in 
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
	    change_hyp_with_using hyp_id real_type_of_hyp (observe_tac "prove_trivial" prove_trivial);
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


let clean_goal_with_heq static_infos continue_tac dyn_infos  = 
  fun g -> 
    let env = pf_env g 
    and sigma = project g 
    in
    let tac,new_hyps = 
      List.fold_left ( 
	fun (hyps_tac,new_hyps) hyp_id ->
	  let hyp_tac,new_hyp = 
	    clean_hyp_with_heq static_infos dyn_infos.eq_hyps hyp_id env sigma 
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

let treat_new_case static_infos nb_prod continue_tac term dyn_infos = 
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
		   observe (pr_gls g' ++ fnl () ++ str "last hyp is" ++
			      pr_lconstr_env (pf_env g') new_term_value_eq
			   );
		   assert false
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
	 clean_goal_with_heq static_infos continue_tac new_infos  g'
      )
    ]
      g

let do_prove_princ_for_struct 
    (interactive_proof:bool)
    (fnames:constant list)
    static_infos
(*     (ptes:identifier list)  *)
(*     (fixes:(int*constr*identifier*constr) Idmap.t) *)
(*     (hyps: identifier list) *)
(*     (term:constr) *)
    dyn_infos
    : tactic =
(*   let fixes_ids = Idmap.fold (fun _ (_,_,id,_) acc -> id::acc) fixes [] in *)
  let rec do_prove_princ_for_struct_aux do_finalize dyn_infos : tactic = 
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
		       static_infos
		       nb_instanciate_partial 
		       (do_prove_princ_for_struct do_finalize) 
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
			   do_prove_princ_for_struct do_finalize new_infos g'
			) g
		  | _ ->
		      do_finalize dyn_infos g 
	      end
	  | Cast(t,_,_) -> 
	      do_prove_princ_for_struct do_finalize {dyn_infos with info = t} g
	  | Const _ | Var _ | Meta _ | Evar _ | Sort _ | Construct _ | Ind _ ->
	      do_finalize dyn_infos g
	  | App(_,_) ->
	      let f,args = decompose_app dyn_infos.info in
	      begin
		match kind_of_term f with
		  | Var _ | Construct _ | Rel _ | Evar _ | Meta _  | Ind _ ->
		      let new_infos = 
			{ dyn_infos with 
			    info = (f,args)
			}
		      in
		      do_prove_princ_for_struct_args do_finalize new_infos  g
		  | Const c when not (List.mem c fnames) ->
		      let new_infos = 
			{ dyn_infos with 
			    info = (f,args)
			}
		      in
		      do_prove_princ_for_struct_args do_finalize new_infos g
		  | Const _ ->
		      do_finalize dyn_infos  g
		  | _ ->
(* 		      observe *)
(* 			(str "Applied binders not yet implemented: in "++ fnl () ++ *)
(* 			   pr_lconstr_env (pf_env g) term ++ fnl () ++ *)
(* 			   pr_lconstr_env (pf_env g) f ++ spc () ++ str "is applied") ; *)
		      tclFAIL 0 (str "TODO : Applied binders not yet implemented") g
	      end
	  | Fix _ | CoFix _ ->
	      error ( "Anonymous local (co)fixpoints are not handled yet")

	  | Prod _ -> assert false
	  | LetIn _ -> 
	      let new_infos = 
		{ dyn_infos with 
		    info = nf_betaoiotazeta dyn_infos.info 
		}
	      in 

	      tclTHENLIST 
		[tclMAP 
		   (fun hyp_id -> h_reduce_with_zeta (Tacticals.onHyp hyp_id)) 
		   dyn_infos.rec_hyps;
		 h_reduce_with_zeta Tacticals.onConcl;
		 do_prove_princ_for_struct do_finalize new_infos
		] g
	  | _ ->
	      errorlabstrm "" (str "in do_prove_princ_for_struct found : "(* ++ *)
(* 				 pr_lconstr_env (pf_env g) term *)
			      )
  and do_prove_princ_for_struct do_finalize dyn_infos g =
(*     observe (str "proving with "++Printer.pr_lconstr term++ str " on goal " ++ pr_gls g); *)
    do_prove_princ_for_struct_aux do_finalize dyn_infos g
  and do_prove_princ_for_struct_args do_finalize dyn_infos (* f_args'  args *) :tactic =
    fun g ->
(*      if Tacinterp.get_debug () <> Tactic_debug.DebugOff  *)
(*      then msgnl (str "do_prove_princ_for_struct_args with "  ++  *)
(* 		   pr_lconstr_env (pf_env g) f_args' *)
(* 		); *)
      let (f_args',args) = dyn_infos.info in 
      let tac =
	match args with
	  | []  ->
	      do_finalize {dyn_infos with info = f_args'}
	  | arg::args ->
	      let do_finalize dyn_infos =
		let new_arg = dyn_infos.info in 
		tclTRYD
		  (do_prove_princ_for_struct_args
		     do_finalize
		     {dyn_infos with info = (mkApp(f_args',[|new_arg|])), args}
		  )
	      in
	      do_prove_princ_for_struct do_finalize 
		{dyn_infos with info = arg }
      in
      tclTRYD(tac ) g
  in
  let do_finish_proof dyn_infos = 
    clean_goal_with_heq 
      static_infos
      finish_proof dyn_infos
  in
  observe_tac "do_prove_princ_for_struct"
    (do_prove_princ_for_struct do_finish_proof dyn_infos) 

let is_pte_type t =
  isSort (snd (decompose_prod t))
    
let is_pte (_,_,t) = is_pte_type t

exception Not_Rec



let instanciate_hyps_with_args (do_prove:identifier list -> tactic) hyps args_id = 
  let args = Array.of_list (List.map mkVar  args_id) in 
  let instanciate_one_hyp hid = 
    tclORELSE
      ( (* we instanciate the hyp if possible  *)
(* 	tclTHENLIST *)
(* 	  [h_generalize [mkApp(mkVar hid,args)]; *)
(* 	   intro_erasing hid] *)
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
	   observe (str "Instanciation: removing hyp " ++ Ppconstr.pr_id hid);
	   thin [hid] g
	)
      )
  in
  (* if no args then no instanciation ! *)     
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
		types = new_type
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
	       tclORELSE
		 (h_mutual_fix this_fix_info.name this_fix_info.idx other_fix_info)
		 (tclFAIL 1000 (str "bad index" ++ 
				  str (string_of_int this_fix_info.idx) ++
				  str "offset := " ++
				  (str (string_of_int offset))))
		 g
	   | _,[] -> anomaly "Not a valid information"
     in
     let do_prove ptes_to_fixes args branches : tactic =
       fun g ->
	 let static_infos = 
	   {
	     ptes_to_fixes = ptes_to_fixes;
	     fixes_ids = 
	       Idmap.fold 
		 (fun _ fix_info acc -> fix_info.name::acc) 
		 ptes_to_fixes []
	   }
	 in
	 match kind_of_term (pf_concl g) with
	   | App(pte,pte_args) when isVar pte ->
	       begin
		 let pte = destVar pte in
		 try
		   if not (Idmap.mem pte ptes_to_fixes) then raise Not_Rec;
		   let nparams = List.length !params in
		   let args_as_constr = List.map mkVar  args in
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
		  let applied_body =
		    Reductionops.nf_beta
		      (applist(new_body,List.rev args_as_constr))
		  in
		  let do_prove branches applied_body =
		    do_prove_princ_for_struct
		      interactive_proof
		      (Array.to_list fnames)
		      static_infos
		      branches
		      applied_body
		  in
		  let replace_and_prove =
		    tclTHENS
		      (fun g ->
(* 			 observe (str "replacing " ++  *)
(* 				    pr_lconstr_env (pf_env g) (array_last pte_args) ++ *)
(* 				    str " with " ++  *)
(* 				    pr_lconstr_env (pf_env g) applied_body  ++  *)
(* 				    str " rec_arg_num is " ++ str (string_of_int rec_num) *)
(* 				 ); *)
			 (Equality.replace (array_last pte_args) applied_body) g
		      )
		      [
			clean_goal_with_heq 
			  static_infos do_prove 
			  {
			    nb_rec_hyps = List.length branches;
			    rec_hyps = branches;
			    info = applied_body;
			    eq_hyps = [];
			  } ;
			try
			  let id = List.nth (List.rev args_as_constr) (rec_num) in
			  (* observe (str "choosen var := "++ pr_lconstr id); *)
			  (tclTHENSEQ
			     [(h_simplest_case id);
			      Tactics.intros_reflexivity
			     ])
			with _ -> tclIDTAC
			
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
			     do_prove_princ_for_struct
			       interactive_proof
			       (Array.to_list fnames)
			       static_infos
			   in
			   clean_goal_with_heq static_infos
			     do_prove dyn_infos g'
			)
		     )
		     g
	       end
	   | _ -> assert false
     in
     tclTHENSEQ
       [
	 (fun g -> observe_tac "introducing params" (intro_with_remembrance  params princ_info.nparams) g);
	 (fun g -> observe_tac "introducing predicate" (intro_with_remembrance predicates  princ_info.npredicates) g);
	 (fun g -> observe_tac "introducing branches" (intro_with_remembrance branches princ_info.nbranches) g);
	 (fun g -> observe_tac "declaring fix(es)" mk_fixes g);
	 (fun g -> 
	    let nb_prod_g = nb_prod (pf_concl g) in 
	    tclTHENLIST [
	      tclDO nb_prod_g intro;
	      (fun g' -> 
		 let args = 
		   fst (list_chop ~msg:"args" nb_prod_g (pf_ids_of_hyps g')) 
		 in
		 let do_prove_on_branches branches : tactic =
		   observe_tac "proving" (do_prove !pte_to_fix args branches)
		 in
		   observe_tac "instanciating rec hyps" 
		   (instanciate_hyps_with_args do_prove_on_branches !branches (List.rev args))
		 g'
	      )
	    ]
	      g
	 )
       ]
       goal






















  
exception Toberemoved_with_rel of int*constr
exception Toberemoved
  
let compute_new_princ_type_from_rel rel_to_fun sorts princ_type =
  let princ_type_info = compute_elim_sig princ_type in 
  let env = Global.env () in 
(*   let type_sort = (Termops.new_sort_in_family InType) in  *)
  let change_predicate_sort i (x,_,t) = 
    let new_sort = sorts.(i) in
    let args,_ = decompose_prod t in 
    let real_args = 
      if princ_type_info.indarg_in_concl 
      then List.tl args 
      else args
    in
    x,None,compose_prod real_args (mkSort new_sort) 
  in
  let new_predicates = 
    list_map_i
      change_predicate_sort 
      0
      princ_type_info.predicates
  in
  let env_with_params_and_predicates = 
    Environ.push_rel_context 
      new_predicates
      (Environ.push_rel_context 
	 princ_type_info.params 
	 env
      )
  in
  let rel_as_kn = 
    fst (match princ_type_info.indref with
	   | Some (Libnames.IndRef ind) -> ind 
	   | _ -> failwith "Not a valid predicate"
	)
  in
  let pre_princ = 
    it_mkProd_or_LetIn 
      ~init:
      (it_mkProd_or_LetIn 
	 ~init:(option_fold_right
			   mkProd_or_LetIn
			   princ_type_info.indarg
			   princ_type_info.concl
			)
	 princ_type_info.args
      )
      princ_type_info.branches
  in
  let is_dom c =
    match kind_of_term c with
      | Ind((u,_)) -> u = rel_as_kn
      | Construct((u,_),_) -> u = rel_as_kn
      | _ -> false
  in
  let get_fun_num c =
    match kind_of_term c with
      | Ind(_,num) -> num
      | Construct((_,num),_) -> num
      | _ -> assert false
  in
  let dummy_var = mkVar (id_of_string "________") in
  let mk_replacement c i args =
    let res = mkApp(rel_to_fun.(i),Array.map pop (array_get_start args)) in 
(*     observe (str "replacing " ++ pr_lconstr c ++ str " by "  ++ pr_lconstr res); *)
    res
  in
  let rec has_dummy_var t  =
    fold_constr
      (fun b t -> b || (eq_constr t dummy_var) || (has_dummy_var t))
      false
      t
  in
  let rec compute_new_princ_type remove env pre_princ : types*(constr list) =
    let (new_princ_type,_) as res =
      match kind_of_term pre_princ with
	| Rel n ->
	    begin
	      try match Environ.lookup_rel n env with
		| _,_,t when is_dom t -> raise Toberemoved
		| _ -> pre_princ,[] with Not_found -> assert false
	    end
	| Prod(x,t,b) ->
	    compute_new_princ_type_for_binder remove mkProd env x t b
	| Lambda(x,t,b) ->
	    compute_new_princ_type_for_binder remove mkLambda env x t b
	| Ind _ | Construct _ when is_dom pre_princ -> raise Toberemoved
	| App(f,args) when is_dom f ->
	    let var_to_be_removed = destRel (array_last args) in
	    let num = get_fun_num f in
	    raise (Toberemoved_with_rel (var_to_be_removed,mk_replacement pre_princ num args))
	| App(f,args) ->
	    let is_pte = 
	      match kind_of_term f with 
		| Rel n ->  
		    is_pte (Environ.lookup_rel n env)
		| _ -> false 
	    in
	    let args = 
	      if is_pte && remove 
	      then array_get_start args 
	      else args 
	    in
	    let new_args,binders_to_remove =
	      Array.fold_right (compute_new_princ_type_with_acc remove env)
		args
		([],[])
	    in
	    let new_f,binders_to_remove_from_f = compute_new_princ_type remove env f in
	    applist(new_f, new_args),
	    list_union_eq eq_constr binders_to_remove_from_f binders_to_remove
	| LetIn(x,v,t,b) ->
	    compute_new_princ_type_for_letin remove env x v t b
	| _ -> pre_princ,[]
    in
(*     observennl ( *)
(*       match kind_of_term pre_princ with  *)
(* 	| Prod _ ->  *)
(* 	    str "compute_new_princ_type for "++ *)
(* 	      pr_lconstr_env env pre_princ ++ *)
(* 	      str" is "++ *)
(* 	      pr_lconstr_env env new_princ_type ++ fnl () *)
(* 	| _ -> str "" *)
(*     ); *)
    res
	
  and compute_new_princ_type_for_binder remove bind_fun env x t b =
    begin
      try
	let new_t,binders_to_remove_from_t = compute_new_princ_type remove env t in
	let new_x : name = get_name (ids_of_context env) x in
	let new_env = Environ.push_rel (x,None,t) env in
	let new_b,binders_to_remove_from_b = compute_new_princ_type remove new_env b in
	if List.exists (eq_constr (mkRel 1)) binders_to_remove_from_b
	then (pop new_b),filter_map (eq_constr (mkRel 1)) pop binders_to_remove_from_b
	else
	  (
	    bind_fun(new_x,new_t,new_b),
	    list_union_eq
	      eq_constr
	      binders_to_remove_from_t
	      (List.map pop binders_to_remove_from_b)
	  )
	
      with
	| Toberemoved ->
(* 	    msgnl (str "Decl of "++Ppconstr.pr_name x ++ str " is removed "); *)
	    let new_b,binders_to_remove_from_b = compute_new_princ_type  remove env (substnl [dummy_var] 1 b)  in
	    new_b, List.map pop binders_to_remove_from_b
	| Toberemoved_with_rel (n,c) ->
(* 	    msgnl (str "Decl of "++Ppconstr.pr_name x ++ str " is removed "); *)
	    let new_b,binders_to_remove_from_b = compute_new_princ_type  remove env (substnl [c] n b)  in
	    new_b, list_add_set_eq eq_constr (mkRel n) (List.map pop binders_to_remove_from_b)
    end
  and compute_new_princ_type_for_letin remove env x v t b =
    begin
      try
	let new_t,binders_to_remove_from_t = compute_new_princ_type remove env t in
	let new_v,binders_to_remove_from_v = compute_new_princ_type remove env v in
	let new_x : name = get_name (ids_of_context env) x in
	let new_env = Environ.push_rel (x,Some v,t) env in
	let new_b,binders_to_remove_from_b = compute_new_princ_type remove  new_env b in
	if List.exists (eq_constr (mkRel 1)) binders_to_remove_from_b
	then (pop new_b),filter_map (eq_constr (mkRel 1)) pop binders_to_remove_from_b
	else
	  (
	    mkLetIn(new_x,new_v,new_t,new_b),
	    list_union_eq
	      eq_constr
	      (list_union_eq eq_constr binders_to_remove_from_t binders_to_remove_from_v)
	      (List.map pop binders_to_remove_from_b)
	  )
	
      with
	| Toberemoved ->
(* 	    msgnl (str "Decl of "++Ppconstr.pr_name x ++ str " is removed "); *)
	    let new_b,binders_to_remove_from_b = compute_new_princ_type remove env (substnl [dummy_var] 1 b)  in
	    new_b, List.map pop binders_to_remove_from_b
	| Toberemoved_with_rel (n,c) ->
(* 	    msgnl (str "Decl of "++Ppconstr.pr_name x ++ str " is removed "); *)
	    let new_b,binders_to_remove_from_b = compute_new_princ_type remove env (substnl [c] n b)  in
	    new_b, list_add_set_eq eq_constr (mkRel n) (List.map pop binders_to_remove_from_b)
    end
  and  compute_new_princ_type_with_acc remove env e (c_acc,to_remove_acc)  =
	      let new_e,to_remove_from_e = compute_new_princ_type remove env e
	      in
	      new_e::c_acc,list_union_eq eq_constr to_remove_from_e to_remove_acc
  in
(*   observe (str "Computing new principe from " ++ pr_lconstr_env  env_with_params_and_predicates pre_princ); *)
  let pre_res,_ = 
    compute_new_princ_type princ_type_info.indarg_in_concl env_with_params_and_predicates pre_princ in 
  it_mkProd_or_LetIn  	 
    ~init:(it_mkProd_or_LetIn ~init:pre_res new_predicates)
    princ_type_info.params
    
  

let change_property_sort toSort princ princName = 
  let princ_info = compute_elim_sig princ in 
  let change_sort_in_predicate (x,v,t) = 
    (x,None,
     let args,_ = decompose_prod t in 
     compose_prod args (mkSort toSort)
    )
  in 
  let princName_as_constr = Tacinterp.constr_of_id (Global.env ()) princName in 
  let init = 
    let nargs =  (princ_info.nparams + (List.length  princ_info.predicates)) in 
    mkApp(princName_as_constr,
	  Array.init nargs
	    (fun i -> mkRel (nargs - i )))
  in
  it_mkLambda_or_LetIn
    ~init: 
    (it_mkLambda_or_LetIn ~init 
       (List.map change_sort_in_predicate princ_info.predicates)
    )
    princ_info.params
    

let pp_dur time time' = 
  str (string_of_float (System.time_difference time time'))

(* Things to be removed latter : just here to compare 
   saving proof with and without  normalizing the proof 
*)
let new_save id const (locality,kind) hook =
  let {const_entry_body = pft;
       const_entry_type = tpo;
       const_entry_opaque = opacity } = const in
  let l,r = match locality with
    | Decl_kinds.Local when Lib.sections_are_opened () ->
        let k = Decl_kinds.logical_kind_of_goal_kind kind in
	let c = Declare.SectionLocalDef (pft, tpo, opacity) in
	let _ = Declare.declare_variable id (Lib.cwd(), c, k) in
	(Decl_kinds.Local, Libnames.VarRef id)
    | Decl_kinds.Local ->
        let k = Decl_kinds.logical_kind_of_goal_kind kind in
        let kn = Declare.declare_constant id (DefinitionEntry const, k) in
	(Decl_kinds.Global, Libnames.ConstRef kn)
    | Decl_kinds.Global ->
        let k = Decl_kinds.logical_kind_of_goal_kind kind in
        let kn = Declare.declare_constant id (DefinitionEntry const, k) in
	(Decl_kinds.Global, Libnames.ConstRef kn) in
  let time1 = System.get_time () in
  Pfedit.delete_current_proof ();
  let time2 = System.get_time () in
  hook l r;
  time1,time2
(*   definition_message id *)





let new_save_named opacity =
(*   if do_observe ()  *)
(*   then  *)
  let time1 = System.get_time () in 
    let id,(const,persistence,hook) = Pfedit.cook_proof () in
    let time2 = System.get_time () in 
    let const = 
      { const with 
	  const_entry_body = (* nf_betaoiotazeta  *)const.const_entry_body ;
	  const_entry_opaque = opacity
      }
    in
    let time3 = System.get_time ()  in
    let time4,time5 = new_save id const persistence hook in
    let time6 = System.get_time () in 
    Pp.msgnl
      (str "cooking proof time : " ++ pp_dur time1 time2 ++ fnl () ++
	 str "reducing proof time : " ++ pp_dur time2 time3 ++ fnl () ++
	 str "saving proof time : " ++ pp_dur time3 time4 ++fnl () ++
	 str "deleting proof time : " ++ pp_dur time4 time5 ++fnl () ++
	 str "hook time :" ++ pp_dur time5 time6
      )
       
;;

(* End of things to be removed latter : just here to compare 
   saving proof with and without  normalizing the proof 
*)


let generate_functional_principle 
    interactive_proof
    old_princ_type sorts new_princ_name funs i proof_tac 
    = 
  let f = funs.(i) in 
  let type_sort = Termops.new_sort_in_family InType in 
  let new_sorts = 
    match sorts with 
      | None -> Array.make (Array.length funs) (type_sort)
      | Some a -> a
  in
  (* First we get the type of the old graph principle *)
  let mutr_nparams = (compute_elim_sig old_princ_type).nparams in 
  (* First we get the type of the old graph principle *)
   let new_principle_type =
    compute_new_princ_type_from_rel
      (Array.map mkConst funs)
      new_sorts
      old_princ_type
   in
(*    observe (str "new_principle_type : " ++ pr_lconstr new_principle_type); *)
  let base_new_princ_name,new_princ_name =
    match new_princ_name with
      | Some (id) -> id,id
      | None ->
	  let id_of_f = id_of_label (con_label f) in
	  id_of_f,Indrec.make_elimination_ident id_of_f (family_of_sort type_sort)
  in
  let names = ref [new_princ_name] in 
  let hook _ _  =
    if sorts = None 
    then
(*     let id_of_f = id_of_label (con_label f) in *)
    let register_with_sort fam_sort =
      let s = Termops.new_sort_in_family  fam_sort in
      let name = Indrec.make_elimination_ident base_new_princ_name fam_sort in
      let value =
	change_property_sort s new_principle_type new_princ_name
      in
(*       Pp.msgnl (str "new principle := " ++ pr_lconstr value); *)
      let ce =
	{ const_entry_body = value;
	  const_entry_type = None;
	  const_entry_opaque = false;
	  const_entry_boxed = Options.boxed_definitions()
	}
      in
      ignore(
	Declare.declare_constant
	  name
	  (Entries.DefinitionEntry ce,
	   Decl_kinds.IsDefinition (Decl_kinds.Scheme)
	  )
      );
      names := name :: !names
    in
    register_with_sort InProp;
    register_with_sort InSet
  in
  begin
    Command.start_proof
      new_princ_name
      (Decl_kinds.Global,(Decl_kinds.Proof Decl_kinds.Theorem))
      new_principle_type
      hook
    ;
    try
      let _tim1 = System.get_time ()  in
      Pfedit.by  (proof_tac (Array.map mkConst funs) mutr_nparams);
      let _tim2 =  System.get_time ()  in
(* 	begin *)
(* 	  let dur1 = System.time_difference tim1 tim2 in *)
(* 	  Pp.msgnl (str ("Time to compute proof: ") ++ str (string_of_float dur1)); *)
(* 	end; *)
      let do_save =  not (do_observe ()) && not interactive_proof in 
      let _ = 
	try 
	  Options.silently Command.save_named true;
	  let _dur2 = System.time_difference _tim2 (System.get_time ()) in
(* 	  Pp.msgnl (str ("Time to check proof: ") ++ str (string_of_float dur2)); *)
	  Options.if_verbose 
	    (fun () -> 
	       Pp.msgnl (
		 prlist_with_sep
		   (fun () -> str" is defined " ++ fnl ()) 
		   Ppconstr.pr_id
		   (List.rev !names) ++ str" is defined " 
	       )
	    ) 
	       ()
	with e when do_save -> 
	  msg_warning
	    (
	      Cerrors.explain_exn e
	    );
	  if not (do_observe ())
	  then begin Vernacentries.interp (Vernacexpr.VernacAbort None);raise e end
      in
      ()

(*       let tim3 = Sys.time ()  in *)
(* Pp.msgnl (str ("Time to save proof: ") ++ str (string_of_float (tim3 -. tim2))); *)

    with
      | e ->
	  msg_warning
	    (
	      Cerrors.explain_exn e
	    );
	  if not ( do_observe ())
	  then begin Vernacentries.interp (Vernacexpr.VernacAbort None);raise e end
  end






let get_funs_constant mp dp = 
  let rec get_funs_constant const e : (Names.constant*int) array = 
    match kind_of_term (snd (decompose_lam e)) with 
      | Fix((_,(na,_,_))) -> 
	  Array.mapi 
	    (fun i na -> 
	       match na with 
		 | Name id -> 
		     let const = make_con mp dp (label_of_id id) in 
		     const,i
		 | Anonymous -> 
		     anomaly "Anonymous fix" 
	    )
	    na
      | _ -> [|const,0|]
  in
  function const -> 
    let find_constant_body const = 
      match (Global.lookup_constant const ).const_body with
	| Some b ->
	    let body = force b in
	    let body = Tacred.cbv_norm_flags
	      (Closure.RedFlags.mkflags [Closure.RedFlags.fZETA])
	      (Global.env ())
	      (Evd.empty)
	      body
	    in
	    body
	| None -> error ( "Cannot define a principle over an axiom ")
    in
    let f = find_constant_body const in
    let l_const = get_funs_constant const f in 
    (* 
       We need to check that all the functions found are in the same block 
       to prevent Reset stange thing
    *) 
    let l_bodies = List.map find_constant_body (Array.to_list (Array.map fst l_const)) in 
    let l_params,l_fixes = List.split (List.map decompose_lam l_bodies) in 
    (* all the paremeter must be equal*) 
    let _check_params = 
      let first_params = List.hd l_params  in 
      List.iter 
	(fun params -> 
	   if not ((=) first_params params) 
	   then error "Not a mutal recursive block"
	)
	l_params
    in
    (* The bodies has to be very similar *) 
    let _check_bodies = 
      try 
	let extract_info is_first body = 
	  match kind_of_term body with 
	    | Fix((idxs,_),(na,ta,ca)) -> (idxs,na,ta,ca)
	    | _ -> 
		if is_first && (List.length l_bodies = 1) 
		then raise Not_Rec
		else error "Not a mutal recursive block"
	in
	let first_infos = extract_info true (List.hd l_bodies) in 
	let check body  = (* Hope this is correct *)
	  if not (first_infos = (extract_info false body)) 
	  then  error "Not a mutal recursive block"
	in 
	List.iter check l_bodies
      with Not_Rec -> ()
    in
    l_const
	
let make_scheme fas = 
  let env = Global.env () 
  and sigma = Evd.empty in
  let id_to_constr id = 
    Tacinterp.constr_of_id env  id
  in 
  let funs = List.map (fun (_,f,_) -> id_to_constr f) fas in 
  let first_fun = destConst (List.hd funs) in 
  let funs_mp,funs_dp,first_fun_id = Names.repr_con first_fun in 
  let first_fun_rel_id = mk_rel_id (id_of_label first_fun_id) in 
  let first_fun_kn = 
    (* Fixme: take into accour funs_mp and funs_dp *)
    fst (destInd (id_to_constr first_fun_rel_id))
  in
  let this_block_funs_indexes = get_funs_constant funs_mp funs_dp first_fun in
  let this_block_funs = Array.map fst this_block_funs_indexes in 
  let prop_sort = InProp in
  let funs_indexes = 
    let this_block_funs_indexes = Array.to_list this_block_funs_indexes in 
    List.map
      (function const -> List.assoc (destConst const) this_block_funs_indexes)
      funs
  in
  let ind_list = 
    List.map 
      (fun (idx) -> 
	 let ind = first_fun_kn,idx in 
	 let (mib,mip) = Global.lookup_inductive ind in
	 ind,mib,mip,true,prop_sort
      )
      funs_indexes
  in
  let l_schemes = List.map (Typing.type_of env sigma ) (Indrec.build_mutual_indrec env sigma ind_list) in 
  let i = ref (-1) in
  let sorts = 
    List.rev_map (fun (_,_,x) -> 
		Termops.new_sort_in_family (Pretyping.interp_elimination_sort x)
	     ) 
      fas 
  in
  let princ_names = List.map (fun (x,_,_) -> x) fas in 
  let _ = List.map2
    (fun princ_name scheme_type -> 
       incr i;
(*        observe (str "Generating " ++ Ppconstr.pr_id princ_name ++str " with " ++ *)
(* 	       pr_lconstr scheme_type ++ str " and " ++ (fun a -> prlist_with_sep spc (fun c -> pr_lconstr (mkConst c)) (Array.to_list a)) this_block_funs *)
(* 	       ); *)
       generate_functional_principle
	 false
	 scheme_type
	 (Some (Array.of_list sorts))
	 (Some princ_name)
	 this_block_funs
	 !i
	 (prove_princ_for_struct false !i (Array.of_list (List.map destConst funs)))
    )
    princ_names
    l_schemes 
  in
  ()

let make_case_scheme fa = 
  let env = Global.env () 
  and sigma = Evd.empty in
  let id_to_constr id = 
    Tacinterp.constr_of_id env  id
  in 
  let funs =  (fun (_,f,_) -> id_to_constr f) fa in 
  let first_fun = destConst  funs in 
  let funs_mp,funs_dp,first_fun_id = Names.repr_con first_fun in 
  let first_fun_rel_id = mk_rel_id (id_of_label first_fun_id) in 
  let first_fun_kn = 
    (* Fixme: take into accour funs_mp and funs_dp *)
    fst (destInd (id_to_constr first_fun_rel_id))
  in
  let this_block_funs_indexes = get_funs_constant funs_mp funs_dp first_fun in
  let this_block_funs = Array.map fst this_block_funs_indexes in 
  let prop_sort = InProp in
  let funs_indexes = 
    let this_block_funs_indexes = Array.to_list this_block_funs_indexes in 
    List.assoc (destConst funs) this_block_funs_indexes
  in
  let ind_fun = 
	 let ind = first_fun_kn,funs_indexes in 
	 ind,prop_sort
  in
  let scheme_type =  (Typing.type_of env sigma ) ((fun (ind,sf) -> Indrec.make_case_gen env sigma ind sf)  ind_fun) in 
  let sorts =
    (fun (_,_,x) ->
       Termops.new_sort_in_family (Pretyping.interp_elimination_sort x)
    )
      fa
  in
  let princ_name =  (fun (x,_,_) -> x) fa in
  let _ = 
(*     observe (str "Generating " ++ Ppconstr.pr_id princ_name ++str " with " ++ *)
(* 	       pr_lconstr scheme_type ++ str " and " ++ (fun a -> prlist_with_sep spc (fun c -> pr_lconstr (mkConst c)) (Array.to_list a)) this_block_funs *)
(* 	    ); *)
    generate_functional_principle
      false
      scheme_type
      (Some ([|sorts|]))
      (Some princ_name)
      this_block_funs
      0
      (prove_princ_for_struct false 0 [|destConst funs|])
  in
  ()
