(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
open Tacexpr
open Declarations
open Util
open Names
open Term
open Pp
open Libnames
open Tacticals
open Tactics
open Indfun_common
open Tacmach
open Sign
open Hiddentac

(* Some pretty printing function for debugging purpose *)

let pr_binding prc  = 
  function
    | loc, Rawterm.NamedHyp id, c -> hov 1 (Ppconstr.pr_id id ++ str " := " ++ Pp.cut () ++ prc c)
    | loc, Rawterm.AnonHyp n, c -> hov 1 (int n ++ str " := " ++ Pp.cut () ++ prc c)

let pr_bindings prc prlc = function
  | Rawterm.ImplicitBindings l ->
      brk (1,1) ++ str "with" ++ brk (1,1) ++
      Util.prlist_with_sep spc prc l
  | Rawterm.ExplicitBindings l ->
      brk (1,1) ++ str "with" ++ brk (1,1) ++ 
        Util.prlist_with_sep spc (fun b -> str"(" ++ pr_binding prlc b ++ str")") l
  | Rawterm.NoBindings -> mt ()


let pr_with_bindings prc prlc (c,bl) =
  prc c ++ hv 0 (pr_bindings prc prlc bl)



let pr_constr_with_binding prc (c,bl) :  Pp.std_ppcmds = 
  pr_with_bindings prc prc  (c,bl)

(* The local debuging mechanism *)
let msgnl = Pp.msgnl

let observe strm =
  if do_observe ()
  then Pp.msgnl strm
  else ()

let observennl strm =
  if do_observe ()
  then begin Pp.msg strm;Pp.pp_flush () end
  else ()


let do_observe_tac s tac g =
 try    let goal = begin try (Printer.pr_goal (sig_it g)) with _ -> assert false end in
 let v = tac g in msgnl (goal ++ fnl () ++ s ++(str " ")++(str "finished")); v
 with e ->
   let goal = begin try (Printer.pr_goal (sig_it g)) with _ -> assert false end in
   msgnl (str "observation "++ s++str " raised exception " ++ 
	    Cerrors.explain_exn e ++ str " on goal " ++ goal ); 
   raise e;;


let observe_tac s tac g =
  if do_observe ()
  then do_observe_tac (str s) tac g
  else tac g

(* [nf_zeta] $\zeta$-normalization of a term *)
let nf_zeta =       
  Reductionops.clos_norm_flags  (Closure.RedFlags.mkflags [Closure.RedFlags.fZETA])
    Environ.empty_env
    Evd.empty


(* [id_to_constr id] finds the term associated to [id] in the global environment *)
let id_to_constr id = 
  try
    Tacinterp.constr_of_id (Global.env ())  id
  with Not_found -> 
    raise (UserError ("",str "Cannot find " ++ Ppconstr.pr_id id))

(* [generate_type g_to_f f graph i] build the completeness (resp. correctness) lemma type if [g_to_f = true] 
   (resp. g_to_f = false) where [graph]  is the graph of [f] and is the [i]th function in the block. 

   [generate_type true f i] returns 
   \[\forall (x_1:t_1)\ldots(x_n:t_n), let fv := f x_1\ldots x_n in, forall res, 
   graph\ x_1\ldots x_n\ res \rightarrow res = fv \] decomposed as the context and the conclusion 

   [generate_type false f i] returns 
   \[\forall (x_1:t_1)\ldots(x_n:t_n), let fv := f x_1\ldots x_n in, forall res, 
   res = fv \rightarrow graph\ x_1\ldots x_n\ res\] decomposed as the context and the conclusion 
 *)

let generate_type g_to_f f graph i = 
  (*i we deduce the number of arguments of the function and its returned type from the graph i*)
  let graph_arity = Inductive.type_of_inductive (Global.env()) (Global.lookup_inductive (destInd graph))  in 
  let ctxt,_ = decompose_prod_assum graph_arity in 
  let fun_ctxt,res_type = 
    match ctxt with 
      | [] | [_] -> anomaly "Not a valid context"
      | (_,_,res_type)::fun_ctxt -> fun_ctxt,res_type
  in
  let nb_args = List.length fun_ctxt in
  let args_from_decl i decl = 
    match decl with 
      | (_,Some _,_) -> incr i; failwith "args_from_decl"
      | _ -> let j = !i in incr i;mkRel (nb_args - j  + 1) 
  in
  (*i We need to name the vars [res] and [fv] i*)
  let res_id = 
    Termops.next_global_ident_away 
      true
      (id_of_string "res")
      (map_succeed (function (Name id,_,_) -> id | (Anonymous,_,_) -> failwith "") fun_ctxt)
  in
  let fv_id = 
    Termops.next_global_ident_away 
      true
      (id_of_string "fv")
      (res_id::(map_succeed (function (Name id,_,_) -> id | (Anonymous,_,_) -> failwith "Anonymous!") fun_ctxt))
  in
  (*i we can then type the argument to be applied to the function [f] i*)
  let args_as_rels = 
    let i = ref 0 in
    Array.of_list ((map_succeed (args_from_decl i) (List.rev fun_ctxt))) 
  in
  let args_as_rels = Array.map Termops.pop args_as_rels in
  (*i
    the hypothesis [res = fv] can then be computed 
    We will need to lift it by one in order to use it as a conclusion 
    i*)
  let res_eq_f_of_args =
    mkApp(Coqlib.build_coq_eq (),[|lift 2 res_type;mkRel 1;mkRel 2|])
  in 
  (*i 
    The hypothesis [graph\ x_1\ldots x_n\ res] can then be computed 
    We will need to lift it by one in order to use it as a conclusion 
    i*)  
  let graph_applied = 
    let args_and_res_as_rels = 
      let i = ref 0 in
      Array.of_list ((map_succeed (args_from_decl i) (List.rev ((Name res_id,None,res_type)::fun_ctxt))) )
    in
    let args_and_res_as_rels = 
      Array.mapi (fun i c -> if i <> Array.length args_and_res_as_rels - 1 then lift 1 c else c) args_and_res_as_rels
    in
    mkApp(graph,args_and_res_as_rels) 
  in 
  (*i The [pre_context]  is the defined to be the context corresponding to 
    \[\forall (x_1:t_1)\ldots(x_n:t_n), let fv := f x_1\ldots x_n in, forall res,  \]
    i*)
  let pre_ctxt = 
    (Name res_id,None,lift 1 res_type)::(Name fv_id,Some (mkApp(mkConst f,args_as_rels)),res_type)::fun_ctxt 
  in 
  (*i and we can return the solution depending on which lemma type we are defining i*)
  if g_to_f 
  then (Anonymous,None,graph_applied)::pre_ctxt,(lift 1 res_eq_f_of_args)
  else (Anonymous,None,res_eq_f_of_args)::pre_ctxt,(lift 1 graph_applied)


(* 
   [find_induction_principle f] searches and returns the [body] and the [type] of [f_rect]
   
   WARNING: while convertible, [type_of body] and [type] can be non equal
*)
let find_induction_principle f = 
  let f_as_constant =  match kind_of_term f with  
    | Const c' -> c'
    | _ -> error "Must be used with a function"
  in
  let infos = find_Function_infos f_as_constant in 
  match infos.rect_lemma with 
    | None -> raise Not_found 
    | Some rect_lemma -> 
	let rect_lemma = mkConst rect_lemma in 
	let typ = Typing.type_of (Global.env ()) Evd.empty rect_lemma in 
	rect_lemma,typ
	
  

(*     let fname =  *)
(*       match kind_of_term f with  *)
(* 	| Const c' ->  *)
(* 	    id_of_label (con_label c')  *)
(* 	| _ -> error "Must be used with a function"  *)
(*     in *)

(*     let princ_name =  *)
(*       ( *)
(* 	Indrec.make_elimination_ident *)
(* 	  fname *)
(* 	  InType *)
(*       ) *)
(*     in *)
(*     let c = (\* mkConst(mk_from_const (destConst f) princ_name ) in  *\) failwith "" in  *)
(*     c,Typing.type_of (Global.env ()) Evd.empty c *)


let rec generate_fresh_id x avoid i = 
  if i == 0 
  then [] 
  else
    let id = Termops.next_global_ident_away true x avoid in 
    id::(generate_fresh_id x (id::avoid) (pred i))


(* [prove_fun_correct functional_induction funs_constr graphs_constr schemes lemmas_types_infos i ] 
   is the tactic used to prove correctness lemma. 
   
   [functional_induction] is the tactic defined in [indfun] (dependency problem)
   [funs_constr], [graphs_constr] [schemes] [lemmas_types_infos] are the mutually recursive functions
   (resp. graphs of the functions and principles and correctness lemma types) to prove correct. 
   
   [i] is the indice of the function to prove correct

   The lemma to prove if suppose to have been generated by [generate_type] (in $\zeta$ normal form that is 
   it looks like~:
   [\forall (x_1:t_1)\ldots(x_n:t_n), forall res, 
   res = f x_1\ldots x_n in, \rightarrow graph\ x_1\ldots x_n\ res]


   The sketch of the proof is the following one~: 
   \begin{enumerate}
   \item intros until $x_n$
   \item $functional\ induction\ (f.(i)\ x_1\ldots x_n)$ using schemes.(i)
   \item for each generated branch intro [res] and [hres :res = f x_1\ldots x_n], rewrite [hres] and the 
   apply the corresponding constructor of the corresponding graph inductive.
   \end{enumerate}
   
*)
let prove_fun_correct functional_induction funs_constr graphs_constr schemes lemmas_types_infos i : tactic =
  fun g ->
    (* first of all we recreate the lemmas types to be used as predicates of the induction principle 
       that is~:
       \[fun (x_1:t_1)\ldots(x_n:t_n)=> fun  fv => fun res => res = fv \rightarrow graph\ x_1\ldots x_n\ res\]
    *)
    let lemmas =
      Array.map
	(fun (_,(ctxt,concl)) ->
	   match ctxt with
	     | [] | [_] | [_;_] -> anomaly "bad context"
	     | hres::res::(x,_,t)::ctxt ->
		 Termops.it_mkLambda_or_LetIn
		   ~init:(Termops.it_mkProd_or_LetIn ~init:concl [hres;res])
		   ((x,None,t)::ctxt)
	)
	lemmas_types_infos
    in
    (* we the get the definition of the graphs block *)
    let graph_ind = destInd graphs_constr.(i) in
    let kn = fst graph_ind in 
    let mib,_ = Global.lookup_inductive graph_ind in 
    (* and the principle to use in this lemma in $\zeta$ normal form *)
    let f_principle,princ_type = schemes.(i) in
    let princ_type =  nf_zeta princ_type in
    let princ_infos = Tactics.compute_elim_sig princ_type in
    (* The number of args of the function is then easilly computable *)
    let nb_fun_args = nb_prod (pf_concl g)  - 2  in
    let args_names = generate_fresh_id (id_of_string "x") [] nb_fun_args in
    let ids = args_names@(pf_ids_of_hyps g) in
    (* Since we cannot ensure that the funcitonnal principle is defined in the 
       environement and due to the bug #1174, we will need to pose the principle
       using a name 
    *)
    let principle_id = Termops.next_global_ident_away true (id_of_string "princ") ids in
    let ids = principle_id :: ids in
    (* We get the branches of the principle *)
    let branches = List.rev princ_infos.branches in
    (* and built the intro pattern for each of them *)
    let intro_pats =
      List.map
	(fun (_,_,br_type) ->
	   List.map
	     (fun id -> Genarg.IntroIdentifier id)
	     (generate_fresh_id (id_of_string "y") ids (List.length (fst (decompose_prod_assum br_type))))
	)
	branches
    in
    (* before building the full intro pattern for the principle *)
    let pat = Genarg.IntroOrAndPattern intro_pats in
    let eq_ind = Coqlib.build_coq_eq () in
    let eq_construct = mkConstruct((destInd eq_ind),1) in
    (* The next to referencies will be used to find out which constructor to apply in each branch *)
    let ind_number = ref 0 
    and min_constr_number = ref 0 in 
    (* The tactic to prove the ith branch of the principle *)
    let prove_branche i g =
      (* We get the identifiers of this branch *)
      let this_branche_ids =
	List.fold_right
	  (fun pat acc ->
	     match pat with
	       | Genarg.IntroIdentifier id -> Idset.add id acc
	       | _ -> anomaly "Not an identifier"
	  )
	  (List.nth intro_pats (pred i))
	  Idset.empty
      in
      (* and get the real args of the branch by unfolding the defined constant *)
      let pre_args,pre_tac =
	List.fold_right
	  (fun (id,b,t) (pre_args,pre_tac) ->
	     if Idset.mem id this_branche_ids
	     then
	       match b with
		 | None -> (id::pre_args,pre_tac)
		 | Some b ->
		     (pre_args,
		      tclTHEN (h_reduce (Rawterm.Unfold([[],EvalVarRef id])) allHyps) pre_tac
		     )
		     
	     else (pre_args,pre_tac)
	  )
	  (pf_hyps g)
	  ([],tclIDTAC)
      in
      (* 
	 We can then recompute the arguments of the constructor. 
	 For each [hid] introduced by this branch, if [hid] has type  
	 $forall res, res=fv -> graph.(j)\ x_1\ x_n res$ the corresponding arguments of the constructor are
	 [ fv (hid fv (refl_equal fv)) ]. 
	 
	 If [hid] has another type the corresponding argument of the constructor is [hid]
      *)
      let constructor_args =
	List.fold_right
	  (fun hid acc ->
	     let type_of_hid = pf_type_of g (mkVar hid) in
	     match kind_of_term type_of_hid with
	       | Prod(_,_,t') ->
		   begin
		     match kind_of_term t' with
		       | Prod(_,t'',t''') ->
			   begin
			     match kind_of_term t'',kind_of_term t''' with
			       | App(eq,args), App(graph',_)
				   when
				     (eq_constr eq eq_ind) &&
				       array_exists  (eq_constr graph') graphs_constr ->
				   ((mkApp(mkVar hid,[|args.(2);(mkApp(eq_construct,[|args.(0);args.(2)|]))|]))
				    ::args.(2)::acc)
			       | _ -> mkVar hid ::  acc
			   end
		       | _ -> mkVar hid :: acc
		   end
	       | _ -> mkVar hid :: acc
	  ) pre_args []
      in
      (* in fact we must also add the parameters to the constructor args *)
      let constructor_args =
	let params_id = fst (list_chop princ_infos.nparams args_names) in
	(List.map mkVar params_id)@(List.rev constructor_args)
      in
      (* We then get the constructor corresponding to this branch and 
	 modifies the references has needed i.e. 
	 if the constructor is the last one of the current inductive then 
	 add one the number of the inductive to take and add the number of constructor of the previous 
	 graph to the minimal constructor number 
      *)
      let constructor = 
	let constructor_num = i - !min_constr_number in 
	let length = Array.length (mib.Declarations.mind_packets.(!ind_number).Declarations.mind_consnames) in 
	if constructor_num <= length
	then 
	  begin 
	    (kn,!ind_number),constructor_num
	  end
	else 
	  begin
	    incr ind_number;
	    min_constr_number := !min_constr_number + length ;
	    (kn,!ind_number),1
	  end
      in
      (* we can then build the final proof term *)
      let app_constructor = applist((mkConstruct(constructor)),constructor_args) in
      (* an apply the tactic *)
      let res,hres =
	match generate_fresh_id (id_of_string "z") (ids(* @this_branche_ids *)) 2 with
	  | [res;hres] -> res,hres
	  | _ -> assert false
      in
      observe (str "constructor := " ++ Printer.pr_lconstr_env (pf_env g) app_constructor);
      (
	tclTHENSEQ
	  [
	    (* unfolding of all the defined variables introduced by this branch *)
	    observe_tac "unfolding" pre_tac;
	    (* $zeta$ normalizing of the conclusion *)
	    h_reduce
	      (Rawterm.Cbv
		 { Rawterm.all_flags with
		     Rawterm.rDelta = false ;
		     Rawterm.rConst = []
		 }
	      )
	      onConcl;
	    (* introducing the the result of the graph and the equality hypothesis *)
	    observe_tac "introducing" (tclMAP h_intro [res;hres]);
	    (* replacing [res] with its value *)
	    observe_tac "rewriting res value" (Equality.rewriteLR (mkVar hres));
	    (* Conclusion *)
	    observe_tac "exact" (h_exact app_constructor)
	  ]
      )
	g
    in
    (* end of branche proof *)
    let param_names = fst (list_chop princ_infos.nparams args_names) in
    let params = List.map mkVar param_names in
    let lemmas = Array.to_list (Array.map (fun c -> applist(c,params)) lemmas) in
    (* The bindings of the principle 
       that is the params of the principle and the different lemma types 
    *)
    let bindings =
      let params_bindings,avoid =
	List.fold_left2
	  (fun (bindings,avoid) (x,_,_) p ->
	     let id = Nameops.next_ident_away (Nameops.out_name x) avoid in
	     (dummy_loc,Rawterm.NamedHyp id,p)::bindings,id::avoid
	  )
	  ([],pf_ids_of_hyps g)
	  princ_infos.params
	  (List.rev params)
      in
      let lemmas_bindings =
	List.rev (fst  (List.fold_left2
	  (fun (bindings,avoid) (x,_,_) p ->
	     let id = Nameops.next_ident_away (Nameops.out_name x) avoid in 
	     (dummy_loc,Rawterm.NamedHyp id,nf_zeta p)::bindings,id::avoid)
	  ([],avoid)
	  princ_infos.predicates
	  (lemmas)))
      in
      Rawterm.ExplicitBindings (params_bindings@lemmas_bindings)
    in
    tclTHENSEQ
      [ observe_tac "intro args_names" (tclMAP h_intro args_names);
	observe_tac "principle" (forward
	  (Some (h_exact f_principle))
	  (Genarg.IntroIdentifier principle_id)
	  princ_type);
	tclTHEN_i
	  (observe_tac "functional_induction" (
	     fun g -> 
	       observe
		 (pr_constr_with_binding (Printer.pr_lconstr_env (pf_env g))  (mkVar principle_id,bindings));
	       functional_induction  false (applist(funs_constr.(i),List.map mkVar args_names))
		 (Some (mkVar principle_id,bindings))
		 pat g
	   ))
	  (fun i g -> observe_tac ("proving branche "^string_of_int i) (prove_branche i) g )
      ]
      g

(* [generalize_depedent_of x hyp g] 
   generalize every hypothesis which depends of [x] but [hyp] 
*)
let generalize_depedent_of x hyp g = 
  tclMAP 
    (function 
       | (id,None,t) when not (id = hyp) && 
	   (Termops.occur_var (pf_env g) x t) -> h_generalize [mkVar id]
       | _ -> tclIDTAC
    )
    (pf_hyps g)
    g






let rec reflexivity_with_destruct_cases g = 
  let destruct_case () = 
    try 
      match kind_of_term (snd (destApp (pf_concl g))).(2) with 
	| Case(_,_,v,_) -> 
	    tclTHENSEQ[
	      h_case (v,Rawterm.NoBindings);
	      intros;
	      observe_tac "reflexivity_with_destruct_cases" reflexivity_with_destruct_cases 
	    ]
	| _ -> reflexivity
    with _ -> reflexivity
  in
  tclFIRST
    [ reflexivity;
      destruct_case ()
    ]
    g


(* [prove_fun_complete funs graphs schemes lemmas_types_infos i] 
   is the tactic used to prove completness lemma. 
   
   [funcs], [graphs] [schemes] [lemmas_types_infos] are the mutually recursive functions
   (resp. definitions of the graphs of the functions, principles and correctness lemma types) to prove correct. 
   
   [i] is the indice of the function to prove complete

   The lemma to prove if suppose to have been generated by [generate_type] (in $\zeta$ normal form that is 
   it looks like~:
   [\forall (x_1:t_1)\ldots(x_n:t_n), forall res, 
   graph\ x_1\ldots x_n\ res, \rightarrow  res = f x_1\ldots x_n in]


   The sketch of the proof is the following one~: 
   \begin{enumerate}
   \item intros until $H:graph\ x_1\ldots x_n\ res$
   \item $elim\ H$ using schemes.(i)
   \item for each generated branch, intro  the news hyptohesis, for each such hyptohesis [h], if [h] has 
   type [x=?] with [x] a variable, then subst [x], 
   if [h] has type [t=?] with [t] not a variable then rewrite [t] in the subterms, else 
   if [h] is a match then destruct it, else do just introduce it, 
   after all intros, the conclusion should be a reflexive equality.
   \end{enumerate}
   
*)


let prove_fun_complete funcs graphs schemes lemmas_types_infos i : tactic = 
  fun g ->  
    (* We compute the types of the different mutually recursive lemmas 
       in $\zeta$ normal form
    *)
    let lemmas = 
      Array.map 
	(fun (_,(ctxt,concl)) -> nf_zeta (Termops.it_mkLambda_or_LetIn ~init:concl ctxt)) 
	lemmas_types_infos
    in
    (* We get the constant and the principle corresponding to this lemma *)
    let f = funcs.(i) in
    let graph_principle = nf_zeta schemes.(i)  in 
    let princ_type = pf_type_of g graph_principle in 
    let princ_infos = Tactics.compute_elim_sig princ_type in 
    (* Then we get the number of argument of the function 
       and compute a fresh name for each of them
    *)
    let nb_fun_args = nb_prod (pf_concl g)  - 2  in 
    let args_names = generate_fresh_id (id_of_string "x") [] nb_fun_args in
    let ids = args_names@(pf_ids_of_hyps g) in
    (* and fresh names for res H and the principle (cf bug bug #1174) *)
    let res,hres,graph_principle_id = 
      match generate_fresh_id (id_of_string "z") ids 3 with 
	| [res;hres;graph_principle_id] -> res,hres,graph_principle_id
	| _ -> assert false 
    in
    let ids = res::hres::graph_principle_id::ids in 
    (* we also compute fresh names for each hyptohesis of each branche of the principle *)
    let branches = List.rev princ_infos.branches in 
    let intro_pats = 
      List.map 
	(fun (_,_,br_type) -> 
	   List.map 
	     (fun id -> id) 
	     (generate_fresh_id (id_of_string "y") ids (nb_prod br_type))
	)
	branches
    in
    let eq_ind = Coqlib.build_coq_eq () in 
    (* We will need to change the function by its body 
       using [f_equation] if it is recursive (that is the graph is infinite 
       or unfold if the graph is finite 
    *)
    let rewrite_tac j ids : tactic = 
      let graph_def = graphs.(j) in 
      let infos =  try find_Function_infos (destConst funcs.(j)) with Not_found ->  error "No graph found" in 
      if infos.is_general ||  Rtree.is_infinite graph_def.mind_recargs
      then 
	let eq_lemma = 
	  try out_some (infos).equation_lemma
	  with Failure "out_some"  -> anomaly "Cannot find equation lemma"
	in 
	tclTHENSEQ[
	  tclMAP h_intro ids;
	  Equality.rewriteLR (mkConst eq_lemma);
	  (* Don't forget to $\zeta$ normlize the term since the principles have been $\zeta$-normalized *)
	  h_reduce 
	    (Rawterm.Cbv
	       {Rawterm.all_flags 
		with Rawterm.rDelta = false; 		 
	       }) 
	    onConcl
	  ;
	  h_generalize (List.map mkVar ids);
	  thin ids
	]
      else unfold_in_concl [([],Names.EvalConstRef (destConst f))]
    in
    (* [intros_with_rewrite] do the intros in each branch and treat each new hypothesis 
       (unfolding, substituting, destructing cases \ldots)
    *)
    let rec intros_with_rewrite_aux : tactic = 
      fun g -> 
	match kind_of_term (pf_concl g) with 
	  | Prod(_,t,t') -> 
	      begin 
		match kind_of_term t with 
		  | App(eq,args) when (eq_constr eq eq_ind) -> 
		      if isVar args.(1)
		      then 			
			let id = pf_get_new_id (id_of_string "y") g  in 
			tclTHENSEQ [ h_intro id;
				     generalize_depedent_of (destVar args.(1)) id; 
				     tclTRY (Equality.rewriteLR (mkVar id));
				     intros_with_rewrite
				   ] 
			  g
		      else
			begin 
			  let id = pf_get_new_id (id_of_string "y") g  in 
			  tclTHENSEQ[
			    h_intro id;
			    tclTRY (Equality.rewriteLR (mkVar id));
			    intros_with_rewrite
			  ] g
			end
		  | Ind _ when eq_constr t (Coqlib.build_coq_False ()) -> 
		      Tauto.tauto g
		  | Case(_,_,v,_) -> 
		      tclTHENSEQ[
			h_case (v,Rawterm.NoBindings);
			intros_with_rewrite
		      ] g
		  | LetIn _ -> 
		      tclTHENSEQ[
			h_reduce 
			  (Rawterm.Cbv
			     {Rawterm.all_flags 
			      with Rawterm.rDelta = false; 		 
			     }) 
			  onConcl
			;
			intros_with_rewrite
		      ] g
		  | _ -> 			
		      let id = pf_get_new_id (id_of_string "y") g  in 
		      tclTHENSEQ [ h_intro id;intros_with_rewrite] g
	      end
	  | LetIn _ -> 
	      tclTHENSEQ[
		h_reduce 
		  (Rawterm.Cbv
		     {Rawterm.all_flags 
		      with Rawterm.rDelta = false; 		 
		     }) 
		  onConcl
		;
		intros_with_rewrite
	      ] g
	  | _ -> tclIDTAC g 
    and intros_with_rewrite g = 
      observe_tac "intros_with_rewrite" intros_with_rewrite_aux g
    in
    (* The proof of each branche itself *)
    let ind_number = ref 0 in 
    let min_constr_number = ref 0 in
    let prove_branche i g = 
      (* we fist compute the inductive corresponding to the branch *)
      let this_ind_number = 
	let constructor_num = i - !min_constr_number in 
	let length = Array.length (graphs.(!ind_number).Declarations.mind_consnames) in 
	if constructor_num <= length
	then !ind_number
	else 
	  begin
	    incr ind_number;
	    min_constr_number := !min_constr_number + length;
	    !ind_number
	  end
      in
      let this_branche_ids = List.nth intro_pats (pred i) in
      tclTHENSEQ[
	(* we expand the definition of the function *)
        observe_tac "rewrite_tac" (rewrite_tac this_ind_number this_branche_ids);
	(* introduce hypothesis with some rewrite *)
        (intros_with_rewrite);
	(* The proof is (almost) complete *)
        observe_tac "reflexivity" (reflexivity_with_destruct_cases)
      ]
	g
    in
    let params_names = fst (list_chop princ_infos.nparams args_names) in
    let params = List.map mkVar params_names in 
    tclTHENSEQ 
      [ tclMAP h_intro (args_names@[res;hres]);
	observe_tac "h_generalize" 
	(h_generalize [mkApp(applist(graph_principle,params),Array.map (fun c -> applist(c,params)) lemmas)]);
	h_intro graph_principle_id;
	observe_tac "" (tclTHEN_i 
	  (observe_tac "elim" ((elim (mkVar hres,Rawterm.NoBindings) (Some (mkVar graph_principle_id,Rawterm.NoBindings)))))
	  (fun i g -> prove_branche i g ))
      ]
      g




let do_save () = Command.save_named false


(* [derive_correctness make_scheme functional_induction funs graphs] create correctness and completeness 
   lemmas for each function in [funs] w.r.t. [graphs]
   
   [make_scheme] is Functional_principle_types.make_scheme (dependency pb) and 
   [functional_induction] is Indfun.functional_induction (same pb) 
*)
   
let derive_correctness make_scheme functional_induction (funs: constant list) (graphs:inductive list) = 
  let funs = Array.of_list funs and graphs = Array.of_list graphs in
  let funs_constr = Array.map mkConst funs  in
  try 
    let graphs_constr = Array.map mkInd graphs in 
    let lemmas_types_infos = 
      Util.array_map2_i 
	(fun i f_constr graph -> 
	   let const_of_f = destConst f_constr in 
	   let (type_of_lemma_ctxt,type_of_lemma_concl) as type_info = 
	     generate_type false const_of_f graph i
	   in 
	   let type_of_lemma = Termops.it_mkProd_or_LetIn ~init:type_of_lemma_concl type_of_lemma_ctxt in 
	   let type_of_lemma = nf_zeta type_of_lemma in
	   observe (str "type_of_lemma := " ++ Printer.pr_lconstr type_of_lemma);
	   type_of_lemma,type_info
	)
	funs_constr
	graphs_constr 
    in
    let schemes = 
      (* The functional induction schemes are computed and not saved if there is more that one function 
	 if the block contains only one function we can safely reuse [f_rect]
      *)
      try
	if Array.length funs_constr <> 1 then raise Not_found;
	[| find_induction_principle funs_constr.(0) |]
      with Not_found -> 
	  Array.of_list 
	    (List.map 
	       (fun entry -> 
		  (entry.Entries.const_entry_body, out_some entry.Entries.const_entry_type )
	       )
	       (make_scheme (array_map_to_list (fun const -> const,Rawterm.RType None) funs))
	    )
    in
    let proving_tac = 
      prove_fun_correct functional_induction funs_constr graphs_constr schemes lemmas_types_infos
    in
    Array.iteri 
      (fun i f_as_constant -> 
	 let f_id = id_of_label (con_label f_as_constant) in
	 Command.start_proof 
	   (*i The next call to mk_correct_id is valid since we are constructing the lemma
	     Ensures by: obvious
	     i*) 
	   (mk_correct_id f_id)
	   (Decl_kinds.Global,(Decl_kinds.Proof Decl_kinds.Theorem))
	   (fst lemmas_types_infos.(i))
	   (fun _ _ -> ());
	 Pfedit.by (observe_tac ("prove correctness ("^(string_of_id f_id)^")") (proving_tac i));
	 do_save ();
	 let finfo = find_Function_infos f_as_constant in 
	 update_Function
	   {finfo with 
	      correctness_lemma = Some (destConst (Tacinterp.constr_of_id (Global.env ())(mk_correct_id f_id)))
	   }

      )
      funs;
    let lemmas_types_infos = 
      Util.array_map2_i 
	(fun i f_constr graph -> 
	   let const_of_f = destConst f_constr in 
	   let (type_of_lemma_ctxt,type_of_lemma_concl) as type_info = 
	     generate_type true  const_of_f graph i
	   in 
	   let type_of_lemma = Termops.it_mkProd_or_LetIn ~init:type_of_lemma_concl type_of_lemma_ctxt in 
	   let type_of_lemma = nf_zeta type_of_lemma in
	   observe (str "type_of_lemma := " ++ Printer.pr_lconstr type_of_lemma);
	   type_of_lemma,type_info
	)
	funs_constr
	graphs_constr 
    in
    let kn,_ as graph_ind  = destInd graphs_constr.(0) in 
    let  mib,mip = Global.lookup_inductive graph_ind in
    let schemes = 
      Array.of_list 
	(Indrec.build_mutual_indrec (Global.env ()) Evd.empty
	   (Array.to_list 
	      (Array.mapi
		 (fun i mip -> (kn,i),mib,mip,true,InType)
		 mib.Declarations.mind_packets
	      )
	   )
	)
    in
    let proving_tac = 
      prove_fun_complete funs_constr mib.Declarations.mind_packets schemes lemmas_types_infos
    in
    Array.iteri 
      (fun i f_as_constant -> 
	 let f_id = id_of_label (con_label f_as_constant) in
	 Command.start_proof 
	   (*i The next call to mk_complete_id is valid since we are constructing the lemma
	     Ensures by: obvious
	     i*) 
	   (mk_complete_id f_id)
	   (Decl_kinds.Global,(Decl_kinds.Proof Decl_kinds.Theorem))
	   (fst lemmas_types_infos.(i))
	   (fun _ _ -> ());
	 Pfedit.by (observe_tac ("prove completeness ("^(string_of_id f_id)^")") (proving_tac i));
	 do_save ();
	 let finfo = find_Function_infos f_as_constant in 
	 update_Function
	   {finfo with 
	      completeness_lemma = Some (destConst (Tacinterp.constr_of_id (Global.env ())(mk_complete_id f_id)))
	   }
      )
      funs;
  with e ->
    (* In case of problem, we reset all the lemmas *)
    (*i The next call to mk_correct_id is valid since we are erasing the lemmas
      Ensures by: obvious
      i*) 
    let first_lemma_id = 
      let f_id = id_of_label (con_label funs.(0)) in 
      
      mk_correct_id f_id 
    in
     ignore(try Vernacentries.vernac_reset_name (Util.dummy_loc,first_lemma_id) with _ -> ());
    raise e
	   
		   



(***********************************************)

(* [revert_graph kn post_tac hid] transforme an hypothesis [hid] having type Ind(kn,num) t1 ... tn res
   when [kn] denotes a graph block  into
   f_num t1... tn = res (by applying [f_complete] to the first type) before apply post_tac on the result 
   
   if the type of hypothesis has not this form or if we cannot find the completeness lemma then we do nothing
*)
let revert_graph kn post_tac hid g =
    let typ = pf_type_of g (mkVar hid) in 
    match kind_of_term typ with 
      | App(i,args) when isInd i -> 
	  let ((kn',num) as ind') = destInd i in 
	  if kn = kn' 
	  then (* We have generated a graph hypothesis so that we must change it if we can *)
	    let info = 
	      try find_Function_of_graph ind'
	      with Not_found -> (* The graphs are mutually recursive but we cannot find one of them !*)
		anomaly "Cannot retrieve infos about a mutual block"
	    in 
	    (* if we can find a completeness lemma for this function 
	       then we can come back to the functional form. If not, we do nothing 
	    *)
	    match info.completeness_lemma with 
	      | None -> tclIDTAC g
	      | Some f_complete -> 
		  let f_args,res = array_chop (Array.length args - 1) args in
		  tclTHENSEQ
		    [
		      h_generalize [applist(mkConst f_complete,(Array.to_list f_args)@[res.(0);mkVar hid])];
		      thin [hid];
		      h_intro hid; 
		      post_tac hid
		    ]
		    g
		    
	  else tclIDTAC g
      | _ -> tclIDTAC g


(* 
   [functional_inversion hid fconst f_correct ] is the functional version of [inversion]
   
   [hid] is the hypothesis to invert, [fconst] is the function to invert and  [f_correct]
   is the correctness lemma for [fconst].

   The sketch is the follwing~: 
   \begin{enumerate} 
   \item Transforms the hypothesis [hid] such that its type is now $res\ =\ f\ t_1 \ldots t_n$ 
   (fails if it is not possible)
   \item replace [hid] with $R\_f t_1 \ldots t_n res$ using [f_correct]
   \item apply [inversion] on [hid]
   \item finally in each branch, replace each  hypothesis [R\_f ..]  by [f ...] using [f_complete] (whenever 
   such a lemma exists)
   \end{enumerate}
*)
     
let functional_inversion kn hid fconst f_correct : tactic = 
  fun g -> 
    let old_ids = List.fold_right Idset.add  (pf_ids_of_hyps g) Idset.empty in 
    let type_of_h = pf_type_of g (mkVar hid) in 
    match kind_of_term type_of_h with 
      | App(eq,args) when eq_constr eq (Coqlib.build_coq_eq ())  -> 
	  let pre_tac,f_args,res = 
	    match kind_of_term args.(1),kind_of_term args.(2) with 
	      | App(f,f_args),_ when eq_constr f fconst -> 
		  ((fun hid -> h_symmetry (onHyp hid)),f_args,args.(2))
	      |_,App(f,f_args) when eq_constr f fconst -> 
		 ((fun hid -> tclIDTAC),f_args,args.(1)) 
	      | _ -> (fun hid -> tclFAIL 1 (mt ())),[||],args.(2)
	  in 
	  tclTHENSEQ[
	    pre_tac hid;
	    h_generalize [applist(f_correct,(Array.to_list f_args)@[res;mkVar hid])];
	    thin [hid];
	    h_intro hid;
	    Inv.inv FullInversion Genarg.IntroAnonymous (Rawterm.NamedHyp hid);
	    (fun g ->
	       let new_ids = List.filter (fun id -> not (Idset.mem id old_ids)) (pf_ids_of_hyps g) in 
	       tclMAP (revert_graph kn pre_tac)  (hid::new_ids)  g
	    );
	  ] g
      | _ -> tclFAIL 1 (mt ()) g



let invfun qhyp f  =  
  let f = 
    match f with 
      | ConstRef f -> f 
      | _ -> raise (Util.UserError("",str "Not a function"))
  in
  try 
    let finfos = find_Function_infos f in 
    let f_correct = mkConst(out_some finfos.correctness_lemma) 
    and kn = fst finfos.graph_ind
    in
    Tactics.try_intros_until (fun hid -> functional_inversion kn hid (mkConst f)  f_correct) qhyp 
  with 
    | Not_found ->  error "No graph found" 
    | Failure "out_some"  -> error "Cannot use equivalence with graph!"


let invfun qhyp f g = 
  match f with 
    | Some f -> invfun qhyp f g
    | None -> 
	Tactics.try_intros_until 
	  (fun hid g -> 
	     let hyp_typ = pf_type_of g (mkVar hid)  in 
	     match kind_of_term hyp_typ with 
	       | App(eq,args) when eq_constr eq (Coqlib.build_coq_eq ()) -> 
		   begin
		     let f1,_ = decompose_app args.(1) in 
		     try 
		       if not (isConst f1) then failwith "";
		       let finfos = find_Function_infos (destConst f1) in 
		       let f_correct = mkConst(out_some finfos.correctness_lemma) 
		       and kn = fst finfos.graph_ind
		       in
		       functional_inversion kn hid f1 f_correct g
		     with | Failure "" | Failure "out_some" | Not_found -> 
		       try 
			 let f2,_ = decompose_app args.(2) in 
			 if not (isConst f2) then failwith "";
			 let finfos = find_Function_infos (destConst f2) in 
			 let f_correct = mkConst(out_some finfos.correctness_lemma) 
			 and kn = fst finfos.graph_ind
			 in
			 functional_inversion kn hid  f2 f_correct g
		       with
			 | Failure "" -> 
			     errorlabstrm "" (str "Hypothesis" ++ Ppconstr.pr_id hid ++ str " must contain at leat one Function")
			 | Failure "out_some"  ->  
			     if do_observe () 
			     then
			       error "Cannot use equivalence with graph for any side of the equality"
			     else errorlabstrm "" (str "Cannot find inversion information for hypothesis " ++ Ppconstr.pr_id hid)
			 | Not_found -> 
			     if do_observe () 
			     then
			       error "No graph found for any side of equality" 
			     else errorlabstrm "" (str "Cannot find inversion information for hypothesis " ++ Ppconstr.pr_id hid)
		   end
	       | _ -> errorlabstrm "" (Ppconstr.pr_id hid ++ str " must be an equality ")
	  )
	  qhyp
	  g
