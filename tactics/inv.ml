
(* $Id$ *)

open Pp
open Util
open Names
open Generic
open Term
open Global
open Sign
open Environ
open Printer
open Reduction
open Tacmach
open Proof_trees
open Clenv
open Tactics
open Wcclausenv
open Tacticals
open Tactics
open Elim
open Equality
open Typing

(* [make_inv_predicate (ity,args) C]
  
   is given the inductive type, its arguments, both the global
   parameters and its local arguments, and is expected to produce a
   predicate P such that if largs is the "local" part of the
   arguments, then (P largs) will be convertible with a conclusion of
   the form:

   <A1>a1=a1-><A2>a2=a2 ... -> C

   Algorithm: suppose length(largs)=n

   (1) Push the entire arity, [xbar:Abar], carrying along largs and
   the conclusion

   (2) Pair up each ai with its respective Rel version: a1==(Rel n),
   a2==(Rel n-1), etc.

   (3) For each pair, ai,Rel j, if the Ai is dependent - that is, the
   type of [Rel j] is an open term, then we construct the iterated
   tuple, [make_iterated_tuple] does it, and use that for our equation

   Otherwise, we just use <Ai>ai=Rel j

 *)

let named_push_and_liftl env n hyps t l =
  let rec pushrec = function
    | (0, t, (hyps,l)) -> (hyps,t,l)
    | (n, (DOP2(Prod,t,DLAM(na,b))), (hyps,l)) -> 
       pushrec (n-1, b, (push_and_lift (Environ.named_hd env t na,t) hyps l))
    | (n, (DOP2(Cast,t,_)), (hyps,l)) -> pushrec (n,t,(hyps,l))
    | _ -> error "push_and_liftl"
  in 
  pushrec (n,t,(hyps,l))

let named_push_lambda_and_liftl env n hyps t l = 
  let rec pushrec = function
    | (0, t, (hyps,l)) -> (hyps,t,l)
    | (n, (DOP2(Lambda,t,DLAM(na,b))), (hyps,l)) ->
       pushrec (n-1, b, (push_and_lift (Environ.named_hd env t na,t) hyps l))
    | (n, (DOP2(Cast,t,_)), (hyps,l)) -> pushrec (n,t,(hyps,l))
    | _ -> error "push_and_liftl"
  in 
  pushrec (n,t,(hyps,l))

let dest_match_eq gls eqn =
  try 
    dest_match gls eqn eq_pattern
  with _ -> 
    (try 
       dest_match gls eqn eqT_pattern
     with _ -> 
       (try 
	  dest_match gls eqn idT_pattern
        with _ -> errorlabstrm "dest_match_eq" 
	    [< 'sTR "no primitive equality here" >]))
    
let type_of_predicate_argument gls ity globargs =
  let env = pf_env gls in
  let sigma = project gls in 
  let sort = sort_of_goal gls  in
  let elim = Indrec.make_case_gen env sigma ity sort in
  let type_elim = type_of env sigma elim in
  let nparams = mind_nparams ity in
  let (hyps,predicate,_) = named_push_and_liftl env nparams [] type_elim [] in
  let (_,predicate,_) = lam_and_popl nparams hyps predicate [] in
  let prod = whd_beta env Evd.empty (applist (predicate,globargs)) in
  let (_,ty,_) = destProd prod in
  ty

let implicit = Sort implicit_sort

let change_sign env (vars,rels) =
  let env' = change_hyps (fun _ -> vars) env in
  List.fold_left 
    (fun env (n,t) -> 
       let tt = execute_type env Evd.empty t in push_rel (n,tt) env)
    env' rels

let make_inv_predicate (ity,args) c dflt_concl dep_option gls =
  let env = pf_env gls in
  let sigma = project gls in
  let sign = pf_hyps gls in
  let concl = (pf_concl gls) in
  let id = destVar c in 
  let nparams = mind_nparams ity in
  let (globargs,largs_init) = list_chop nparams args in
  let arity = hnf_prod_applist env sigma "make_inv_predicate" 
                (nf_betadeltaiota env sigma (mind_arity ity)) globargs in 
  let len = List.length largs_init in
  let hyps = [] in
  let largs = (List.map insert_lifted largs_init) in
  let (hyps,larg_var_list,concl,dephyp) =                   
    if not dep_option (* (dependent (VAR id) concl) *) then 
      (* We push de arity and leave concl unchanged *)
      let hyps_ar,_,largs_ar = named_push_and_liftl env len hyps arity largs in
      let larg_var_list =
        list_map_i 
          (fun i ai ->
             insert_lifted
               (DOP2(implicit,extract_lifted ai,Rel(len-i+1)))) 1 largs
      in 
      (hyps_ar,larg_var_list,concl,0)
    else 
      if not (dependent (VAR id) concl) then errorlabstrm "make_inv_predicate"
        [< 'sTR "Current goal does not depend on "; print_id id >]
      else   
       (* We abstract the conclusion of goal with respect to args and c to be
	* concl in order to rewrite and have c also rewritten when the case
        * will be done *)
        let p=type_of_predicate_argument gls ity globargs in
        let c2 =
          (match dflt_concl with
             | None -> abstract_list_all gls p concl (largs_init@[c])  
             | (Some concl) -> concl) 
	in  
        let hyps,_,largs =
          named_push_lambda_and_liftl env (nb_lam c2) hyps c2 largs in     
        let c3 = whd_beta env Evd.empty
                   (applist (c2,Array.to_list
                               (rel_vect (List.length largs)
                                  (nb_prod arity +1)))) 
	in
        let larg_var_list =
          list_map_i
            (fun i ai->
               insert_lifted
                 (DOP2(implicit,extract_lifted ai,Rel(len-i+2)))) 1 largs 
        in 
	(hyps,larg_var_list,c3,1)
  in
  (* Now the arity is pushed, and we need to construct the pairs
   * ai,Rel(n-i+1) *)
  (* Now, we can recurse down this list, for each ai,(Rel k) whether to
     push <Ai>(Rel k)=ai (when   Ai is closed).
   In any case, we carry along the rest of larg_var_list *)
  let rec build_concl (hyps,l) =
    match l with
      | [] ->
          let neqns = ((List.length hyps-dephyp)-len) in
          let hyps,concl,_ = prod_and_popl neqns hyps concl [] in
          let _,concl,_ = lam_and_popl (List.length hyps) hyps concl [] in 
	  (concl,neqns)
      | t::restlist ->
          let (ai,k) = 
	    match extract_lifted t with 
	      | DOP2(_,ai,Rel k) -> (ai,k) 
	      | _ -> assert false 
	  in
          let tk = (Typeops.relative (change_sign env (sign,hyps)) k).uj_val in
          let (lhs,eqnty,rhs) =
            if closed0 tk then 
	      (Rel k,tk,ai)
            else 
	      make_iterated_tuple Evd.empty
		(change_sign env (sign,hyps))
		(ai,type_of env Evd.empty ai)
		(Rel k,tk) 
	  in
          let type_type_rhs = type_of env sigma (type_of env sigma rhs) in
          let sort = pf_type_of gls (pf_concl gls) in 
          let eq_term = find_eq_pattern type_type_rhs sort in
          let eqn = applist (eq_term ,[eqnty;lhs;rhs]) in 
	  build_concl (push_and_lift (Anonymous,eqn) hyps restlist) 
  in
  let (predicate,neqns) = build_concl (hyps,larg_var_list) in
  (* OK - this predicate should now be usable by res_elimination_then to
     do elimination on the conclusion. *)
  (predicate,neqns)

(* The result of the elimination is a bunch of goals like:

           |- (cibar:Cibar)Equands->C

   where the cibar are either dependent or not.  We are fed a
   signature, with "true" for every recursive argument, and false for
   every non-recursive one.  So we need to do the
   sign_branch_len(sign) intros, thinning out all recursive
   assumptions.  This leaves us with exactly length(sign) assumptions.

   We save their names, and then do introductions for all the equands
   (there are some number of them, which is the other argument of the
   tactic)

   This gives us the #neqns equations, whose names we get also, and
   the #length(sign) arguments.

   Suppose that #nodep of these arguments are non-dependent.
   Generalize and thin them.

   This gives us #dep = #length(sign)-#nodep arguments which are
   dependent.

   Now, we want to take each of the equations, and do all possible
   injections to get the left-hand-side to be a variable.  At the same
   time, if we find a lhs/rhs pair which are different, we can
   discriminate them to prove false and finish the branch.

   Then, we thin away the equations, and do the introductions for the
   #nodep arguments which we generalized before.
 *)

(* Called after the case-assumptions have been killed off, and all the
   intros have been done.  Given that the clause in question is an
   equality (if it isn't we fail), we are responsible for projecting
   the equality, using Injection and Discriminate, and applying it to
   the concusion *)

let introsReplacing ids gls = 
  let rec introrec = function
    | [] -> tclIDTAC
    | id::tl ->
	(tclTHEN (tclORELSE (intro_replacing id)
		    (tclORELSE (intro_erasing id)
                       (intro_using id)))
           (introrec tl))
  in 
  introrec ids gls

(* Computes the subset of hypothesis in the local context whose
   type depends on t (should be of the form (VAR id)), then
   it generalizes them, applies tac to rewrite all occurrencies of t,
   and introduces generalized hypotheis.
   Precondition: t=(VAR id) *)
    
let rec dependent_hyps id idlist sign = 
  let rec dep_rec =function
    | [] -> []
    | (id1::l) -> 
	let id1ty = snd (lookup_var id1 sign) in  
	if occur_var id id1ty.body then id1::dep_rec l else dep_rec l
  in 
  dep_rec idlist 

let generalizeRewriteIntros tac depids id gls = 
  let dids = dependent_hyps id depids (pf_env gls) in
  (tclTHEN (bring_hyps (List.map in_some dids))
     (tclTHEN tac
	(introsReplacing dids)))
  gls

let var_occurs_in_pf gl id =
  occur_var id (pf_concl gl) or
  exists_sign (fun _ t -> occur_var id t) (pf_untyped_hyps gl)

let split_dep_and_nodep idl gl =
  (List.filter (var_occurs_in_pf gl) idl,
   List.filter (fun x -> not(var_occurs_in_pf gl x)) idl)

(* invariant: ProjectAndApply is responsible for erasing the clause
   which it is given as input
   It simplifies the clause (an equality) to use it as a rewrite rule and then
   erases the result of the simplification. *)

let dest_eq gls t =
  match dest_match_eq gls t with
    | [x;y;z] -> (x,y,z)
    | _ -> error "dest_eq: should be an equality"

(* invariant: ProjectAndApplyNoThining simplifies the clause (an equality) .
   If it can discriminate then the goal is proved, if not tries to use it as
   a rewrite rule. It erases the clause which is given as input *)

let projectAndApply thin cls depids gls =
  let subst_hyp_LR cls = tclTRY(hypSubst (out_some cls)  None) in
  let subst_hyp_RL cls = tclTRY(revHypSubst (out_some cls) None) in
  let subst_hyp gls = 
    let orient_rule cls = 
      let (t,t1,t2) = dest_eq gls (clause_type cls gls) in
      match (strip_outer_cast t1, strip_outer_cast t2) with
        | (VAR id1, _) -> generalizeRewriteIntros (subst_hyp_LR cls) depids id1
        | (_, VAR id2) -> generalizeRewriteIntros (subst_hyp_RL cls) depids id2
        | _ -> subst_hyp_RL cls
    in 
    onLastHyp orient_rule gls 
  in
  let (t,t1,t2) = dest_eq gls (clause_type cls gls)  in
  match (thin, strip_outer_cast t1, strip_outer_cast t2) with
    | (true, VAR id1,  _) -> generalizeRewriteIntros
          (tclTHEN (subst_hyp_LR cls) (clear_clause cls)) depids id1 gls
    | (false, VAR id1,  _) ->
        generalizeRewriteIntros (subst_hyp_LR cls) depids id1 gls
    | (true, _ , VAR id2) -> generalizeRewriteIntros
          (tclTHEN (subst_hyp_RL cls) (clear_clause cls)) depids id2 gls
    | (false, _ , VAR id2) ->
        generalizeRewriteIntros (subst_hyp_RL cls) depids id2 gls
    | (true, _, _) ->
        let deq_trailer neqns =
          tclDO neqns
            (tclTHEN intro (tclTHEN subst_hyp (onLastHyp clear_clause)))
        in 
	(tclTHEN (tclTRY (dEqThen deq_trailer cls)) (clear_clause cls)) gls
    | (false, _, _) -> 
        let deq_trailer neqns = tclDO neqns (tclTHEN intro subst_hyp) in 
	(tclTHEN (dEqThen deq_trailer cls) (clear_clause cls)) gls

(* Inversion qui n'introduit pas les hypotheses, afin de pouvoir les nommer
   soi-meme (proposition de Valerie). *)
let case_trailer_gene othin neqns ba gl =
  let (depids,nodepids) = split_dep_and_nodep ba.assums gl in
  let rewrite_eqns =
    match othin with
      | Some thin ->
          onLastHyp
            (fun last ->
               (tclTHEN
                  (tclDO neqns
                     (tclTHEN intro
                        (onLastHyp
                           (fun cls ->
                              tclTRY (projectAndApply thin cls depids)))))
		  (tclTHEN
                     (onCL (compose List.rev (afterHyp (out_some last))) 
			bring_hyps)
                     (onCL (afterHyp (out_some last)) clear_clauses))))
      | None -> tclIDTAC
  in
  (tclTHEN (tclDO neqns intro)
     (tclTHEN (bring_hyps (List.map in_some nodepids))
	(tclTHEN (clear_clauses (List.map in_some nodepids))
	   (tclTHEN (onCL (compose List.rev (nLastHyps neqns)) bring_hyps)
	      (tclTHEN (onCL (nLastHyps neqns) clear_clauses)
		 (tclTHEN rewrite_eqns
		    (tclMAP (fun id ->
			       (tclORELSE (clear_clause (Some id))
				  (tclTHEN (bring_hyps [Some id])
				     (clear_clause (Some id)))))
		       depids)))))))
  gl

(* Introduction of the equations on arguments
   othin: discriminates Simple Inversion, Inversion and Inversion_clear
     None: the equations are introduced, but not rewritten
     Some thin: the equations are rewritten, and cleared if thin is true *)

let case_trailer othin neqns ba gl =
  let (depids,nodepids) = split_dep_and_nodep ba.assums gl in
  let rewrite_eqns =
    match othin with
      | Some thin ->
          (tclTHEN (onCL (compose List.rev (nLastHyps neqns)) bring_hyps)
             (tclTHEN (onCL (nLastHyps neqns) clear_clauses)
		(tclTHEN
		   (tclDO neqns
                      (tclTHEN intro
			 (onLastHyp
			    (fun cls -> 
			       tclTRY (projectAndApply thin cls depids)))))
		   (tclTHEN (tclDO (List.length nodepids) intro)
		      (tclMAP (fun id -> 
				 tclTRY (clear_clause (Some id))) depids)))))
      | None -> tclIDTAC
  in
  (tclTHEN (tclDO neqns intro)
     (tclTHEN (bring_hyps (List.map in_some nodepids))
	(tclTHEN (clear_clauses (List.map in_some nodepids))
	   rewrite_eqns)))
  gl

let res_case_then gene thin indbinding c dflt_concl dep_option gl =
  let (wc,kONT) = startWalk gl in
  let t = 
    strong_prodspine (fun _ _ -> pf_whd_betadeltaiota gl) 
      (pf_env gl) (project gl) (pf_type_of gl c) in
  let indclause = mk_clenv_from wc (c,t) in
  let indclause' = clenv_constrain_with_bindings indbinding indclause in
  let newc = clenv_instance_template indclause' in
  let (ity,args) = decomp_app (clenv_instance_template_type indclause') in
  let ity = destMutInd ity in
  let (elim_predicate,neqns) =
    make_inv_predicate (ity,args) c dflt_concl dep_option gl in
  let nparams = mind_nparams ity in
  let largs = snd (list_chop nparams args) in
  let (cut_concl,case_tac) =
    if dep_option & (dependent c (pf_concl gl)) then 
      applist(elim_predicate,largs@[c]),case_then_using 
    else 
      applist(elim_predicate,largs),case_nodep_then_using 
  in
  let case_trailer_tac =
    if gene then case_trailer_gene thin neqns else case_trailer thin neqns
  in
  (tclTHENS
     (cut_intro cut_concl)
     [onLastHyp
        (fun cls->
           (tclTHEN (applyUsing
                       (applist(VAR (out_some cls),
                                list_tabulate
                                  (fun _ -> mkMeta(new_meta())) neqns)))
              Auto.default_auto));
      case_tac (introCaseAssumsThen case_trailer_tac)
        (Some elim_predicate) ([],[]) newc])
  gl

(* Error messages of the inversion tactics *)
let not_found_message ids =
  if List.length ids = 1 then
    [<'sTR "the variable"; 'sPC ; 'sTR (string_of_id (List.hd ids)) ; 'sPC;
      'sTR" was not found in the current environment" >]
  else 
    [<'sTR "the variables ["; 
      'sPC ; prlist (fun id -> [<'sTR (string_of_id id) ; 'sPC >]) ids;
      'sTR" ] were not found in the current environment" >]

let no_generalisation() =
  errorlabstrm "Inv"
    [< 'sTR "Cannot find a well typed generalisation of the goal">]
    
let dep_prop_prop_message id =
  errorlabstrm "Inv"
    [< 'sTR "Inversion on "; print_id id ;
       'sTR " would needs dependent elimination Prop-Prop" >]
 
let not_inductive_here id =
  errorlabstrm "mind_specif_of_mind"
    [< 'sTR "Cannot recognize an inductive predicate in "; print_id id ;
       'sTR ". If there is one, may be the structure of the arity or of the type of constructors is hidden by constant definitions." >]

let wrap_inv_error id = function
  | UserError ("abstract_list_all",_) -> no_generalisation ()
  | UserError ("Case analysis",s) -> errorlabstrm "Inv needs Nodep Prop Set" s
  | UserError("mind_specif_of_mind",_)  -> not_inductive_here id
  | UserError (a,b)  -> errorlabstrm "Inv" b
  | Invalid_argument "it_list2" -> dep_prop_prop_message id
  | Invalid_argument("mind_specif_of_mind")  -> not_inductive_here id
  | Not_found  ->  errorlabstrm "Inv" (not_found_message [id]) 
  | e -> raise e

let inv gene com dflt_concl dep_option id =
  let inv_tac = res_case_then gene com [] (VAR id) dflt_concl dep_option in
  let tac =
    if com = Some true (* if Inversion_clear, clear the hypothesis *) then 
      tclTHEN inv_tac (tclTRY (clear_clause (Some id)))
    else 
      inv_tac
  in 
  fun gls -> try tac gls with e -> wrap_inv_error id e

let hinv_kind = Identifier (id_of_string "HalfInversion")
let inv_kind = Identifier (id_of_string "Inversion")
let invclr_kind = Identifier (id_of_string "InversionClear")

let com_of_id id =
  if id = hinv_kind then None
  else if id = inv_kind then Some false
  else Some true

(* Inv generates nodependent inversion *)
let (half_inv_tac, inv_tac, inv_clear_tac) =
  let gentac =
    hide_tactic "Inv"
      (function
	 | [ic; Identifier id] -> inv false (com_of_id ic) None false id
	 | _ -> anomaly "Inv called with bad args")
  in
  ((fun id -> gentac [hinv_kind; Identifier id]),
   (fun id -> gentac [inv_kind; Identifier id]),
   (fun id -> gentac [invclr_kind; Identifier id]))

(* Inversion without intros. No vernac entry yet! *)
let named_inv =
  let gentac =
    hide_tactic "NamedInv"
      (function
	 | [ic; Identifier id] -> inv true (com_of_id ic) None false id
	 | _ -> anomaly "NamedInv called with bad args")
  in 
  (fun ic id -> gentac [ic; Identifier id])

(* Generates a dependent inversion with a certain generalisation of the goal *)
let (half_dinv_tac, dinv_tac, dinv_clear_tac) =
  let gentac =
    hide_tactic "DInv"
      (function
	 | [ic; Identifier id] -> inv false (com_of_id ic) None true id
	 | _ -> anomaly "DInv called with bad args")
  in
  ((fun id -> gentac [hinv_kind; Identifier id]),
   (fun id -> gentac [inv_kind; Identifier id]),
   (fun id -> gentac [invclr_kind; Identifier id]))

(* generates a dependent inversion using a given generalisation of the goal *)
let (half_dinv_with, dinv_with, dinv_clear_with) =
  let gentac =
    hide_tactic "DInvWith"
      (function
	 | [ic; Identifier id; Command com] ->
             fun gls -> 
	       inv false (com_of_id ic)
		 (Some (pf_constr_of_com gls com)) true id gls
	 | _ -> anomaly "DInvWith called with bad args")
  in
  ((fun id com -> gentac [hinv_kind; Identifier id; Command com]),
   (fun id com -> gentac [inv_kind; Identifier id; Command com]),
   (fun id com -> gentac [invclr_kind; Identifier id; Command com]))

(* InvIn will bring the specified clauses into the conclusion, and then
 * perform inversion on the named hypothesis.  After, it will intro them
 * back to their places in the hyp-list. *)

let invIn com id ids gls =
  let nb_prod_init = nb_prod (pf_concl gls) in
  let intros_replace_ids gls =
    let nb_of_new_hyp =
      nb_prod (pf_concl gls) - (List.length ids + nb_prod_init)
    in 
    if nb_of_new_hyp < 1 then 
      introsReplacing ids gls
    else 
      (tclTHEN (tclDO nb_of_new_hyp intro) (introsReplacing ids)) gls
  in
  try 
    (tclTHEN (bring_hyps (List.map in_some ids))
       (tclTHEN (inv false com None false id)
          (intros_replace_ids)))
    gls
  with e -> wrap_inv_error id e

let invIn_tac =
  let gentac =
    hide_tactic "InvIn"
      (function
	 | (com::(Identifier id)::hl) ->
	     let hl' =
	       List.map (function
			   | Identifier id -> id
			   | _ -> anomaly "InvIn called with bas args") hl 
	     in
             invIn (com_of_id com) id hl'
	 | _ -> anomaly "InvIn called with bad args")
  in 
  fun com id hl ->
    gentac
      ((Identifier (id_of_string com))
       ::(Identifier id)
       ::(List.map (fun id -> (Identifier id)) hl))
