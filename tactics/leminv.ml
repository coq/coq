
(* $Id$ *)

open Pp
open Util
open Names
open Generic
open Term
open Sign
open Evd
open Printer
open Reduction
open Tacmach
open Proof_trees
open Clenv
open Declare
open Wcclausenv
open Pattern
open Tacticals
open Tactics
open Equality
open Inv

(* Fonctions temporaires pour relier la forme castée et la forme jugement *)
let tsign_of_csign (idl,tl) = (idl,List.map outcast_type tl)

let csign_of_tsign = map_sign_typ incast_type
(* FIN TMP *)

let not_work_message = "tactic fails to build the inversion lemma, may be because the predicate has arguments that depend on other arguments"

(* Inversion stored in lemmas *)

(* ALGORITHM:

   An inversion stored in a lemma is computed from a term-pattern, in
   a signature, as follows:

   Suppose we have an inductive relation, (I abar), in a signature Gamma:

       Gamma |- (I abar)

   Then we compute the free-variables of abar.  Suppose that Gamma is
   thinned out to only include these.

   [We need technically to require that all free-variables of the
    types of the free variables of abar are themselves free-variables
    of abar.  This needs to be checked, but it should not pose a
    problem - it is hard to imagine cases where it would not hold.]

   Now, we pose the goal:

       (P:(Gamma)Prop)(Gamma)(I abar)->(P vars[Gamma]).

   We execute the tactic:

   REPEAT Intro THEN (OnLastHyp (Inv NONE false o outSOME))

   This leaves us with some subgoals.  All the assumptions after "P"
   in these subgoals are new assumptions.  I.e. if we have a subgoal,

       P:(Gamma)Prop, Gamma, Hbar:Tbar |- (P ybar)

   then the assumption we needed to have was

      (Hbar:Tbar)(P ybar)

   So we construct all the assumptions we need, and rebuild the goal
   with these assumptions.  Then, we can re-apply the same tactic as
   above, but instead of stopping after the inversion, we just apply
   the respective assumption in each subgoal.

 *)
 
let thin_hyps_to_term (hyps,t) =
  let vars = (global_vars t) in
  rev_sign(fst(it_sign (fun ((hyps,globs) as sofar) id a ->
                          if List.mem id globs then
                            (add_sign (id,a) hyps,(global_vars a)@globs)
                          else sofar) (nil_sign,vars) hyps))

(* returns the sub_signature of sign corresponding to those identifiers that
 * are not global. *)

let get_local_sign sign =
  let lid = ids_of_sign sign in
  let globsign = Global.var_context() in
  let add_local id res_sign = 
    if not (mem_sign globsign id) then 
      add_sign (lookup_sign id sign) res_sign
    else 
      res_sign
  in 
  List.fold_right add_local lid nil_sign

(* returs the identifier of lid that was the latest declared in sign.
 * (i.e. is the identifier id of lid such that 
 * sign_length (sign_prefix id sign) > sign_length (sign_prefix id' sign) >
 * for any id'<>id in lid).
 * it returns both the pair (id,(sign_prefix id sign)) *)

let max_prefix_sign lid sign =
  let rec max_rec (resid,prefix) = function
    | [] -> (resid,prefix)
    | (id::l) -> 
	let pre = sign_prefix id sign in  
	if sign_length pre > sign_length prefix then 
          max_rec (id,pre) l
        else 
	  max_rec (resid,prefix) l
  in
  match lid with 
    | [] -> nil_sign
    | id::l -> snd (max_rec (id, sign_prefix id sign) l)

let rel_of_env env = 
  let rec rel_rec = function 
    | ([],  _) -> []
    | ((_::env), n) -> (Rel n)::(rel_rec (env, n+1))
  in 
  rel_rec (env, 1)

let build_app op env = applist (op, List.rev (rel_of_env env))

(* similar to prod_and_pop, but gives [na:T]B intead of (na:T)B *)

let prod_and_pop_named = function
  | ([], body, l, acc_ids) -> error "lam_and_pop"
  | (((na,t)::tlenv), body, l, acc_ids) -> 
      let id = next_name_away_with_default "a" na acc_ids in
      (tlenv,DOP2(Prod,t,DLAM((Name id),body)),
       List.map (function 
		   | (0,x) -> (0,lift (-1) x)
		   | (n,x) -> (n-1,x)) l,
       (id::acc_ids))

(* similar to prod_and_popl but gives [nan:Tan]...[na1:Ta1]B instead of
 * (nan:Tan)...(na1:Ta1)B  it generates new names with respect to l
    whenever nai=Anonymous *)

let prod_and_popl_named  n env t l = 
  let rec poprec = function
    | (0, (env,b,l,_)) -> (env,b,l)
    | (n, ([],_,_,_)) -> error "lam_and_popl"
    | (n, q) -> poprec (n-1, prod_and_pop_named q)
  in 
  poprec (n,(env,t,l,[]))

(* [dep_option] indicates wether the inversion lemma is dependent or not.
   If it is dependent and I is of the form (x_bar:T_bar)(I t_bar) then
   the stated goal will be (x_bar:T_bar)(H:(I t_bar))(P t_bar H) 
   where P:(x_bar:T_bar)(H:(I t_bar))[sort]            .
   The generalisation of such a goal at the moment of the dependent case should
   be easy

   If it is non dependent, then if [I]=(I t_bar) and (x_bar:T_bar) are thte
   variables occurring in [I], then the stated goal will be:
    (x_bar:T_bar)(I t_bar)->(P x_bar) 
   where P: P:(x_bar:T_bar)(H:(I t_bar)->[sort]     
*)

(* Adaption rapide : à relire *)
let compute_first_inversion_scheme sign i sort dep_option =
  let globenv = Global.env () in
  let (ity,largs) = find_mrectype globenv Evd.empty i in
  let ar = Global.mind_arity ity in 
  (* let ar = nf_betadeltaiota empty_evd (mind_arity ity) in *)
  let fv = global_vars i in
  let thin_sign = thin_hyps_to_term (sign,i) in
  if not(list_subset fv (ids_of_sign thin_sign)) then
    errorlabstrm "lemma_inversion"
      [< 'sTR"Cannot compute lemma inversion when there are" ; 'sPC ;
	 'sTR"free variables in the types of an inductive" ; 'sPC ;
	 'sTR"which are not free in its instance" >];
  let p = next_ident_away (id_of_string "P") (ids_of_sign sign) in
  if dep_option  then   
    let (pty,goal) =
      let (env,_,_) = push_and_liftl (nb_prod ar) []  ar [] in
      let h = next_ident_away (id_of_string "P") (ids_of_sign sign) in
      let (env1,_)= push_and_lift (Name h, (build_app (mkMutInd ity) env)) env [] in
      let (_,pty,_) = prod_and_popl_named (List.length env1) env1 sort [] in 
      let pHead= applist(VAR p, largs@[Rel 1]) 
      in  (pty, Environ.prod_name globenv (Name h,i,pHead))
    in 
    (prepend_sign thin_sign 
       (add_sign (p,nf_betadeltaiota globenv Evd.empty pty) nil_sign),
       goal)
  else  
    let local_sign = get_local_sign thin_sign in 
    let pHead= 
      applist(VAR p, 
	      List.rev(List.map (fun id -> VAR id) (ids_of_sign local_sign)))in
    let (pty,goal) = 
      (it_sign (fun b id ty -> mkNamedProd id ty b) 
	 sort local_sign, mkArrow i pHead) 
    in 
    let npty = nf_betadeltaiota globenv Evd.empty pty in
    let lid = global_vars npty in 
    let maxprefix = max_prefix_sign lid thin_sign in
    (prepend_sign local_sign (add_sign (p,npty)  maxprefix), goal)

(* [inversion_scheme sign I]

   Given a local signature, [sign], and an instance of an inductive
   relation, [I], inversion_scheme will prove the associated inversion
   scheme on sort [sort]. Depending on the value of [dep_option] it will
   build a dependent lemma or a non-dependent one *)

let inversion_scheme sign i sort dep_option inv_op =
  let (i,sign) = add_prods_sign Evd.empty (i,sign) in
  let sign = csign_of_tsign sign in
  let (invSign,invGoal) =
    compute_first_inversion_scheme sign i sort dep_option in
  let invSign = castify_sign Evd.empty invSign in
  if (not((list_subset (global_vars invGoal) (ids_of_sign invSign)))) then
    errorlabstrm "lemma_inversion"
      [< 'sTR"Computed inversion goal was not closed in initial signature" >];
  let invGoalj = get_type_of Evd.empty invSign invGoal in
  let pfs =
    mk_pftreestate
      (mkGOAL (mt_ctxt Spset.empty) invSign (j_val_cast invGoalj)) in
  let pfs =
    solve_pftreestate (tclTHEN intro 
			 (onLastHyp (comp inv_op outSOME))) pfs in
  let pf = proof_of_pftreestate pfs in
  let (pfterm,meta_types) = Refiner.extract_open_proof pf.goal.hyps pf in
  let invSign =
    sign_it
      (fun id ty sign ->
         if mem_sign (initial_sign()) id then sign
         else add_sign (id,ty) sign)
      invSign
      nil_sign 
  in
  let (invSign,mvb) =
    List.fold_left
      (fun (sign,mvb) (mv,mvty) ->
         let h = next_ident_away (id_of_string "H") (ids_of_sign sign) in 
	 (add_sign (h,mvty) sign,
          (mv,((VAR h):constr))::mvb))
      (csign_of_tsign invSign,[])
      meta_types 
  in
  let invProof =
    it_sign (fun b id ty -> mkNamedLambda id ty b)
      (strong (whd_meta mvb) pfterm) invSign 
  in
  invProof

open Discharge
open Constrtypes

let add_inversion_lemma name sign i sort dep_option inv_op =
  let invProof = inversion_scheme sign i sort dep_option inv_op in 
  machine_constant_verbose (initial_assumptions())
    ((name,false,NeverDischarge),invProof)

open Pfedit

(* inv_op = Inv (derives de complete inv. lemma)
 * inv_op = InvNoThining (derives de semi inversion lemma) *)

let inversion_lemma_from_goal n na id sort dep_option inv_op =
  let pts = get_pftreestate() in
  let pf = proof_of_pftreestate pts in
  let gll,_ = frontier pf in
  let gl = List.nth gll (n-1) in
  add_inversion_lemma na gl.hyps (snd(lookup_sign id gl.hyps)).body 
    sort dep_option inv_op

let inversion_clear = inv false (Some true) None
			
open Vernacinterp

let _ = 
  vinterp_add
    ("MakeInversionLemmaFromHyp",
     fun [VARG_NUMBER n;
	  VARG_IDENTIFIER na;
	  VARG_IDENTIFIER id] ->
       fun () ->
	 inversion_lemma_from_goal n na id mkProp 
	   false (inversion_clear false))

let no_inductive_inconstr ass constr =
  [< 'sTR "Cannot recognize an inductive predicate in "; term0 ass constr;
     'sTR "."; 'sPC; 'sTR "If there is one, may be the structure of the arity";
     'sPC; 'STR "or of the type of constructors"; 'sPC;
     'sTR "is hidden by constant definitions." >]

let add_inversion_lemma_exn na constr sort bool  tac =
  try
    (add_inversion_lemma na (initial_sign()) constr sort bool tac)
  with 
    | Induc -> 
	errorlabstrm "add_inversion_lemma" (no_inductive_inconstr 
					      (gLOB (initial_sign())) constr)
    |   UserError ("abstract_list_all",_) -> 
	  no_generalisation()
    |   UserError ("Case analysis",s) -> 
	  errorlabstrm "Inv needs Nodep Prop Set" s
    |   UserError ("mind_specif_of_mind",_)  -> 
          errorlabstrm "mind_specif_of_mind" 
            (no_inductive_inconstr (gLOB (initial_sign())) constr)

let _ = 
  vinterp_add
    ("MakeInversionLemma",
     fun [VARG_IDENTIFIER na;
	  VARG_COMMAND com;
	  VARG_COMMAND sort] ->
       fun () ->
	 add_inversion_lemma_exn na 
	   (constr_of_com Evd.empty (initial_sign()) com)
	   (constr_of_com Evd.empty (initial_sign()) sort)
	   false (inversion_clear false))

let _ = 
  vinterp_add
    ("MakeSemiInversionLemmaFromHyp",
     fun [VARG_NUMBER n;
	  VARG_IDENTIFIER na;
	  VARG_IDENTIFIER id] ->
       fun () ->
	 inversion_lemma_from_goal n na id mkProp false 
	   (inversion_clear false))

let _ = 
  vinterp_add
    ("MakeSemiInversionLemma",
     fun [VARG_IDENTIFIER na;
	  VARG_COMMAND com;
	  VARG_COMMAND sort] ->
       fun () ->
	 add_inversion_lemma_exn na 
	   (constr_of_com Evd.empty (initial_sign()) com)
	   (constr_of_com Evd.empty (initial_sign()) sort)
	   false (inv false (Some false) None false))

let _ = 
  vinterp_add
    ("MakeDependentInversionLemma",
     fun [VARG_IDENTIFIER na;
	  VARG_COMMAND com;
	  VARG_COMMAND sort] ->
       fun () ->
	 add_inversion_lemma_exn na 
	   (constr_of_com Evd.empty (initial_sign()) com)
	   (constr_of_com Evd.empty (initial_sign()) sort)
	   true (inversion_clear true))

let _ = 
  vinterp_add
    ("MakeDependentSemiInversionLemma",
     fun [VARG_IDENTIFIER na;
	  VARG_COMMAND com;
	  VARG_COMMAND sort] ->
       fun () ->
	 add_inversion_lemma_exn na
	   (constr_of_com Evd.empty (initial_sign()) com)
	   (constr_of_com Evd.empty (initial_sign()) sort)
	   true (inversion_clear true))

(* ================================= *)
(* Applying a given inversion lemma  *)
(* ================================= *)

let lemInv id c gls =
  try
    let (wc,kONT) = startWalk gls in
    let clause = mk_clenv_type_of wc c in
    let clause = clenv_constrain_with_bindings [(ABS (-1),VAR id)] clause in
    res_pf kONT clause gls
  with 
    | Not_found  ->  
	errorlabstrm "LemInv" (not_found_message [id])
    |  UserError (a,b) -> 
	 errorlabstrm "LemInv" 
	   [< 'sTR "Cannot refine current goal with the lemma "; 
	      term0 (gLOB (initial_sign())) c  >] 

let useInversionLemma =
  let gentac =
    hide_tactic "UseInversionLemma"
      (fun [IDENTIFIER id;COMMAND com] gls ->
         lemInv id (pf_constr_of_com gls com) gls)
      (*fun sigma gl (_,[IDENTIFIER id;COMMAND com]) ->
        [< 'sTR"UseInv" ; 'sPC ; print_id id ; 'sPC ; pr_com sigma gl com >]*)
  in 
  fun id com -> gentac [IDENTIFIER id;COMMAND com]

let lemInvIn id c ids gls =
  let intros_replace_ids gls =
    let nb_of_new_hyp  = nb_prod (pf_concl gls) - List.length ids in 
    if nb_of_new_hyp < 1  then 
      introsReplacing ids gls
    else 
      (tclTHEN (tclDO nb_of_new_hyp intro) (introsReplacing ids)) gls
  in 
  try 
    ((tclTHEN (tclTHEN (bring_hyps (List.map inSOME ids))
		 (lemInv id c))
        (intros_replace_ids)) gls)
  with Not_found -> errorlabstrm "LemInvIn" (not_found_message ids)
    |  UserError(a,b) -> errorlabstrm "LemInvIn" b  

let useInversionLemmaIn =
  let gentac = hide_tactic "UseInversionLemmaIn"
		 (fun ((IDENTIFIER id)::(COMMAND com)::hl) gls ->
		    lemInvIn id (pf_constr_of_com gls com)
                      (List.map (fun (IDENTIFIER id) -> id) hl) gls)
  in 
  fun id com hl ->
    gentac ((IDENTIFIER id)::(COMMAND com)
            ::(List.map (fun id -> (IDENTIFIER id)) hl))
