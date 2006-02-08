open Util
open Names
open Term
open Tacinvutils
open Pp
open Indfun_common
open Libnames
open Tacticals
open Tactics
open Tacmach
open Sign


let tac_pattern l =
  (Hiddentac.h_reduce 
    (Rawterm.Pattern l)
    Tacticals.onConcl
  )


let rec nb_prod x =
  let rec count n c =
    match kind_of_term c with
        Prod(_,_,t) -> count (n+1) t
      | LetIn(_,a,_,t) -> count n (subst1 a t)
      | Cast(c,_,_) -> count n c
      | _ -> n
  in count 0 x

let intro_discr_until n tac : tactic = 
  let rec intro_discr_until acc : tactic =
  fun g -> 
    if nb_prod (pf_concl g) <= n then tac (List.rev acc) g
    else 
      tclTHEN 
	intro 
	(fun g' ->
	  let id,_,t = pf_last_hyp g' in
	  tclORELSE
	     (tclABSTRACT None (Extratactics.h_discrHyp (Rawterm.NamedHyp id)))
	    (intro_discr_until ((id,t)::acc))
	    g'
	) 
	g
  in
  intro_discr_until []


let rec discr_rew_in_H hypname idl : tactic =
  match idl with 
    | [] -> (Extratactics.h_discrHyp (Rawterm.NamedHyp hypname))
    | ((id,t)::idl') ->
       match kind_of_term t with 
	 | App(eq',[| _ ; arg1 ; _ |]) when eq_constr eq' (Lazy.force eq) -> 
	     begin 
	       let constr,_ = decompose_app arg1 in 
	       if isConstruct constr 
	       then 
		 (discr_rew_in_H hypname idl')
	       else 
		 tclTHEN 
		   (tclTRY (Equality.general_rewrite_in true hypname (mkVar id)))
		   (discr_rew_in_H hypname idl')
	     end
	 | _ -> discr_rew_in_H hypname idl'

let finalize fname hypname idl : tactic = 
  tclTRY (
    (tclTHEN 
      (Hiddentac.h_reduce
	(Rawterm.Unfold [[],EvalConstRef fname])
	(Tacticals.onHyp hypname)
      )
      (discr_rew_in_H hypname idl)
    ))

let gen_fargs fargs : tactic = 
  fun g -> 
    generalize
      (List.map
	 (fun arg -> 
	    let targ = pf_type_of g arg in
	    let refl_arg = mkApp (Lazy.force refl_equal , [|targ ; arg|]) in
	    refl_arg
	 )
	 (Array.to_list fargs)
      ) 
      g 
      

let invfun (hypname:identifier) (fid:identifier) : tactic=
  fun g -> 
    let nprod_goal = nb_prod (pf_concl g) in
    let f_ind_id =  
      (
	Indrec.make_elimination_ident
	  fid 
	  (Tacticals.elimination_sort_of_goal g)
      )
    in
    let fname = const_of_id fid in
    let princ = const_of_id f_ind_id in
    let princ_info = 
      let princ_type = 
	(try (match (Global.lookup_constant princ) with
		  {Declarations.const_type=t} -> t
	     )
	 with _ -> assert false)
      in
      compute_elim_sig princ_type
    in
    let _,_,typhyp = List.find (fun (id,_,_) -> hypname=id) (pf_hyps g) in
    let do_invert  fargs  appf : tactic = 
      let frealargs = (snd (array_chop (List.length princ_info.params) fargs))  
      in
      let pat_args = 
	(List.map (fun e -> ([-1],e)) (Array.to_list frealargs)) @ [[],appf] 
      in
      tclTHENSEQ 
	[
	  gen_fargs frealargs;
	  tac_pattern pat_args;
	  Hiddentac.h_apply (mkConst princ,Rawterm.NoBindings);
	  intro_discr_until nprod_goal (finalize fname hypname) 
	    
	]
    in
    match kind_of_term typhyp with
      | App(eq',[| _ ; arg1 ; arg2 |]) when eq_constr eq' (Lazy.force eq) -> 
(* 	  let valf = def_of_const (mkConst fname) in *)
	  let eq_arg1 , eq_arg2 , good_eq_form , fargs = 
	    match kind_of_term arg1 , kind_of_term arg2 with
	      | App(f, args),_ when eq_constr f (mkConst fname) -> 
		  arg1 , arg2 , tclIDTAC , args
	      | _,App(f, args) when eq_constr f (mkConst fname) -> 
		  arg2 , arg1 , symmetry_in hypname , args
	      | _ , _  -> error "inversion impossible" 
	  in
	  tclTHEN
	    good_eq_form
	    (do_invert fargs eq_arg1)
	    g
      | App(f',fargs) when eq_constr f' (mkConst fname) -> 
	  do_invert fargs typhyp g
	  

      | _ -> error "inversion impossible"

