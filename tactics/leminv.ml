(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Pp
open Util
open Names
open Nameops
open Term
open Termops
open Sign
open Evd
open Printer
open Reductionops
open Declarations
open Inductiveops
open Environ
open Tacmach
open Proof_trees
open Proof_type
open Pfedit
open Evar_refiner
open Clenv
open Declare
open Wcclausenv
open Tacticals
open Tactics
open Inv
open Safe_typing

let not_work_message = "tactic fails to build the inversion lemma, may be because the predicate has arguments that depend on other arguments"

let no_inductive_inconstr env constr =
  [< 'sTR "Cannot recognize an inductive predicate in "; 
     prterm_env env constr;
     'sTR "."; 'sPC; 'sTR "If there is one, may be the structure of the arity";
     'sPC; 'sTR "or of the type of constructors"; 'sPC;
     'sTR "is hidden by constant definitions." >]

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
 
let thin_ids env (hyps,vars) =
  fst
    (List.fold_left
       (fun ((ids,globs) as sofar) (id,c,a) ->
          if List.mem id globs then
	    match c with
	      | None -> (id::ids,(global_vars env a)@globs)
	      | Some body ->
                  (id::ids,(global_vars env body)@(global_vars env a)@globs)
          else sofar)
       ([],vars) hyps)

(* returns the sub_signature of sign corresponding to those identifiers that
 * are not global. *)
(*
let get_local_sign sign =
  let lid = ids_of_sign sign in
  let globsign = Global.named_context() in
  let add_local id res_sign = 
    if not (mem_sign globsign id) then 
      add_sign (lookup_sign id sign) res_sign
    else 
      res_sign
  in 
  List.fold_right add_local lid nil_sign
*)
(* returs the identifier of lid that was the latest declared in sign.
 * (i.e. is the identifier id of lid such that 
 * sign_length (sign_prefix id sign) > sign_length (sign_prefix id' sign) >
 * for any id'<>id in lid).
 * it returns both the pair (id,(sign_prefix id sign)) *)
(*
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
*)
let rec add_prods_sign env sigma t =
  match kind_of_term (whd_betadeltaiota env sigma t) with
    | Prod (na,c1,b) ->
	let id = id_of_name_using_hdchar env t na in
	let b'= subst1 (mkVar id) b in
        add_prods_sign (push_named_decl (id,None,c1) env) sigma b'
    | LetIn (na,c1,t1,b) ->
	let id = id_of_name_using_hdchar env t na in
	let b'= subst1 (mkVar id) b in
        add_prods_sign (push_named_decl (id,Some c1,t1) env) sigma b'
    | _ -> (env,t)

(* [dep_option] indicates wether the inversion lemma is dependent or not.
   If it is dependent and I is of the form (x_bar:T_bar)(I t_bar) then
   the stated goal will be (x_bar:T_bar)(H:(I t_bar))(P t_bar H) 
   where P:(x_bar:T_bar)(H:(I x_bar))[sort].
   The generalisation of such a goal at the moment of the dependent case should
   be easy.

   If it is non dependent, then if [I]=(I t_bar) and (x_bar:T_bar) are the
   variables occurring in [I], then the stated goal will be:
    (x_bar:T_bar)(I t_bar)->(P x_bar) 
   where P: P:(x_bar:T_bar)[sort].
*)

let compute_first_inversion_scheme env sigma ind sort dep_option =
  let indf,realargs = dest_ind_type ind in
  let allvars = ids_of_context env in
  let p = next_ident_away (id_of_string "P") allvars in
  let pty,goal =
    if dep_option  then
      let pty = make_arity env true indf sort in
      let goal = 
	mkProd
	  (Anonymous, mkAppliedInd ind, applist(mkVar p,realargs@[mkRel 1]))
      in
      pty,goal
    else
      let i = mkAppliedInd ind in
      let ivars = global_vars env i in
      let revargs,ownsign =
	fold_named_context
	  (fun env (id,_,_ as d) (revargs,hyps) ->
             if List.mem id ivars then ((mkVar id)::revargs,add_named_decl d hyps)
	     else (revargs,hyps))
          env ([],[]) in
      let pty = it_mkNamedProd_or_LetIn (mkSort sort) ownsign in
      let goal = mkArrow i (applist(mkVar p, List.rev revargs)) in
      (pty,goal)
  in
  let npty = nf_betadeltaiota env sigma pty in
  let extenv = push_named_decl (p,None,npty) env in
  extenv, goal

(* [inversion_scheme sign I]

   Given a local signature, [sign], and an instance of an inductive
   relation, [I], inversion_scheme will prove the associated inversion
   scheme on sort [sort]. Depending on the value of [dep_option] it will
   build a dependent lemma or a non-dependent one *)

let inversion_scheme env sigma t sort dep_option inv_op =
  let (env,i) = add_prods_sign env sigma t in
  let ind =
    try find_rectype env sigma i
    with Induc ->
      errorlabstrm "inversion_scheme" (no_inductive_inconstr env i) 
  in
  let (invEnv,invGoal) =
    compute_first_inversion_scheme env sigma ind sort dep_option 
  in
  assert 
    (list_subset 
       (global_vars env invGoal) 
       (ids_of_named_context (named_context invEnv)));
  (*
    errorlabstrm "lemma_inversion"
    [< 'sTR"Computed inversion goal was not closed in initial signature" >];
  *)
  let invSign = named_context invEnv in
  let pfs = mk_pftreestate (mk_goal invSign invGoal) in
  let pfs = solve_pftreestate (tclTHEN intro (onLastHyp inv_op)) pfs in
  let (pfterm,meta_types) = extract_open_pftreestate pfs in
  let global_named_context = Global.named_context () in
  let ownSign =
    fold_named_context
      (fun env (id,_,_ as d) sign ->
         if mem_named_context id global_named_context then sign
	 else add_named_decl d sign)
      invEnv empty_named_context 
  in
  let (_,ownSign,mvb) =
    List.fold_left
      (fun (avoid,sign,mvb) (mv,mvty) ->
         let h = next_ident_away (id_of_string "H") avoid in
	 (h::avoid, add_named_decl (h,None,mvty) sign, (mv,mkVar h)::mvb))
      (ids_of_context invEnv, ownSign, [])
      meta_types 
  in
  let invProof = 
    it_mkNamedLambda_or_LetIn (local_strong (whd_meta mvb) pfterm) ownSign 
  in
  invProof

let add_inversion_lemma name env sigma t sort dep inv_op =
  let invProof = inversion_scheme env sigma t sort dep inv_op in
  let _ = 
    declare_constant name
    (ConstantEntry { const_entry_body = invProof;
                     const_entry_type = None;
                     const_entry_opaque = false }, 
     NeverDischarge)
  in ()

(* open Pfedit *)

(* inv_op = Inv (derives de complete inv. lemma)
 * inv_op = InvNoThining (derives de semi inversion lemma) *)

let inversion_lemma_from_goal n na id sort dep_option inv_op =
  let pts = get_pftreestate() in
  let gl = nth_goal_of_pftreestate n pts in
  let t = pf_get_hyp_typ gl id in
  let env = pf_env gl and sigma = project gl in
  let fv = global_vars env t in
(* Pourquoi ??? 
  let thin_ids = thin_ids (hyps,fv) in
  if not(list_subset thin_ids fv) then
    errorlabstrm "lemma_inversion"
      [< 'sTR"Cannot compute lemma inversion when there are" ; 'sPC ;
	 'sTR"free variables in the types of an inductive" ; 'sPC ;
	 'sTR"which are not free in its instance" >]; *)
  add_inversion_lemma na env sigma t sort dep_option inv_op
   
open Vernacinterp

let _ = 
  vinterp_add
    "MakeInversionLemmaFromHyp"
    (function
       | [VARG_NUMBER n; VARG_IDENTIFIER na; VARG_IDENTIFIER id] ->
	   fun () ->
	     inversion_lemma_from_goal n na id mk_Prop false inv_clear_tac
       | _ -> bad_vernac_args "MakeInversionLemmaFromHyp")

let add_inversion_lemma_exn na com comsort bool tac =
  let env = Global.env () and sigma = Evd.empty in
  let c = Astterm.interp_type sigma env com in
  let sort = Astterm.interp_sort comsort in
  try
    add_inversion_lemma na env sigma c sort bool tac
  with 
    |   UserError ("Case analysis",s) -> (* référence à Indrec *)
	  errorlabstrm "Inv needs Nodep Prop Set" s

let _ = 
  vinterp_add
    "MakeInversionLemma"
     (function
	| [VARG_IDENTIFIER na; VARG_CONSTR com; VARG_CONSTR sort] ->
	    fun () ->
	      add_inversion_lemma_exn na com sort false inv_clear_tac
       | _ -> bad_vernac_args "MakeInversionLemma")

let _ = 
  vinterp_add
    "MakeSemiInversionLemmaFromHyp"
    (function
       | [VARG_NUMBER n; VARG_IDENTIFIER na; VARG_IDENTIFIER id] ->
	   fun () ->
	     inversion_lemma_from_goal n na id mk_Prop false half_inv_tac
       | _ -> bad_vernac_args "MakeSemiInversionLemmaFromHyp")

let _ = 
  vinterp_add
    "MakeSemiInversionLemma"
    (function
       | [VARG_IDENTIFIER na; VARG_CONSTR com; VARG_CONSTR sort] ->
	   fun () ->
	     add_inversion_lemma_exn na com sort false half_inv_tac
       | _ -> bad_vernac_args "MakeSemiInversionLemma")

let _ = 
  vinterp_add
    "MakeDependentInversionLemma"
    (function
       | [VARG_IDENTIFIER na; VARG_CONSTR com; VARG_CONSTR sort] ->
	   fun () ->
	     add_inversion_lemma_exn na com sort true dinv_clear_tac
       | _ -> bad_vernac_args "MakeDependentInversionLemma")

let _ = 
  vinterp_add
    "MakeDependentSemiInversionLemma"
    (function
       | [VARG_IDENTIFIER na; VARG_CONSTR com; VARG_CONSTR sort] ->
	   fun () ->
	     add_inversion_lemma_exn na com sort true half_dinv_tac
       | _ -> bad_vernac_args "MakeDependentSemiInversionLemma")

(* ================================= *)
(* Applying a given inversion lemma  *)
(* ================================= *)

let lemInv id c gls =
  try
    let (wc,kONT) = startWalk gls in
    let clause = mk_clenv_type_of wc c in
    let clause = clenv_constrain_with_bindings [(Abs (-1),mkVar id)] clause in
    res_pf kONT clause gls
  with 
(* Ce n'est pas l'endroit pour cela
    | Not_found  ->  
	errorlabstrm "LemInv" (not_found_message [id])
 *)
    |  UserError (a,b) -> 
	 errorlabstrm "LemInv" 
	   [< 'sTR "Cannot refine current goal with the lemma "; 
	      prterm_env (Global.env()) c  >] 

let useInversionLemma =
  let gentac =
    hide_tactic "UseInversionLemma"
      (function
	 | [id_or_num; Command com] ->
	     tactic_try_intros_until
               (fun id gls -> lemInv id (pf_interp_constr gls com) gls)
	       id_or_num
	 | [id_or_num; Constr c] ->
	     tactic_try_intros_until
               (fun id gls -> lemInv id c gls)
	       id_or_num
	 | l  -> bad_vernac_args "useInversionLemma" l)
  in 
  fun id c -> gentac [Identifier id;Constr c]

let lemInvIn id c ids gls =
  let intros_replace_ids gls =
    let nb_of_new_hyp  = nb_prod (pf_concl gls) - List.length ids in 
    if nb_of_new_hyp < 1  then 
      intros_replacing ids gls
    else 
      (tclTHEN (tclDO nb_of_new_hyp intro) (intros_replacing ids)) gls
  in 
(*  try *)
    ((tclTHEN (tclTHEN (bring_hyps ids) (lemInv id c))
        (intros_replace_ids)) gls)
(*  with Not_found -> errorlabstrm "LemInvIn" (not_found_message ids)
    |  UserError(a,b) -> errorlabstrm "LemInvIn" b  
*)

let useInversionLemmaIn =
  let gentac =
    hide_tactic "UseInversionLemmaIn"
      (function
	 | ((Identifier id)::(Command com)::hl as ll) ->
	     fun gls ->
	       lemInvIn id (pf_interp_constr gls com)
                 (List.map
		    (function
		       | (Identifier id) -> id
		       | _ -> bad_vernac_args "UseInversionLemmaIn" ll) hl) gls
	 | ((Identifier id)::(Constr c)::hl as ll) ->
	     fun gls ->
	       lemInvIn id c
                 (List.map
		    (function
		       | (Identifier id) -> id
		       | _ -> bad_vernac_args "UseInversionLemmaIn" ll) hl) gls
	 | ll -> bad_vernac_args "UseInversionLemmaIn" ll)
  in 
  fun id c hl ->
    gentac ((Identifier id)::(Constr c)
            ::(List.map (fun id -> (Identifier id)) hl))
