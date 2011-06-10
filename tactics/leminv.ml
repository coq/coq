(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Util
open Names
open Nameops
open Term
open Termops
open Namegen
open Sign
open Evd
open Printer
open Reductionops
open Declarations
open Entries
open Inductiveops
open Environ
open Tacmach
open Proof_type
open Pfedit
open Evar_refiner
open Clenv
open Declare
open Tacticals
open Tactics
open Inv
open Vernacexpr
open Safe_typing
open Decl_kinds

let no_inductive_inconstr env constr =
  (str "Cannot recognize an inductive predicate in " ++
     pr_lconstr_env env constr ++
     str "." ++ spc () ++ str "If there is one, may be the structure of the arity" ++
     spc () ++ str "or of the type of constructors" ++ spc () ++
     str "is hidden by constant definitions.")

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
        add_prods_sign (push_named (id,None,c1) env) sigma b'
    | LetIn (na,c1,t1,b) ->
	let id = id_of_name_using_hdchar env t na in
	let b'= subst1 (mkVar id) b in
        add_prods_sign (push_named (id,Some c1,t1) env) sigma b'
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
             if List.mem id ivars then
	       ((mkVar id)::revargs,add_named_decl d hyps)
	     else
	       (revargs,hyps))
          env ~init:([],[])
      in
      let pty = it_mkNamedProd_or_LetIn (mkSort sort) ownsign in
      let goal = mkArrow i (applist(mkVar p, List.rev revargs)) in
      (pty,goal)
  in
  let npty = nf_betadeltaiota env sigma pty in
  let extenv = push_named (p,None,npty) env in
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
    with Not_found ->
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
    (str"Computed inversion goal was not closed in initial signature.");
  *)
  let pf = Proof.start [invEnv,invGoal] in
  Proof.run_tactic env (Proofview.V82.tactic (tclTHEN intro (onLastHypId inv_op))) pf;
  let pfterm = List.hd (Proof.partial_proof pf) in
  let global_named_context = Global.named_context () in
  let ownSign = ref begin
    fold_named_context
      (fun env (id,_,_ as d) sign ->
         if mem_named_context id global_named_context then sign
	 else add_named_decl d sign)
      invEnv ~init:empty_named_context
  end in
  let avoid = ref [] in
  let { sigma=sigma } = Proof.V82.subgoals pf in
  let rec fill_holes c =
    match kind_of_term c with
    | Evar (e,args) ->
	let h = next_ident_away (id_of_string "H") !avoid in
	let ty,inst = Evarutil.generalize_evar_over_rels sigma (e,args) in
	avoid := h::!avoid;
	ownSign := add_named_decl (h,None,ty) !ownSign;
	applist (mkVar h, inst)
    | _ -> map_constr fill_holes c
  in
  let c = fill_holes pfterm in
  (* warning: side-effect on ownSign *)
  let invProof = it_mkNamedLambda_or_LetIn c !ownSign
  in
  invProof

let add_inversion_lemma name env sigma t sort dep inv_op =
  let invProof = inversion_scheme env sigma t sort dep inv_op in
  let _ =
    declare_constant name
    (DefinitionEntry
       { const_entry_body = invProof;
         const_entry_type = None;
         const_entry_opaque = false },
     IsProof Lemma)
  in ()

(* inv_op = Inv (derives de complete inv. lemma)
 * inv_op = InvNoThining (derives de semi inversion lemma) *)

let inversion_lemma_from_goal n na (loc,id) sort dep_option inv_op =
  let pts = get_pftreestate() in
  let { it=gls ; sigma=sigma } = Proof.V82.subgoals pts in
  let gl = { it = List.nth gls (n-1) ; sigma=sigma } in
  let t =
    try pf_get_hyp_typ gl id
    with Not_found -> Pretype_errors.error_var_not_found_loc loc id in
  let env = pf_env gl and sigma = project gl in
  add_inversion_lemma na env sigma t sort dep_option inv_op

let add_inversion_lemma_exn na com comsort bool tac =
  let env = Global.env () and sigma = Evd.empty in
  let c = Constrintern.interp_type sigma env com in
  let sort = Pretyping.interp_sort comsort in
  try
    add_inversion_lemma na env sigma c sort bool tac
  with
    |   UserError ("Case analysis",s) -> (* référence à Indrec *)
	  errorlabstrm "Inv needs Nodep Prop Set" s

(* ================================= *)
(* Applying a given inversion lemma  *)
(* ================================= *)

let lemInv id c gls =
  try
    let clause = mk_clenv_type_of gls c in
    let clause = clenv_constrain_last_binding (mkVar id) clause in
    Clenvtac.res_pf clause ~flags:Unification.elim_flags gls
  with
    | NoSuchBinding ->
	errorlabstrm ""
	  (hov 0 (pr_constr c ++ spc () ++ str "does not refer to an inversion lemma."))
    | UserError (a,b) ->
	 errorlabstrm "LemInv"
	   (str "Cannot refine current goal with the lemma " ++
	      pr_lconstr_env (Global.env()) c)

let lemInv_gen id c = try_intros_until (fun id -> lemInv id c) id

let lemInvIn id c ids gls =
  let hyps = List.map (pf_get_hyp gls) ids in
  let intros_replace_ids gls =
    let nb_of_new_hyp  = nb_prod (pf_concl gls) - List.length ids in
    if nb_of_new_hyp < 1  then
      intros_replacing ids gls
    else
      (tclTHEN (tclDO nb_of_new_hyp intro) (intros_replacing ids)) gls
  in
  ((tclTHEN (tclTHEN (bring_hyps hyps) (lemInv id c))
    (intros_replace_ids)) gls)

let lemInvIn_gen id c l = try_intros_until (fun id -> lemInvIn id c l) id

let lemInv_clause id c = function
  | [] -> lemInv_gen id c
  | l -> lemInvIn_gen id c l
