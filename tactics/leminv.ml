(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pp
open CErrors
open Util
open Names
open Termops
open Environ
open Constr
open EConstr
open Vars
open Namegen
open Evd
open Printer
open Reductionops
open Entries
open Inductiveops
open Tacmach.New
open Clenv
open Declare
open Tacticals.New
open Tactics
open Decl_kinds
open Context.Named.Declaration

module NamedDecl = Context.Named.Declaration

let no_inductive_inconstr env sigma constr =
  (str "Cannot recognize an inductive predicate in " ++
     pr_leconstr_env env sigma constr ++
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
  match EConstr.kind sigma (whd_all env sigma t) with
    | Prod (na,c1,b) ->
	let id = id_of_name_using_hdchar env sigma t na in
	let b'= subst1 (mkVar id) b in
        add_prods_sign (push_named (LocalAssum (id,c1)) env) sigma b'
    | LetIn (na,c1,t1,b) ->
	let id = id_of_name_using_hdchar env sigma t na in
	let b'= subst1 (mkVar id) b in
        add_prods_sign (push_named (LocalDef (id,c1,t1)) env) sigma b'
    | _ -> (env,t)

(* [dep_option] indicates whether the inversion lemma is dependent or not.
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
  let allvars = vars_of_env env in
  let p = next_ident_away (Id.of_string "P") allvars in
  let pty,goal =
    if dep_option  then
      let pty = make_arity env sigma true indf sort in
      let goal =
	mkProd
	  (Anonymous, mkAppliedInd ind, applist(mkVar p,realargs@[mkRel 1]))
      in
      pty,goal
    else
      let i = mkAppliedInd ind in
      let ivars = global_vars env sigma i in
      let revargs,ownsign =
	fold_named_context
	  (fun env d (revargs,hyps) ->
            let d = map_named_decl EConstr.of_constr d in
             let id = NamedDecl.get_id d in
             if Id.List.mem id ivars then
	       ((mkVar id)::revargs, Context.Named.add d hyps)
	     else
	       (revargs,hyps))
          env ~init:([],[])
      in
      let pty = it_mkNamedProd_or_LetIn (mkSort sort) ownsign in
      let goal = mkArrow i (applist(mkVar p, List.rev revargs)) in
      (pty,goal)
  in
  let npty = nf_all env sigma pty in
  let extenv = push_named (LocalAssum (p,npty)) env in
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
      user_err ~hdr:"inversion_scheme" (no_inductive_inconstr env sigma i)
  in
  let (invEnv,invGoal) =
    compute_first_inversion_scheme env sigma ind sort dep_option
  in
  assert
    (List.subset
       (global_vars env sigma invGoal)
       (ids_of_named_context (named_context invEnv)));
  (*
    user_err ~hdr:"lemma_inversion"
    (str"Computed inversion goal was not closed in initial signature.");
  *)
  let pf = Proof.start (Evd.from_ctx (evar_universe_context sigma)) [invEnv,invGoal] in
  let pf =
    fst (Proof.run_tactic env (
      tclTHEN intro (onLastHypId inv_op)) pf)
  in
  let pfterm = List.hd (Proof.partial_proof pf) in
  let global_named_context = Global.named_context_val () in
  let ownSign = ref begin
    fold_named_context
      (fun env d sign ->
        let d = map_named_decl EConstr.of_constr d in
         if mem_named_context_val (NamedDecl.get_id d) global_named_context then sign
	 else Context.Named.add d sign)
      invEnv ~init:Context.Named.empty
  end in
  let avoid = ref Id.Set.empty in
  let _,_,_,_,sigma = Proof.proof pf in
  let sigma = Evd.minimize_universes sigma in
  let rec fill_holes c =
    match EConstr.kind sigma c with
    | Evar (e,args) ->
	let h = next_ident_away (Id.of_string "H") !avoid in
	let ty,inst = Evarutil.generalize_evar_over_rels sigma (e,args) in
	avoid := Id.Set.add h !avoid;
	ownSign := Context.Named.add (LocalAssum (h,ty)) !ownSign;
	applist (mkVar h, inst)
    | _ -> EConstr.map sigma fill_holes c
  in
  let c = fill_holes pfterm in
  (* warning: side-effect on ownSign *)
  let invProof = it_mkNamedLambda_or_LetIn c !ownSign in
  let p = EConstr.to_constr sigma invProof in
  p, sigma

let add_inversion_lemma ~poly name env sigma t sort dep inv_op =
  let invProof, sigma = inversion_scheme env sigma t sort dep inv_op in
  let univs =
    Evd.const_univ_entry ~poly sigma
  in
  let entry = definition_entry ~univs invProof in
  let _ = declare_constant name (DefinitionEntry entry, IsProof Lemma) in
  ()

(* inv_op = Inv (derives de complete inv. lemma)
 * inv_op = InvNoThining (derives de semi inversion lemma) *)

let add_inversion_lemma_exn ~poly na com comsort bool tac =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let sigma, c = Constrintern.interp_type_evars env sigma com in
  let sigma, sort = Evd.fresh_sort_in_family ~rigid:univ_rigid sigma comsort in
  try
    add_inversion_lemma ~poly na env sigma c sort bool tac
  with
    |   UserError (Some "Case analysis",s) -> (* Reference to Indrec *)
	  user_err ~hdr:"Inv needs Nodep Prop Set" s

(* ================================= *)
(* Applying a given inversion lemma  *)
(* ================================= *)

let lemInv id c =
  Proofview.Goal.enter begin fun gls ->
  try
    let clause = mk_clenv_from_env (pf_env gls) (project gls) None (c, pf_unsafe_type_of gls c) in
    let clause = clenv_constrain_last_binding (EConstr.mkVar id) clause in
    Clenvtac.res_pf clause ~flags:(Unification.elim_flags ()) ~with_evars:false
  with
    | NoSuchBinding ->
	user_err 
	  (hov 0 (pr_econstr_env (pf_env gls) (project gls) c ++ spc () ++ str "does not refer to an inversion lemma."))
    | UserError (a,b) ->
	 user_err ~hdr:"LemInv"
	   (str "Cannot refine current goal with the lemma " ++
	      pr_leconstr_env (pf_env gls) (project gls) c)
  end

let lemInv_gen id c = try_intros_until (fun id -> lemInv id c) id

let lemInvIn id c ids =
  Proofview.Goal.enter begin fun gl ->
    let hyps = List.map (fun id -> pf_get_hyp id gl) ids in
    let intros_replace_ids =
      let concl = Proofview.Goal.concl gl in
      let sigma = project gl in
      let nb_of_new_hyp = nb_prod sigma concl - List.length ids in
      if nb_of_new_hyp < 1  then
        intros_replacing ids
      else
        (tclTHEN (tclDO nb_of_new_hyp intro) (intros_replacing ids))
    in
    ((tclTHEN (tclTHEN (bring_hyps hyps) (lemInv id c))
        (intros_replace_ids)))
  end

let lemInvIn_gen id c l = try_intros_until (fun id -> lemInvIn id c l) id

let lemInv_clause id c = function
  | [] -> lemInv_gen id c
  | l -> lemInvIn_gen id c l
