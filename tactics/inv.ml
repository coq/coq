(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Errors
open Util
open Names
open Nameops
open Term
open Vars
open Context
open Termops
open Namegen
open Environ
open Inductiveops
open Printer
open Retyping
open Tacmach.New
open Tacticals.New
open Tactics
open Elim
open Equality
open Misctypes
open Tacexpr
open Proofview.Notations

let clear hyps = Proofview.V82.tactic (clear hyps)

let var_occurs_in_pf gl id =
  let env = Proofview.Goal.env gl in
  occur_var env id (Proofview.Goal.concl gl) ||
  List.exists (occur_var_in_decl env id) (Proofview.Goal.hyps gl)

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

type inversion_status = Dep of constr option | NoDep

let compute_eqn env sigma n i ai =
  (mkRel (n-i),get_type_of env sigma (mkRel (n-i)))

let make_inv_predicate env evd indf realargs id status concl =
  let nrealargs = List.length realargs in
  let (hyps,concl) =
    match status with
      | NoDep ->
	  (* We push the arity and leave concl unchanged *)
	  let hyps_arity,_ = get_arity env indf in
	    (hyps_arity,concl)
      | Dep dflt_concl ->
	  if not (occur_var env id concl) then
	    errorlabstrm "make_inv_predicate"
              (str "Current goal does not depend on " ++ pr_id id ++ str".");
          (* We abstract the conclusion of goal with respect to
             realargs and c to * be concl in order to rewrite and have
             c also rewritten when the case * will be done *)
	  let pred =
            match dflt_concl with
              | Some concl -> concl (*assumed it's some [x1..xn,H:I(x1..xn)]C*)
              | None ->
		let sort = get_sort_family_of env !evd concl in
		let sort = Evarutil.evd_comb1 (Evd.fresh_sort_in_family env) evd sort in
		let p = make_arity env true indf sort in
		let evd',(p,ptyp) = Unification.abstract_list_all env
                  !evd p concl (realargs@[mkVar id])
		in evd := evd'; p in
	  let hyps,bodypred = decompose_lam_n_assum (nrealargs+1) pred in
	  (* We lift to make room for the equations *)
	  (hyps,lift nrealargs bodypred)
  in
  let nhyps = rel_context_length hyps in
  let env' = push_rel_context hyps env in
  (* Now the arity is pushed, and we need to construct the pairs
   * ai,mkRel(n-i+1) *)
  (* Now, we can recurse down this list, for each ai,(mkRel k) whether to
     push <Ai>(mkRel k)=ai (when   Ai is closed).
   In any case, we carry along the rest of pairs *)
  let eqdata = Coqlib.build_coq_eq_data () in
  let rec build_concl eqns args n = function
    | [] -> it_mkProd concl eqns, Array.rev_of_list args
    | ai :: restlist ->
        let ai = lift nhyps ai in
        let (xi, ti) = compute_eqn env' !evd nhyps n ai in
        let (lhs,eqnty,rhs) =
          if closed0 ti then
	    (xi,ti,ai)
          else
	    let sigma, res = make_iterated_tuple env' !evd ai (xi,ti) in
	      evd := sigma; res
	in
        let eq_term = eqdata.Coqlib.eq in
	let eq = Evarutil.evd_comb1 (Evd.fresh_global env) evd eq_term in
        let eqn = applist (eq,[eqnty;lhs;rhs]) in
        let eqns = (Anonymous, lift n eqn) :: eqns in
        let refl_term = eqdata.Coqlib.refl in
	let refl_term = Evarutil.evd_comb1 (Evd.fresh_global env) evd refl_term in
        let refl = mkApp (refl_term, [|eqnty; rhs|]) in
	let _ = Evarutil.evd_comb1 (Typing.e_type_of env) evd refl in
        let args = refl :: args in
        build_concl eqns args (succ n) restlist
  in
  let (newconcl, args) = build_concl [] [] 0 realargs in
  let predicate = it_mkLambda_or_LetIn_name env newconcl hyps in
  let _ = Evarutil.evd_comb1 (Typing.e_type_of env) evd predicate in
  (* OK - this predicate should now be usable by res_elimination_then to
     do elimination on the conclusion. *)
  predicate, args

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

(* Computes the subset of hypothesis in the local context whose
   type depends on t (should be of the form (mkVar id)), then
   it generalizes them, applies tac to rewrite all occurrencies of t,
   and introduces generalized hypotheis.
   Precondition: t=(mkVar id) *)

let dependent_hyps env id idlist gl =
  let rec dep_rec =function
    | [] -> []
    | (id1,_,_)::l ->
	(* Update the type of id1: it may have been subject to rewriting *)
	let d = pf_get_hyp id1 gl in
	if occur_var_in_decl env id d
        then d :: dep_rec l
        else dep_rec l
  in
  dep_rec idlist

let split_dep_and_nodep hyps gl =
  List.fold_right
    (fun (id,_,_ as d) (l1,l2) ->
       if var_occurs_in_pf gl id then (d::l1,l2) else (l1,d::l2))
    hyps ([],[])

(* Computation of dids is late; must have been done in rewrite_equations*)
(* Will keep generalizing and introducing back and forth... *)
(* Moreover, others hyps depending of dids should have been *)
(* generalized; in such a way that [dids] can endly be cleared *)
(* Consider for instance this case extracted from Well_Ordering.v

  A : Set
  B : A ->Set
  a0 : A
  f : (B a0) ->WO
  y : WO
  H0 : (le_WO y (sup a0 f))
  ============================
   (Acc WO le_WO y)

  Inversion H0 gives

  A : Set
  B : A ->Set
  a0 : A
  f : (B a0) ->WO
  y : WO
  H0 : (le_WO y (sup a0 f))
  a1 : A
  f0 : (B a1) ->WO
  v : (B a1)
  H1 : (f0 v)=y
  H3 : a1=a0
  f1 : (B a0) ->WO
  v0 : (B a0)
  H4 : (existS A [a:A](B a) ->WO a0 f1)=(existS A [a:A](B a) ->WO a0 f)
  ============================
   (Acc WO le_WO (f1 v0))

while, ideally, we would have expected

  A : Set
  B : A ->Set
  a0 : A
  f0 : (B a0)->WO
  v : (B a0)
  ============================
   (Acc WO le_WO (f0 v))

obtained from destruction with equalities

  A : Set
  B : A ->Set
  a0 : A
  f : (B a0) ->WO
  y : WO
  H0 : (le_WO y (sup a0 f))
  a1 : A
  f0 : (B a1)->WO
  v : (B a1)
  H1 : (f0 v)=y
  H2 : (sup a1 f0)=(sup a0 f)
  ============================
   (Acc WO le_WO (f0 v))

by clearing initial hypothesis H0 and its dependency y, clearing H1
(in fact H1 can be avoided using the same trick as for newdestruct),
decomposing H2 to get a1=a0 and (a1,f0)=(a0,f), replacing a1 by a0
everywhere and removing a1 and a1=a0 (in fact it would have been more
regular to replace a0 by a1, avoiding f1 and v0 cannot replace f0 and v),
finally removing H4 (here because f is not used, more generally after using
eq_dep and replacing f by f0) [and finally rename a0, f0 into a,f].
Summary: nine useless hypotheses!
Nota: with Inversion_clear, only four useless hypotheses
*)

let generalizeRewriteIntros as_mode tac depids id =
  Proofview.tclENV >>= fun env ->
  Proofview.Goal.nf_enter begin fun gl ->
  let dids = dependent_hyps env id depids gl in
  let reintros = if as_mode then intros_replacing else intros_possibly_replacing in
  (tclTHENLIST
    [bring_hyps dids; tac;
     (* may actually fail to replace if dependent in a previous eq *)
     reintros (ids_of_named_context dids)])
  end

let error_too_many_names pats =
  let loc = Loc.join_loc (fst (List.hd pats)) (fst (List.last pats)) in
  Proofview.tclENV >>= fun env ->
  tclZEROMSG ~loc (
    str "Unexpected " ++
    str (String.plural (List.length pats) "introduction pattern") ++
    str ": " ++ pr_enum (Miscprint.pr_intro_pattern (fun c -> Printer.pr_constr (snd (c env Evd.empty)))) pats ++
    str ".")

let rec get_names (allow_conj,issimple) (loc,pat as x) = match pat with
  | IntroNaming IntroAnonymous | IntroForthcoming _ ->
      error "Anonymous pattern not allowed for inversion equations."
  | IntroNaming (IntroFresh _) ->
      error "Fresh pattern not allowed for inversion equations."
  | IntroAction IntroWildcard ->
      error "Discarding pattern not allowed for inversion equations."
  | IntroAction (IntroRewrite _) ->
      error "Rewriting pattern not allowed for inversion equations."
  | IntroAction (IntroOrAndPattern [[]]) when allow_conj -> (None, [])
  | IntroAction (IntroOrAndPattern [(_,IntroNaming (IntroIdentifier id)) :: _ as l])
      when allow_conj -> (Some id,l)
  | IntroAction (IntroOrAndPattern [_]) ->
      if issimple then
        error"Conjunctive patterns not allowed for simple inversion equations."
      else
        error"Nested conjunctive patterns not allowed for inversion equations."
  | IntroAction (IntroInjection l) ->
      error "Injection patterns not allowed for inversion equations."
  | IntroAction (IntroOrAndPattern l) ->
      error "Disjunctive patterns not allowed for inversion equations."
  | IntroAction (IntroApplyOn (c,pat)) ->
      error "Apply patterns not allowed for inversion equations."
  | IntroNaming (IntroIdentifier id) ->
      (Some id,[x])

let rec tclMAP_i allow_conj n tacfun = function
  | [] -> tclDO n (tacfun (None,[]))
  | a::l as l' ->
      if Int.equal n 0 then error_too_many_names l'
      else
        tclTHEN
          (tacfun (get_names allow_conj a))
          (tclMAP_i allow_conj (n-1) tacfun l)

let remember_first_eq id x = if !x == MoveLast then x := MoveAfter id

(* invariant: ProjectAndApply is responsible for erasing the clause
   which it is given as input
   It simplifies the clause (an equality) to use it as a rewrite rule and then
   erases the result of the simplification. *)
(* invariant: ProjectAndApplyNoThining simplifies the clause (an equality) .
   If it can discriminate then the goal is proved, if not tries to use it as
   a rewrite rule. It erases the clause which is given as input *)

let projectAndApply as_mode thin avoid id eqname names depids =
  let subst_hyp l2r id =
    tclTHEN (tclTRY(rewriteInConcl l2r (mkVar id)))
      (if thin then clear [id] else (remember_first_eq id eqname; tclIDTAC))
  in
  let substHypIfVariable tac id =
    Proofview.Goal.nf_enter begin fun gl ->
    (** We only look at the type of hypothesis "id" *)
    let hyp = pf_nf_evar gl (pf_get_hyp_typ id (Proofview.Goal.assume gl)) in
    let (t,t1,t2) = Hipattern.dest_nf_eq gl hyp in
    match (kind_of_term t1, kind_of_term t2) with
    | Var id1, _ -> generalizeRewriteIntros as_mode (subst_hyp true id) depids id1
    | _, Var id2 -> generalizeRewriteIntros as_mode (subst_hyp false id) depids id2
    | _ -> tac id
    end
  in
  let deq_trailer id clear_flag _ neqns =
    assert (clear_flag == None);
    tclTHENLIST
      [if as_mode then clear [id] else tclIDTAC;
       (tclMAP_i (false,false) neqns (function (idopt,_) ->
	 tclTRY (tclTHEN
	   (intro_move_avoid idopt avoid MoveLast)
	   (* try again to substitute and if still not a variable after *)
	   (* decomposition, arbitrarily try to rewrite RL !? *)
	   (tclTRY (onLastHypId (substHypIfVariable (fun id -> subst_hyp false id))))))
	 names);
       (if as_mode then tclIDTAC else clear [id])]
          (* Doing the above late breaks the computation of dids in 
             generalizeRewriteIntros, and hence breaks proper intros_replacing
             but it is needed for compatibility *)
  in
  substHypIfVariable
    (* If no immediate variable in the equation, try to decompose it *)
    (* and apply a trailer which again try to substitute *)
    (fun id ->
      dEqThen false (deq_trailer id)
	(Some (None,ElimOnConstr (mkVar id,NoBindings))))
    id

let nLastDecls i tac =
  Proofview.Goal.nf_enter (fun gl -> tac (nLastDecls gl i))

(* Introduction of the equations on arguments
   othin: discriminates Simple Inversion, Inversion and Inversion_clear
     None: the equations are introduced, but not rewritten
     Some thin: the equations are rewritten, and cleared if thin is true *)

let rewrite_equations as_mode othin neqns names ba =
  Proofview.Goal.nf_enter begin fun gl ->
  let (depids,nodepids) = split_dep_and_nodep ba.Tacticals.assums gl in
  let first_eq = ref MoveLast in
  let avoid = if as_mode then List.map pi1 nodepids else [] in
  match othin with
    | Some thin ->
        tclTHENLIST
            [tclDO neqns intro;
             bring_hyps nodepids;
             clear (ids_of_named_context nodepids);
             (nLastDecls neqns (fun ctx -> bring_hyps (List.rev ctx)));
             (nLastDecls neqns (fun ctx -> clear (ids_of_named_context ctx)));
	     tclMAP_i (true,false) neqns (fun (idopt,names) ->
               (tclTHEN
		 (intro_move_avoid idopt avoid MoveLast)
		 (onLastHypId (fun id ->
		   tclTRY (projectAndApply as_mode thin avoid id first_eq names depids)))))
	       names;
	     tclMAP (fun (id,_,_) -> tclIDTAC >>= fun () -> (* delay for [first_eq]. *)
               let idopt = if as_mode then Some id else None in
	       intro_move idopt (if thin then MoveLast else !first_eq))
	       nodepids;
	     (tclMAP (fun (id,_,_) -> tclTRY (clear [id])) depids)]
    | None ->
        (* simple inversion *)
        if as_mode then
          tclMAP_i (false,true) neqns (fun (idopt,_) ->
	    intro_move idopt MoveLast) names
        else
          (tclTHENLIST
             [tclDO neqns intro;
              bring_hyps nodepids;
              clear (ids_of_named_context nodepids)])
  end

let interp_inversion_kind = function
  | SimpleInversion -> None
  | FullInversion -> Some false
  | FullInversionClear -> Some true

let rewrite_equations_tac as_mode othin id neqns names ba =
  let othin = interp_inversion_kind othin in
  let tac = rewrite_equations as_mode othin neqns names ba in
  match othin with
  | Some true (* if Inversion_clear, clear the hypothesis *) ->
    tclTHEN tac (tclTRY (clear [id]))
  | _ ->
    tac

let raw_inversion inv_kind id status names =
  Proofview.Goal.nf_enter begin fun gl ->
    let sigma = Proofview.Goal.sigma gl in
    let env = Proofview.Goal.env gl in
    let concl = Proofview.Goal.concl gl in
    let c = mkVar id in
    let (ind, t) =
      try pf_apply Tacred.reduce_to_atomic_ind gl (pf_type_of gl c)
      with UserError _ ->
        let msg = str "The type of " ++ pr_id id ++ str " is not inductive." in
        Errors.errorlabstrm "" msg
    in
    let IndType (indf,realargs) = find_rectype env sigma t in
    let evdref = ref sigma in
    let (elim_predicate, args) =
      make_inv_predicate env evdref indf realargs id status concl in
    let sigma = !evdref in
    let (cut_concl,case_tac) =
      if status != NoDep && (dependent c concl) then
        Reduction.beta_appvect elim_predicate (Array.of_list (realargs@[c])),
        case_then_using
      else
        Reduction.beta_appvect elim_predicate (Array.of_list realargs),
        case_nodep_then_using
    in
    let refined id =
      let prf = mkApp (mkVar id, args) in
      Proofview.Refine.refine (fun h -> h, prf)
    in
    let neqns = List.length realargs in
    let as_mode = names != None in
    tclTHEN (Proofview.Unsafe.tclEVARS sigma)
      (tclTHENS
        (assert_before Anonymous cut_concl)
        [case_tac names
            (introCaseAssumsThen
               (rewrite_equations_tac as_mode inv_kind id neqns))
            (Some elim_predicate) ind (c, t);
        onLastHypId (fun id -> tclTHEN (refined id) reflexivity)])
  end

(* Error messages of the inversion tactics *)
let wrap_inv_error id = function (e, info) -> match e with
  | Indrec.RecursionSchemeError
      (Indrec.NotAllowedCaseAnalysis (_,(Type _ | Prop Pos as k),i)) ->
      Proofview.tclENV >>= fun env ->
      tclZEROMSG (
	(strbrk "Inversion would require case analysis on sort " ++
	pr_sort Evd.empty k ++
	strbrk " which is not allowed for inductive definition " ++
	pr_inductive env (fst i) ++ str "."))
  | e -> Proofview.tclZERO ~info e

(* The most general inversion tactic *)
let inversion inv_kind status names id =
  Proofview.tclORELSE
    (raw_inversion inv_kind id status names)
    (wrap_inv_error id)

(* Specializing it... *)

let inv_gen thin status names =
  try_intros_until (inversion thin status names)

open Tacexpr

let inv k = inv_gen k NoDep

let inv_tac id       = inv FullInversion None (NamedHyp id)
let inv_clear_tac id = inv FullInversionClear None (NamedHyp id)

let dinv k c = inv_gen k (Dep c)

let dinv_tac id       = dinv FullInversion None None (NamedHyp id)
let dinv_clear_tac id = dinv FullInversionClear None None (NamedHyp id)

(* InvIn will bring the specified clauses into the conclusion, and then
 * perform inversion on the named hypothesis.  After, it will intro them
 * back to their places in the hyp-list. *)

let invIn k names ids id =
  Proofview.Goal.nf_enter begin fun gl ->
    let hyps = List.map (fun id -> pf_get_hyp id gl) ids in
    let concl = Proofview.Goal.concl gl in
    let nb_prod_init = nb_prod concl in
    let intros_replace_ids =
      Proofview.Goal.enter begin fun gl ->
        let concl = pf_nf_concl gl in
        let nb_of_new_hyp =
          nb_prod concl - (List.length hyps + nb_prod_init)
        in
        if nb_of_new_hyp < 1 then
          intros_replacing ids
        else
          tclTHEN (tclDO nb_of_new_hyp intro) (intros_replacing ids)
      end
    in
    Proofview.tclORELSE
      (tclTHENLIST
         [bring_hyps hyps;
          inversion k NoDep names id;
          intros_replace_ids])
      (wrap_inv_error id)
  end

let invIn_gen k names idl = try_intros_until (invIn k names idl)

let inv_clause k names = function
  | [] -> inv k names
  | idl -> invIn_gen k names idl
