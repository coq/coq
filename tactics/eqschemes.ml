(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* File created by Hugo Herbelin, Nov 2009 *)

(* This file builds schemes related to equality inductive types,
   especially for dependent rewrite, rewriting on arbitrary equality
   types and congruence on arbitrary equality types *)

(* However, the choices made lack uniformity, as we have to make a
   compromise between several constraints and ideal requirements:

   - Having the extended schemes working conservatively over the
     existing non-dependent schemes eq_rect and eq_rect_r. There is in
     particular a problem with the dependent rewriting schemes in
     hypotheses for which the inductive types cannot be in last
     position of the scheme as it is the general rule in Coq. This has
     an effect on the order of generated goals (side-conditions of the
     lemma after or before the main goal). The non-dependent case can be
     fixed but to the price of a lost of uniformity wrt side-conditions
     in the dependent and non-dependent cases.

   - Having schemes general enough to support non-symmetric equality
     type like eq_true.

   - Having schemes that avoid introducing beta-expansions blocked by
     "match" so as to please the guard condition, but this introduces
     some tricky things involving involutivity of symmetry that I
     don't how to avoid. The result below is a compromise with
     dependent left-to-right rewriting in conclusion (l2r_dep) using
     the tricky involutivity of symmetry and dependent left-to-right
     rewriting in hypotheses (r2l_forward_dep), that one wants to be
     used for non-symmetric equality and that introduces blocked
     beta-expansions.

   One may wonder whether these extensions are worth to be done
   regarding the price we have to pay and regarding the rare
   situations where they are needed. However, I believe it meets a 
   natural expectation of the user.
*)

open CErrors
open Util
open Names
open Term
open Constr
open Vars
open Declarations
open Environ
open Inductive
open Termops
open Namegen
open Inductiveops
open Ind_tables
open Indrec
open Context.Rel.Declaration

module RelDecl = Context.Rel.Declaration

let hid = Id.of_string "H"
let xid = Id.of_string "X"
let default_id_of_sort = function InProp | InSet -> hid | InType -> xid
let fresh env id = next_global_ident_away id Id.Set.empty
let with_context_set ctx (b, ctx') = 
  (b, Univ.ContextSet.union ctx ctx')

let build_dependent_inductive ind (mib,mip) =
  let realargs,_ = List.chop mip.mind_nrealdecls mip.mind_arity_ctxt in
  applist
    (mkIndU ind,
       Context.Rel.to_extended_list mkRel mip.mind_nrealdecls mib.mind_params_ctxt
       @ Context.Rel.to_extended_list mkRel 0 realargs)

let named_hd env t na = named_hd env (Evd.from_env env) (EConstr.of_constr t) na
let name_assumption env = function
| LocalAssum (na,t) -> LocalAssum (named_hd env t na, t)
| LocalDef (na,c,t) -> LocalDef (named_hd env c na, c, t)

let name_context env hyps =
  snd
    (List.fold_left
       (fun (env,hyps) d ->
	  let d' = name_assumption env d in (push_rel d' env, d' :: hyps))
       (env,[]) (List.rev hyps))

let my_it_mkLambda_or_LetIn s c = it_mkLambda_or_LetIn c s
let my_it_mkProd_or_LetIn s c = Term.it_mkProd_or_LetIn c s
let my_it_mkLambda_or_LetIn_name s c =
  let env = Global.env () in
  let mkLambda_or_LetIn_name d b = mkLambda_or_LetIn (name_assumption env d) b in
  List.fold_left (fun c d -> mkLambda_or_LetIn_name d c) c s

let get_coq_eq ctx =
  try
    let eq = Globnames.destIndRef Coqlib.glob_eq in
    (* Do not force the lazy if they are not defined *)
    let eq, ctx = with_context_set ctx 
      (UnivGen.fresh_inductive_instance (Global.env ()) eq) in
      mkIndU eq, mkConstructUi (eq,1), ctx
  with Not_found ->
    user_err Pp.(str "eq not found.")

let univ_of_eq env eq =
  let open EConstr in
  let eq = of_constr eq in
  let sigma = Evd.from_env env in
  match kind sigma (Retyping.get_type_of env sigma eq) with
  | Prod (_,t,_) -> (match kind sigma t with
                       Sort k ->
                        (match ESorts.kind sigma k with Type u -> u | _ -> assert false)
                     | _ -> assert false)
  | _ -> assert false

(**********************************************************************)
(* Check if an inductive type [ind] has the form                      *)
(*                                                                    *)
(*   I q1..qm,p1..pn a1..an with one constructor                      *)
(*   C : I q1..qm,p1..pn p1..pn                                       *)
(*                                                                    *)
(* in which case, a symmetry lemma is definable                       *)
(**********************************************************************)

let error msg = user_err Pp.(str msg)

let get_sym_eq_data env (ind,u) =
  let (mib,mip as specif) = lookup_mind_specif env ind in
  if not (Int.equal (Array.length mib.mind_packets) 1) ||
    not (Int.equal (Array.length mip.mind_nf_lc) 1) then
    error "Not an inductive type with a single constructor.";
  let arityctxt = Vars.subst_instance_context u mip.mind_arity_ctxt in
  let realsign,_ = List.chop mip.mind_nrealdecls arityctxt in
  if List.exists is_local_def realsign then
    error "Inductive equalities with local definitions in arity not supported.";
  let constrsign,ccl = decompose_prod_assum mip.mind_nf_lc.(0) in
  let _,constrargs = decompose_app ccl in
  if not (Int.equal (Context.Rel.length constrsign) (Context.Rel.length mib.mind_params_ctxt)) then
    error "Constructor must have no arguments"; (* This can be relaxed... *)
  let params,constrargs = List.chop mib.mind_nparams constrargs in
  if mip.mind_nrealargs > mib.mind_nparams then
    error "Constructors arguments must repeat the parameters.";
  let _,params2 = List.chop (mib.mind_nparams-mip.mind_nrealargs) params in
  let paramsctxt = Vars.subst_instance_context u mib.mind_params_ctxt in
  let paramsctxt1,_ =
    List.chop (mib.mind_nparams-mip.mind_nrealargs) paramsctxt in
  if not (List.equal Constr.equal params2 constrargs) then
    error "Constructors arguments must repeat the parameters.";
  (* nrealargs_ctxt and nrealargs are the same here *)
  (specif,mip.mind_nrealargs,realsign,paramsctxt,paramsctxt1)

(**********************************************************************)
(* Check if an inductive type [ind] has the form                      *)
(*                                                                    *)
(*   I q1..qm a1..an with one constructor                             *)
(*   C : I q1..qm b1..bn                                              *)
(*                                                                    *)
(* in which case it expresses the equalities ai=bi, but not in a way  *)
(* such that symmetry is a priori definable                           *)
(**********************************************************************)

let get_non_sym_eq_data env (ind,u) =
  let (mib,mip as specif) = lookup_mind_specif env ind in
  if not (Int.equal (Array.length mib.mind_packets) 1) ||
    not (Int.equal (Array.length mip.mind_nf_lc) 1) then
    error "Not an inductive type with a single constructor.";
  let arityctxt = Vars.subst_instance_context u mip.mind_arity_ctxt in
  let realsign,_ = List.chop mip.mind_nrealdecls arityctxt in
  if List.exists is_local_def realsign then
    error "Inductive equalities with local definitions in arity not supported";
  let constrsign,ccl = decompose_prod_assum mip.mind_nf_lc.(0) in
  let _,constrargs = decompose_app ccl in
  if not (Int.equal (Context.Rel.length constrsign) (Context.Rel.length mib.mind_params_ctxt)) then
    error "Constructor must have no arguments";
  let _,constrargs = List.chop mib.mind_nparams constrargs in
  let constrargs = List.map (Vars.subst_instance_constr u) constrargs in
  let paramsctxt = Vars.subst_instance_context u mib.mind_params_ctxt in
  (specif,constrargs,realsign,paramsctxt,mip.mind_nrealargs)

(**********************************************************************)
(* Build the symmetry lemma associated to an inductive type           *)
(* I q1..qm,p1..pn a1..an with one constructor                        *)
(* C : I q1..qm,p1..pn p1..pn                                         *)
(*                                                                    *)
(* sym := fun q1..qn p1..pn a1..an (H:I q1..qm p1..pn a1..an) =>      *)
(*        match H in I _.._ a1..an return I q1..qm a1..an p1..pn with *)
(*            C => C                                                  *)
(*        end                                                         *)
(*      : forall q1..qm p1..pn a1..an I q1..qm p1..pn a1..an ->       *)
(*          I q1..qm a1..an p1..pn                                    *)
(*                                                                    *)
(**********************************************************************)

let build_sym_scheme env ind =
  let (ind,u as indu), ctx = UnivGen.fresh_inductive_instance env ind in
  let (mib,mip as specif),nrealargs,realsign,paramsctxt,paramsctxt1 =
    get_sym_eq_data env indu in
  let cstr n =
    mkApp (mkConstructUi(indu,1),Context.Rel.to_extended_vect mkRel n mib.mind_params_ctxt) in
  let varH = fresh env (default_id_of_sort (snd (mind_arity mip))) in
  let applied_ind = build_dependent_inductive indu specif in
  let realsign_ind =
    name_context env ((LocalAssum (Name varH,applied_ind))::realsign) in
  let ci = make_case_info (Global.env()) ind RegularStyle in
  let c = 
  (my_it_mkLambda_or_LetIn paramsctxt
  (my_it_mkLambda_or_LetIn_name realsign_ind
  (mkCase (ci,
     my_it_mkLambda_or_LetIn_name
       (lift_rel_context (nrealargs+1) realsign_ind)
       (mkApp (mkIndU indu,Array.concat
	  [Context.Rel.to_extended_vect mkRel (3*nrealargs+2) paramsctxt1;
	   rel_vect 1 nrealargs;
	   rel_vect (2*nrealargs+2) nrealargs])),
     mkRel 1 (* varH *),
       [|cstr (nrealargs+1)|]))))
  in c, UState.of_context_set ctx

let sym_scheme_kind =
  declare_individual_scheme_object "_sym_internal"
  (fun _ ind ->
    let c, ctx = build_sym_scheme (Global.env() (* side-effect! *)) ind in
      (c, ctx), Safe_typing.empty_private_constants)

(**********************************************************************)
(* Build the involutivity of symmetry for an inductive type           *)
(* I q1..qm,p1..pn a1..an with one constructor                        *)
(* C : I q1..qm,p1..pn p1..pn                                         *)
(*                                                                    *)
(* inv := fun q1..qn p1..pn a1..an (H:I q1..qm p1..pn a1..an) =>      *)
(*        match H in I _.._ a1..an return                             *)
(*          sym q1..qm p1..pn a1..an (sym q1..qm a1..an p1..pn H) = H *)
(*        with                                                        *)
(*          C => refl_equal C                                         *)
(*        end                                                         *)
(*      : forall q1..qm p1..pn a1..an (H:I q1..qm a1..an p1..pn),     *)
(*          sym q1..qm p1..pn a1..an (sym q1..qm a1..an p1..pn H) = H *)
(*                                                                    *)
(**********************************************************************)

let const_of_scheme kind env ind ctx = 
  let sym_scheme, eff = (find_scheme kind ind) in
  let sym, ctx = with_context_set ctx 
    (UnivGen.fresh_constant_instance (Global.env()) sym_scheme) in
    mkConstU sym, ctx, eff

let build_sym_involutive_scheme env ind =
  let (ind,u as indu), ctx = UnivGen.fresh_inductive_instance env ind in
  let (mib,mip as specif),nrealargs,realsign,paramsctxt,paramsctxt1 =
    get_sym_eq_data env indu in
  let eq,eqrefl,ctx = get_coq_eq ctx in
  let sym, ctx, eff = const_of_scheme sym_scheme_kind env ind ctx in
  let cstr n = mkApp (mkConstructUi (indu,1),Context.Rel.to_extended_vect mkRel n paramsctxt) in
  let varH = fresh env (default_id_of_sort (snd (mind_arity mip))) in
  let applied_ind = build_dependent_inductive indu specif in
  let applied_ind_C =
    mkApp
      (mkIndU indu, Array.append
         (Context.Rel.to_extended_vect mkRel (nrealargs+1) mib.mind_params_ctxt)
         (rel_vect (nrealargs+1) nrealargs)) in
  let realsign_ind =
    name_context env ((LocalAssum (Name varH,applied_ind))::realsign) in
  let ci = make_case_info (Global.env()) ind RegularStyle in
  let c = 
    (my_it_mkLambda_or_LetIn paramsctxt
     (my_it_mkLambda_or_LetIn_name realsign_ind
      (mkCase (ci,
	       my_it_mkLambda_or_LetIn_name
	       (lift_rel_context (nrealargs+1) realsign_ind)
	       (mkApp (eq,[|
	       mkApp
	       (mkIndU indu, Array.concat
	       [Context.Rel.to_extended_vect mkRel (3*nrealargs+2) paramsctxt1;
		rel_vect (2*nrealargs+2) nrealargs;
		rel_vect 1 nrealargs]);
               mkApp (sym,Array.concat
	       [Context.Rel.to_extended_vect mkRel (3*nrealargs+2) paramsctxt1;
		rel_vect 1 nrealargs;
		rel_vect (2*nrealargs+2) nrealargs;
		[|mkApp (sym,Array.concat
		[Context.Rel.to_extended_vect mkRel (3*nrealargs+2) paramsctxt1;
		 rel_vect (2*nrealargs+2) nrealargs;
		 rel_vect 1 nrealargs;
		 [|mkRel 1|]])|]]);
	       mkRel 1|])),
	       mkRel 1 (* varH *),
	       [|mkApp(eqrefl,[|applied_ind_C;cstr (nrealargs+1)|])|]))))
  in (c, UState.of_context_set ctx), eff

let sym_involutive_scheme_kind =
  declare_individual_scheme_object "_sym_involutive"
  (fun _ ind ->
    build_sym_involutive_scheme (Global.env() (* side-effect! *)) ind)

(**********************************************************************)
(* Build the left-to-right rewriting lemma for conclusion associated  *)
(* to an inductive type I q1..qm,p1..pn a1..an with one constructor   *)
(* C : I q1..qm,p1..pn p1..pn                                         *)
(* (symmetric equality in non-dependent and dependent cases)          *)
(*                                                                    *)
(* We could have defined the scheme in one match over a generalized   *)
(* type but this behaves badly wrt the guard condition, so we use     *)
(* symmetry instead; with commutative-cuts-aware guard condition a    *)
(* proof in the style of l2r_forward is also possible (see below)     *)
(*                                                                    *)
(* rew := fun q1..qm p1..pn a1..an                                    *)
(*          (P:forall p1..pn, I q1..qm p1..pn a1..an -> kind)         *)
(*          (HC:P a1..an C)                                           *)
(*          (H:I q1..qm p1..pn a1..an)  =>                            *)
(*          match sym_involutive q1..qm p1..pn a1..an H as Heq        *)
(*                in _ = H return P p1..pn H                          *)
(*          with                                                      *)
(*            refl =>                                                 *)
(*              match sym q1..qm p1..pn a1..an H as H                 *)
(*                     in I _.._ p1..pn                               *)
(*                    return P p1..pn (sym q1..qm a1..an p1..pn H)    *)
(*              with                                                  *)
(*                C => HC                                             *)
(*              end                                                   *)
(*          end                                                       *)
(*      : forall q1..qn p1..pn a1..an                                 *)
(*          (P:forall p1..pn, I q1..qm p1..pn a1..an -> kind),        *)
(*          P a1..an C ->                                             *)
(*          forall (H:I q1..qm p1..pn a1..an), P p1..pn H             *)
(*                                                                    *)
(* where A1..An are the common types of p1..pn and a1..an             *)
(*                                                                    *)
(* Note: the symmetry is needed in the dependent case since the       *)
(* dependency is on the inner arguments (the indices in C) and these  *)
(* inner arguments need to be visible as parameters to be able to     *)
(* abstract over them in P.                                           *)
(**********************************************************************)

(**********************************************************************)
(* For information, the alternative proof of dependent l2r_rew scheme *)
(* that would use commutative cuts is the following                   *)
(*                                                                    *)
(* rew := fun q1..qm p1..pn a1..an                                    *)
(*          (P:forall p1..pn, I q1..qm p1..pn a1..an -> kind)         *)
(*          (HC:P a1..an C)                                           *)
(*          (H:I q1..qm p1..pn a1..an)  =>                            *)
(*          match H in I .._.. a1..an return                          *)
(*             forall p1..pn, I q1..qm p1..pn a1..an -> kind),        *)
(*             P a1..an C -> P p1..pn H                               *)
(*          with                                                      *)
(*            C => fun P HC => HC                                     *)
(*          end P HC                                                  *)
(*      : forall q1..qn p1..pn a1..an                                 *)
(*          (P:forall p1..pn, I q1..qm p1..pn a1..an -> kind),        *)
(*          P a1..an C ->                                             *)
(*          forall (H:I q1..qm p1..pn a1..an), P p1..pn H             *)
(*                                                                    *)
(**********************************************************************)

let build_l2r_rew_scheme dep env ind kind =
  let (ind,u as indu), ctx = UnivGen.fresh_inductive_instance env ind in
  let (mib,mip as specif),nrealargs,realsign,paramsctxt,paramsctxt1 =
    get_sym_eq_data env indu in
  let sym, ctx, eff = const_of_scheme sym_scheme_kind env ind ctx in
  let sym_involutive, ctx, eff' = const_of_scheme sym_involutive_scheme_kind env ind ctx in
  let eq,eqrefl,ctx = get_coq_eq ctx in
  let cstr n p =
    mkApp (mkConstructUi(indu,1),
      Array.concat [Context.Rel.to_extended_vect mkRel n paramsctxt1;
                    rel_vect p nrealargs]) in
  let varH = fresh env (default_id_of_sort (snd (mind_arity mip))) in
  let varHC = fresh env (Id.of_string "HC") in
  let varP = fresh env (Id.of_string "P") in
  let applied_ind = build_dependent_inductive indu specif in
  let applied_ind_P =
    mkApp (mkIndU indu, Array.concat
       [Context.Rel.to_extended_vect mkRel (3*nrealargs) paramsctxt1;
        rel_vect 0 nrealargs;
        rel_vect nrealargs nrealargs]) in
  let applied_ind_G =
    mkApp (mkIndU indu, Array.concat
       [Context.Rel.to_extended_vect mkRel (3*nrealargs+3) paramsctxt1;
        rel_vect (nrealargs+3) nrealargs;
        rel_vect 0 nrealargs]) in
  let realsign_P = lift_rel_context nrealargs realsign in
  let realsign_ind_P =
    name_context env ((LocalAssum (Name varH,applied_ind_P))::realsign_P) in
  let realsign_ind_G =
    name_context env ((LocalAssum (Name varH,applied_ind_G))::
                      lift_rel_context (nrealargs+3) realsign) in
  let applied_sym_C n =
     mkApp(sym,
       Array.append (Context.Rel.to_extended_vect mkRel n mip.mind_arity_ctxt) [|mkVar varH|]) in
  let applied_sym_G =
     mkApp(sym,
       Array.concat [Context.Rel.to_extended_vect mkRel (nrealargs*3+4) paramsctxt1;
                     rel_vect (nrealargs+4) nrealargs;
                     rel_vect 1 nrealargs;
		     [|mkRel 1|]]) in
  let s, ctx' = UnivGen.fresh_sort_in_family kind in
  let ctx = Univ.ContextSet.union ctx ctx' in
  let s = mkSort s in
  let ci = make_case_info (Global.env()) ind RegularStyle in
  let cieq = make_case_info (Global.env()) (fst (destInd eq)) RegularStyle in
  let applied_PC =
    mkApp (mkVar varP,Array.append (Context.Rel.to_extended_vect mkRel 1 realsign)
           (if dep then [|cstr (2*nrealargs+1) 1|] else [||])) in
  let applied_PG =
    mkApp (mkVar varP,Array.append (rel_vect 1 nrealargs)
           (if dep then [|applied_sym_G|] else [||])) in
  let applied_PR =
    mkApp (mkVar varP,Array.append (rel_vect (nrealargs+5) nrealargs)
           (if dep then [|mkRel 2|] else [||])) in
  let applied_sym_sym =
         mkApp (sym,Array.concat
	   [Context.Rel.to_extended_vect mkRel (2*nrealargs+4) paramsctxt1;
            rel_vect 4 nrealargs;
            rel_vect (nrealargs+4) nrealargs;
            [|mkApp (sym,Array.concat
	      [Context.Rel.to_extended_vect mkRel (2*nrealargs+4) paramsctxt1;
	       rel_vect (nrealargs+4) nrealargs;
	       rel_vect 4 nrealargs;
	       [|mkRel 2|]])|]]) in
  let main_body =
    mkCase (ci,
      my_it_mkLambda_or_LetIn_name realsign_ind_G applied_PG,
      applied_sym_C 3,
      [|mkVar varHC|]) in
  let c = 
  (my_it_mkLambda_or_LetIn paramsctxt
  (my_it_mkLambda_or_LetIn_name realsign
  (mkNamedLambda varP
    (my_it_mkProd_or_LetIn (if dep then realsign_ind_P else realsign_P) s)
  (mkNamedLambda varHC applied_PC
  (mkNamedLambda varH (lift 2 applied_ind)
  (if dep then (* we need a coercion *)
     mkCase (cieq,
       mkLambda (Name varH,lift 3 applied_ind,
         mkLambda (Anonymous,
                   mkApp (eq,[|lift 4 applied_ind;applied_sym_sym;mkRel 1|]),
                   applied_PR)),
       mkApp (sym_involutive,
         Array.append (Context.Rel.to_extended_vect mkRel 3 mip.mind_arity_ctxt) [|mkVar varH|]),
       [|main_body|])
   else
     main_body))))))
  in (c, UState.of_context_set ctx),
      Safe_typing.concat_private eff' eff

(**********************************************************************)
(* Build the left-to-right rewriting lemma for hypotheses associated  *)
(* to an inductive type I q1..qm,p1..pn a1..an with one constructor   *)
(* C : I q1..qm,p1..pn p1..pn                                         *)
(* (symmetric equality in non dependent and dependent cases)          *)
(*                                                                    *)
(* rew := fun q1..qm p1..pn a1..an (H:I q1..qm p1..pn a1..an)         *)
(*          match H in I _.._ a1..an                                  *)
(*                 return forall                                      *)
(*                  (P:forall p1..pn, I q1..qm p1..pn a1..an -> kind) *)
(*                  (HC:P p1..pn H) =>                                *)
(*                  P a1..an C                                        *)
(*          with                                                      *)
(*             C => fun P HC => HC                                    *)
(*          end                                                       *)
(*      : forall q1..qm p1..pn a1..an                                 *)
(*          (H:I q1..qm p1..pn a1..an)                                *)
(*          (P:forall p1..pn, I q1..qm p1..pn a1..an ->kind),         *)
(*          P p1..pn H -> P a1..an C                                  *)
(*                                                                    *)
(* Note: the symmetry is needed in the dependent case since the       *)
(* dependency is on the inner arguments (the indices in C) and these  *)
(* inner arguments need to be visible as parameters to be able to     *)
(* abstract over them in P.                                           *)
(**********************************************************************)

let build_l2r_forward_rew_scheme dep env ind kind =
  let (ind,u as indu), ctx = UnivGen.fresh_inductive_instance env ind in
  let (mib,mip as specif),nrealargs,realsign,paramsctxt,paramsctxt1 =
    get_sym_eq_data env indu in
  let cstr n p =
    mkApp (mkConstructUi(indu,1),
      Array.concat [Context.Rel.to_extended_vect mkRel n paramsctxt1;
                    rel_vect p nrealargs]) in
  let varH = fresh env (default_id_of_sort (snd (mind_arity mip))) in
  let varHC = fresh env (Id.of_string "HC") in
  let varP = fresh env (Id.of_string "P") in
  let applied_ind = build_dependent_inductive indu specif in
  let applied_ind_P =
    mkApp (mkIndU indu, Array.concat
       [Context.Rel.to_extended_vect mkRel (4*nrealargs+2) paramsctxt1;
        rel_vect 0 nrealargs;
        rel_vect (nrealargs+1) nrealargs]) in
  let applied_ind_P' =
    mkApp (mkIndU indu, Array.concat
       [Context.Rel.to_extended_vect mkRel (3*nrealargs+1) paramsctxt1;
        rel_vect 0 nrealargs;
        rel_vect (2*nrealargs+1) nrealargs]) in
  let realsign_P n = lift_rel_context (nrealargs*n+n) realsign in
  let realsign_ind =
    name_context env ((LocalAssum (Name varH,applied_ind))::realsign) in
  let realsign_ind_P n aP =
    name_context env ((LocalAssum (Name varH,aP))::realsign_P n) in
  let s, ctx' = UnivGen.fresh_sort_in_family kind in
  let ctx = Univ.ContextSet.union ctx ctx' in
  let s = mkSort s in
  let ci = make_case_info (Global.env()) ind RegularStyle in
  let applied_PC =
    mkApp (mkVar varP,Array.append
           (rel_vect (nrealargs*2+3) nrealargs)
           (if dep then [|mkRel 2|] else [||])) in
  let applied_PC' =
    mkApp (mkVar varP,Array.append
           (rel_vect (nrealargs+2) nrealargs)
           (if dep then [|cstr (2*nrealargs+2) (nrealargs+2)|]
	    else [||])) in
  let applied_PG =
    mkApp (mkVar varP,Array.append (rel_vect 3 nrealargs)
           (if dep then [|cstr (3*nrealargs+4) 3|] else [||])) in
  let c = 
  (my_it_mkLambda_or_LetIn paramsctxt
  (my_it_mkLambda_or_LetIn_name realsign
  (mkNamedLambda varH applied_ind
  (mkCase (ci,
     my_it_mkLambda_or_LetIn_name
       (lift_rel_context (nrealargs+1) realsign_ind)
       (mkNamedProd varP
         (my_it_mkProd_or_LetIn
	   (if dep then realsign_ind_P 2 applied_ind_P else realsign_P 2) s)
       (mkNamedProd varHC applied_PC applied_PG)),
     (mkVar varH),
     [|mkNamedLambda varP
        (my_it_mkProd_or_LetIn
	  (if dep then realsign_ind_P 1 applied_ind_P' else realsign_P 2) s)
      (mkNamedLambda varHC applied_PC'
	(mkVar varHC))|])))))
  in c, UState.of_context_set ctx

(**********************************************************************)
(* Build the right-to-left rewriting lemma for hypotheses associated  *)
(* to an inductive type I q1..qm a1..an with one constructor          *)
(* C : I q1..qm b1..bn                                                *)
(* (arbitrary equality in non-dependent and dependent cases)          *)
(*                                                                    *)
(* rew := fun q1..qm a1..an (H:I q1..qm a1..an)                       *)
(*          (P:forall a1..an, I q1..qm a1..an -> kind)                *)
(*          (HC:P a1..an H) =>                                        *)
(*          match H in I _.._ a1..an return P a1..an H -> P b1..bn C  *)
(*          with                                                      *)
(*            C => fun x => x                                         *)
(*          end HC                                                    *)
(*      : forall q1..pm a1..an (H:I q1..qm a1..an)                    *)
(*          (P:forall a1..an, I q1..qm a1..an -> kind),               *)
(*          P a1..an H -> P b1..bn C                                  *)
(*                                                                    *)
(* Note that the dependent elimination here is not a dependency       *)
(* in the conclusion of the scheme but a dependency in the premise of *)
(* the scheme. This is unfortunately incompatible with the standard   *)
(* pattern for schemes in Coq which expects that the eliminated       *)
(* object is the last premise of the scheme. We then have no choice   *)
(* than following the more liberal pattern of having the eliminated   *)
(* object coming before the premises.                                 *)
(*                                                                    *)
(* Note that in the non-dependent case, this scheme (up to the order  *)
(* of premises) generalizes the (backward) l2r scheme above: same     *)
(* statement but no need for symmetry of the equality.                *)
(**********************************************************************)

let build_r2l_forward_rew_scheme dep env ind kind = 
  let (ind,u as indu), ctx = UnivGen.fresh_inductive_instance env ind in
  let ((mib,mip as specif),constrargs,realsign,paramsctxt,nrealargs) =
    get_non_sym_eq_data env indu in
  let cstr n =
    mkApp (mkConstructUi(indu,1),Context.Rel.to_extended_vect mkRel n mib.mind_params_ctxt) in
  let constrargs_cstr = constrargs@[cstr 0] in
  let varH = fresh env (default_id_of_sort (snd (mind_arity mip))) in
  let varHC = fresh env (Id.of_string "HC") in
  let varP = fresh env (Id.of_string "P") in
  let applied_ind = build_dependent_inductive indu specif in
  let realsign_ind =
    name_context env ((LocalAssum (Name varH,applied_ind))::realsign) in
  let s, ctx' = UnivGen.fresh_sort_in_family kind in
  let ctx = Univ.ContextSet.union ctx ctx' in
  let s = mkSort s in
  let ci = make_case_info (Global.env()) ind RegularStyle in
  let applied_PC =
    applist (mkVar varP,if dep then constrargs_cstr else constrargs) in
  let applied_PG =
    mkApp (mkVar varP,
           if dep then Context.Rel.to_extended_vect mkRel 0 realsign_ind
	   else Context.Rel.to_extended_vect mkRel 1 realsign) in
  let c = 
  (my_it_mkLambda_or_LetIn paramsctxt
  (my_it_mkLambda_or_LetIn_name realsign_ind
  (mkNamedLambda varP
    (my_it_mkProd_or_LetIn (lift_rel_context (nrealargs+1)
                             (if dep then realsign_ind else realsign)) s)
  (mkNamedLambda varHC (lift 1 applied_PG)
  (mkApp
    (mkCase (ci,
       my_it_mkLambda_or_LetIn_name
         (lift_rel_context (nrealargs+3) realsign_ind)
         (mkArrow applied_PG (lift (2*nrealargs+5) applied_PC)),
       mkRel 3 (* varH *),
       [|mkLambda
          (Name varHC,
	   lift (nrealargs+3) applied_PC,
	   mkRel 1)|]),
    [|mkVar varHC|]))))))
  in c, UState.of_context_set ctx

(**********************************************************************)
(* This function "repairs" the non-dependent r2l forward rewriting    *)
(* scheme by making it comply with the standard pattern of schemes    *)
(* in Coq. Otherwise said, it turns a scheme of type                  *)
(*                                                                    *)
(*  forall q1..pm a1..an, I q1..qm a1..an ->                          *)
(*  forall (P: forall a1..an, kind),                                  *)
(*         P a1..an -> P b1..bn                                       *)
(*                                                                    *)
(* into a scheme of type                                              *)
(*                                                                    *)
(*  forall q1..pm (P:forall a1..an, kind),                            *)
(*         P a1..an -> forall a1..an, I q1..qm a1..an -> P b1..bn     *)
(*                                                                    *)
(**********************************************************************)

let fix_r2l_forward_rew_scheme (c, ctx') =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let t = Retyping.get_type_of env sigma (EConstr.of_constr c) in
  let t = EConstr.Unsafe.to_constr t in
  let ctx,_ = decompose_prod_assum t in
  match ctx with
  | hp :: p :: ind :: indargs ->
     let c' = 
      my_it_mkLambda_or_LetIn indargs
        (mkLambda_or_LetIn (RelDecl.map_constr (liftn (-1) 1) p)
	  (mkLambda_or_LetIn (RelDecl.map_constr (liftn (-1) 2) hp)
	    (mkLambda_or_LetIn (RelDecl.map_constr (lift 2) ind)
              (EConstr.Unsafe.to_constr (Reductionops.whd_beta sigma
		(EConstr.of_constr (applist (c,
	          Context.Rel.to_extended_list mkRel 3 indargs @ [mkRel 1;mkRel 3;mkRel 2]))))))))
      in c', ctx'
  | _ -> anomaly (Pp.str "Ill-formed non-dependent left-to-right rewriting scheme.")

(**********************************************************************)
(* Build the right-to-left rewriting lemma for conclusion associated  *)
(* to an inductive type I q1..qm a1..an with one constructor          *)
(* C : I q1..qm b1..bn                                                *)
(* (arbitrary equality in non-dependent and dependent case)           *)
(*                                                                    *)
(* This is actually the standard case analysis scheme                 *)
(*                                                                    *)
(* rew := fun q1..qm a1..an                                           *)
(*          (P:forall a1..an, I q1..qm a1..an -> kind)                *)
(*          (H:I q1..qm a1..an)                                       *)
(*          (HC:P b1..bn C) =>                                        *)
(*          match H in I _.._ a1..an return P a1..an H with           *)
(*            C => HC                                                 *)
(*          end                                                       *)
(*      : forall q1..pm a1..an                                        *)
(*          (P:forall a1..an, I q1..qm a1..an -> kind)                *)
(*          (H:I q1..qm a1..an),                                      *)
(*          P b1..bn C -> P a1..an H                                  *)
(**********************************************************************)
 
let build_r2l_rew_scheme dep env ind k =
  let sigma = Evd.from_env env in
  let (sigma, indu) = Evd.fresh_inductive_instance env sigma ind in
  let (sigma, c) = build_case_analysis_scheme env sigma indu dep k in
    c, Evd.evar_universe_context sigma

let build_l2r_rew_scheme = build_l2r_rew_scheme
let build_l2r_forward_rew_scheme = build_l2r_forward_rew_scheme
let build_r2l_rew_scheme = build_r2l_rew_scheme
let build_r2l_forward_rew_scheme = build_r2l_forward_rew_scheme

(**********************************************************************)
(* Register the rewriting schemes                                     *)
(**********************************************************************)

(**********************************************************************)
(* Dependent rewrite from left-to-right in conclusion                 *)
(* (symmetrical equality type only)                                   *)
(* Gamma |- P p1..pn H   ==>   Gamma |- P a1..an C                    *)
(* with H:I p1..pn a1..an in Gamma                                    *)
(**********************************************************************)
let rew_l2r_dep_scheme_kind =
  declare_individual_scheme_object "_rew_r_dep"
  (fun _ ind -> build_l2r_rew_scheme true (Global.env()) ind InType)

(**********************************************************************)
(* Dependent rewrite from right-to-left in conclusion                 *)
(* Gamma |- P a1..an H   ==>   Gamma |- P b1..bn C                    *)
(* with H:I a1..an in Gamma (non symmetric case)                      *)
(* or   H:I b1..bn a1..an in Gamma (symmetric case)                   *)
(**********************************************************************)
let rew_r2l_dep_scheme_kind =
  declare_individual_scheme_object "_rew_dep"
  (fun _ ind -> build_r2l_rew_scheme true (Global.env()) ind InType,Safe_typing.empty_private_constants)

(**********************************************************************)
(* Dependent rewrite from right-to-left in hypotheses                 *)
(* Gamma, P a1..an H |- D   ==>   Gamma, P b1..bn C |- D              *)
(* with H:I a1..an in Gamma (non symmetric case)                      *)
(* or   H:I b1..bn a1..an in Gamma (symmetric case)                   *)
(**********************************************************************)
let rew_r2l_forward_dep_scheme_kind =
  declare_individual_scheme_object "_rew_fwd_dep"
  (fun _ ind -> build_r2l_forward_rew_scheme true (Global.env()) ind InType,Safe_typing.empty_private_constants)

(**********************************************************************)
(* Dependent rewrite from left-to-right in hypotheses                 *)
(* (symmetrical equality type only)                                   *)
(* Gamma, P p1..pn H |- D   ==>   Gamma, P a1..an C |- D              *)
(* with H:I p1..pn a1..an in Gamma                                    *)
(**********************************************************************)
let rew_l2r_forward_dep_scheme_kind =
  declare_individual_scheme_object "_rew_fwd_r_dep"
  (fun _ ind -> build_l2r_forward_rew_scheme true (Global.env()) ind InType,Safe_typing.empty_private_constants)

(**********************************************************************)
(* Non-dependent rewrite from either left-to-right in conclusion or   *)
(* right-to-left in hypotheses: both l2r_rew and r2l_forward_rew are  *)
(* potential candidates. Since l2r_rew needs a symmetrical equality,  *)
(* we adopt r2l_forward_rew (this one introduces a blocked beta-      *)
(* expansion but since the guard condition supports commutative cuts  *)
(* this is not a problem; we need though a fix to adjust it to the    *)
(* standard form of schemes in Coq)                                   *)
(**********************************************************************)
let rew_l2r_scheme_kind =
  declare_individual_scheme_object "_rew_r"
  (fun _ ind -> fix_r2l_forward_rew_scheme
     (build_r2l_forward_rew_scheme false (Global.env()) ind InType), Safe_typing.empty_private_constants)

(**********************************************************************)
(* Non-dependent rewrite from either right-to-left in conclusion or   *)
(* left-to-right in hypotheses: both r2l_rew and l2r_forward_rew but  *)
(* since r2l_rew works in the non-symmetric case as well as without   *)
(* introducing commutative cuts, we adopt it                          *)
(**********************************************************************)
let rew_r2l_scheme_kind =
  declare_individual_scheme_object "_rew"
  (fun _ ind -> build_r2l_rew_scheme false (Global.env()) ind InType, Safe_typing.empty_private_constants)

(* End of rewriting schemes *)

(**********************************************************************)
(* Build the congruence lemma associated to an inductive type         *)
(* I p1..pn a with one constructor C : I q1..qn b                     *)
(*                                                                    *)
(* congr := fun p1..pn (B:Type) (f:A->B) a (H:I p1..pn a) =>          *)
(*          match H in I _.._ a' return f b = f a' with               *)
(*            C => eq_refl (f b)                                      *)
(*          end                                                       *)
(*       : forall p1..pn (B:Type) (f:A->B) a, I p1..pn a -> f b = f a *)
(*                                                                    *)
(* where A is the common type of a and b                              *)
(**********************************************************************)

(* TODO: extend it to types with more than one index *)

let build_congr env (eq,refl,ctx) ind =
  let (ind,u as indu), ctx = with_context_set ctx 
    (UnivGen.fresh_inductive_instance env ind) in
  let (mib,mip) = lookup_mind_specif env ind in
  if not (Int.equal (Array.length mib.mind_packets) 1) || not (Int.equal (Array.length mip.mind_nf_lc) 1) then
    error "Not an inductive type with a single constructor.";
  if not (Int.equal mip.mind_nrealargs 1) then
    error "Expect an inductive type with one predicate parameter.";
  let i = 1 in
  let arityctxt = Vars.subst_instance_context u mip.mind_arity_ctxt in
  let paramsctxt = Vars.subst_instance_context u mib.mind_params_ctxt in
  let realsign,_ = List.chop mip.mind_nrealdecls arityctxt in
  if List.exists is_local_def realsign then
    error "Inductive equalities with local definitions in arity not supported.";
  let env_with_arity = push_rel_context arityctxt env in
  let ty = RelDecl.get_type (lookup_rel (mip.mind_nrealargs - i + 1) env_with_arity) in
  let constrsign,ccl = decompose_prod_assum mip.mind_nf_lc.(0) in
  let _,constrargs = decompose_app ccl in
  if not (Int.equal (Context.Rel.length constrsign) (Context.Rel.length mib.mind_params_ctxt)) then
    error "Constructor must have no arguments";
  let b = List.nth constrargs (i + mib.mind_nparams - 1) in
  let varB = fresh env (Id.of_string "B") in
  let varH = fresh env (Id.of_string "H") in
  let varf = fresh env (Id.of_string "f") in
  let ci = make_case_info (Global.env()) ind RegularStyle in
  let uni, ctx = UnivGen.extend_context (UnivGen.new_global_univ ()) ctx in
  let ctx = (fst ctx, Univ.enforce_leq uni (univ_of_eq env eq) (snd ctx)) in
  let c = 
  my_it_mkLambda_or_LetIn paramsctxt
     (mkNamedLambda varB (mkSort (Type uni))
     (mkNamedLambda varf (mkArrow (lift 1 ty) (mkVar varB))
     (my_it_mkLambda_or_LetIn_name (lift_rel_context 2 realsign)
     (mkNamedLambda varH
        (applist
           (mkIndU indu,
	    Context.Rel.to_extended_list mkRel (mip.mind_nrealargs+2) paramsctxt @
	    Context.Rel.to_extended_list mkRel 0 realsign))
     (mkCase (ci,
       my_it_mkLambda_or_LetIn_name
	 (lift_rel_context (mip.mind_nrealargs+3) realsign)
         (mkLambda
           (Anonymous,
            applist
             (mkIndU indu,
	        Context.Rel.to_extended_list mkRel (2*mip.mind_nrealdecls+3)
		  paramsctxt
	        @ Context.Rel.to_extended_list mkRel 0 realsign),
            mkApp (eq,
	      [|mkVar varB;
                mkApp (mkVar varf, [|lift (2*mip.mind_nrealdecls+4) b|]);
		mkApp (mkVar varf, [|mkRel (mip.mind_nrealargs - i + 2)|])|]))),
       mkVar varH,
       [|mkApp (refl,
          [|mkVar varB;
	    mkApp (mkVar varf, [|lift (mip.mind_nrealargs+3) b|])|])|]))))))
  in c, UState.of_context_set ctx

let congr_scheme_kind = declare_individual_scheme_object "_congr"
  (fun _ ind ->
     (* May fail if equality is not defined *)
   build_congr (Global.env()) (get_coq_eq Univ.ContextSet.empty) ind,
   Safe_typing.empty_private_constants)
