(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
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
     rewriting in hypotheses (l2r_forward_dep), that one wants to be
     used for non-symmetric equality and that introduces blocked
     beta-expansions.

   One may wonder whether these extensions are worth to be done
   regarding the price we have to pay and regarding the rare
   situations where they are needed. However, I believe it meets a 
   natural expectation of the user.
*)

open Util
open Names
open Term
open Declarations
open Environ
open Inductive
open Termops
open Namegen
open Inductiveops
open Ind_tables
open Indrec

let hid = id_of_string "H"
let xid = id_of_string "X"
let default_id_of_sort = function InProp | InSet -> hid | InType -> xid
let fresh env id = next_global_ident_away id []

let build_dependent_inductive ind (mib,mip) =
  let realargs,_ = list_chop mip.mind_nrealargs_ctxt mip.mind_arity_ctxt in
  applist
    (mkInd ind,
       extended_rel_list mip.mind_nrealargs_ctxt mib.mind_params_ctxt
       @ extended_rel_list 0 realargs)

let my_it_mkLambda_or_LetIn s c = it_mkLambda_or_LetIn ~init:c s
let my_it_mkProd_or_LetIn s c = it_mkProd_or_LetIn ~init:c s
let my_it_mkLambda_or_LetIn_name s c =
  it_mkLambda_or_LetIn_name (Global.env()) c s

let get_coq_eq () =
  try
    let eq = Libnames.destIndRef Coqlib.glob_eq in
    let _ = Global.lookup_inductive eq in
    (* Do not force the lazy if they are not defined *)
    mkInd eq, Coqlib.build_coq_eq_refl ()
  with Not_found ->
    error "eq not found."

let get_sym_eq_data env ind =
  let (mib,mip as specif) = lookup_mind_specif env ind in
  if Array.length mib.mind_packets <> 1 or Array.length mip.mind_nf_lc <> 1 then
    error "Not an inductive type with a single constructor.";
  let realsign,_ = list_chop mip.mind_nrealargs_ctxt mip.mind_arity_ctxt in
  if List.exists (fun (_,b,_) -> b <> None) realsign then
    error "Inductive equalities with local definitions in arity not supported.";
  let constrsign,ccl = decompose_prod_assum mip.mind_nf_lc.(0) in
  let _,constrargs = decompose_app ccl in
  if rel_context_length constrsign<>rel_context_length mib.mind_params_ctxt then
    error "Constructor must have no arguments"; (* This can be relaxed... *)
  let params,constrargs = list_chop mib.mind_nparams constrargs in
  if mip.mind_nrealargs > mib.mind_nparams then
    error "Constructors arguments must repeat the parameters.";
  let _,params2 = list_chop (mib.mind_nparams-mip.mind_nrealargs) params in
  let paramsctxt1,_ =
    list_chop (mib.mind_nparams-mip.mind_nrealargs) mib.mind_params_ctxt in
  if params2 <> constrargs then
    error "Constructors arguments must repeat the parameters.";
  (* nrealargs_ctxt and nrealargs are the same here *)
  (specif,mip.mind_nrealargs,realsign,mib.mind_params_ctxt,paramsctxt1)

let get_non_sym_eq_data env ind =
  let (mib,mip as specif) = lookup_mind_specif env ind in
  if Array.length mib.mind_packets <> 1 or Array.length mip.mind_nf_lc <> 1 then
    error "Not an inductive type with a single constructor.";
  let realsign,_ = list_chop mip.mind_nrealargs_ctxt mip.mind_arity_ctxt in
  if List.exists (fun (_,b,_) -> b <> None) realsign then
    error "Inductive equalities with local definitions in arity not supported";
  let constrsign,ccl = decompose_prod_assum mip.mind_nf_lc.(0) in
  let _,constrargs = decompose_app ccl in
  if rel_context_length constrsign<>rel_context_length mib.mind_params_ctxt then
    error "Constructor must have no arguments";
  let _,constrargs = list_chop mib.mind_nparams constrargs in
  (specif,constrargs,realsign,mip.mind_nrealargs)

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
  let (mib,mip as specif),nrealargs,realsign,paramsctxt,paramsctxt1 =
    get_sym_eq_data env ind in
  let cstr n =
    mkApp (mkConstruct(ind,1),extended_rel_vect n mib.mind_params_ctxt) in
  let varH = fresh env (default_id_of_sort (snd (mind_arity mip))) in
  let applied_ind = build_dependent_inductive ind specif in
  let realsign_ind =
    name_context env ((Name varH,None,applied_ind)::realsign) in
  let ci = make_case_info (Global.env()) ind RegularStyle in
  (my_it_mkLambda_or_LetIn mib.mind_params_ctxt
  (my_it_mkLambda_or_LetIn_name realsign_ind
  (mkCase (ci,
     my_it_mkLambda_or_LetIn_name
       (lift_rel_context (nrealargs+1) realsign_ind)
       (mkApp (mkInd ind,Array.concat
	  [extended_rel_vect (3*nrealargs+2) paramsctxt1;
	   rel_vect 1 nrealargs;
	   rel_vect (2*nrealargs+2) nrealargs])),
     mkRel 1 (* varH *),
       [|cstr (nrealargs+1)|]))))

let sym_scheme_kind =
  declare_individual_scheme_object "_sym"
  (fun ind -> build_sym_scheme (Global.env() (* side-effect! *)) ind)

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

let build_sym_involutive_scheme env ind =
  let (mib,mip as specif),nrealargs,realsign,paramsctxt,paramsctxt1 =
    get_sym_eq_data env ind in
  let sym = mkConst (find_scheme sym_scheme_kind ind) in
  let (eq,eqrefl) = get_coq_eq () in
  let cstr n = mkApp (mkConstruct(ind,1),extended_rel_vect n paramsctxt) in
  let varH = fresh env (default_id_of_sort (snd (mind_arity mip))) in
  let applied_ind = build_dependent_inductive ind specif in
  let applied_ind_C =
    mkApp
      (mkInd ind, Array.append
         (extended_rel_vect (nrealargs+1) mib.mind_params_ctxt)
         (rel_vect (nrealargs+1) nrealargs)) in
  let realsign_ind =
    name_context env ((Name varH,None,applied_ind)::realsign) in
  let ci = make_case_info (Global.env()) ind RegularStyle in
  (my_it_mkLambda_or_LetIn paramsctxt
  (my_it_mkLambda_or_LetIn_name realsign_ind
  (mkCase (ci,
     my_it_mkLambda_or_LetIn_name
       (lift_rel_context (nrealargs+1) realsign_ind)
       (mkApp (eq,[|
	 mkApp
	   (mkInd ind, Array.concat
	     [extended_rel_vect (3*nrealargs+2) paramsctxt1;
	      rel_vect (2*nrealargs+2) nrealargs;
	      rel_vect 1 nrealargs]);
         mkApp (sym,Array.concat
	   [extended_rel_vect (3*nrealargs+2) paramsctxt1;
            rel_vect 1 nrealargs;
            rel_vect (2*nrealargs+2) nrealargs;
            [|mkApp (sym,Array.concat
	      [extended_rel_vect (3*nrealargs+2) paramsctxt1;
	       rel_vect (2*nrealargs+2) nrealargs;
	       rel_vect 1 nrealargs;
	       [|mkRel 1|]])|]]);
	 mkRel 1|])),
     mkRel 1 (* varH *),
       [|mkApp(eqrefl,[|applied_ind_C;cstr (nrealargs+1)|])|]))))

let sym_involutive_scheme_kind =
  declare_individual_scheme_object "_sym_involutive"
  (fun ind -> build_sym_involutive_scheme (Global.env() (* side-effect! *)) ind)

(**********************************************************************)
(* Build the left-to-right rewriting lemma for conclusion associated  *)
(* to an inductive type I q1..qm,p1..pn a1..an with one constructor   *)
(* C : I q1..qm,p1..pn p1..pn                                         *)
(* (symmetric equality in non-dependent and dependent cases)          *)
(*                                                                    *)
(* We could have defined the scheme in one match over a generalized   *)
(* type but this behaves badly wrt the guard condition, so we use     *)
(* symmetry instead                                                   *)
(*                                                                    *)
(* ind_rd := fun q1..qm p1..pn a1..an                                 *)
(*               (P:forall p1..pn, I q1..qm p1..pn a1..an -> kind)    *)
(*               (HC:P a1..an C)                                      *)
(*               (H:I q1..qm p1..pn a1..an)  =>                       *)
(*           match sym_involutive q1..qm p1..pn a1..an H as Heq       *)
(*               in _ = H return P p1..pn H                           *)
(*           with                                                     *)
(*             refl =>                                                *)
(*               match sym q1..qm p1..pn a1..an H as H                *)
(*                      in I _.._ p1..pn                              *)
(*                     return P p1..pn (sym q1..qm a1..an p1..pn H)   *)
(*               with                                                 *)
(*                 C => HC                                            *)
(*               end                                                  *)
(*           end                                                      *)
(*       : forall q1..qn p1..pn a1..an                                *)
(*           (P:forall p1..pn, I q1..qm p1..pn a1..an ->kind),        *)
(*           P a1..an C ->                                            *)
(*           forall (H:I q1..qm p1..pn a1..an), P p1..pn H            *)
(*                                                                    *)
(* where A1..An are the common types of p1..pn and a1..an             *)
(**********************************************************************)

let build_l2r_rew_scheme dep env ind kind =
  let (mib,mip as specif),nrealargs,realsign,paramsctxt,paramsctxt1 =
    get_sym_eq_data env ind in
  let sym = mkConst (find_scheme sym_scheme_kind ind) in
  let sym_involutive = mkConst (find_scheme sym_involutive_scheme_kind ind) in
  let (eq,eqrefl) = get_coq_eq () in
  let cstr n p =
    mkApp (mkConstruct(ind,1),
      Array.concat [extended_rel_vect n paramsctxt1;
                    rel_vect p nrealargs]) in
  let varH = fresh env (default_id_of_sort (snd (mind_arity mip))) in
  let varHC = fresh env (id_of_string "HC") in
  let varP = fresh env (id_of_string "P") in
  let applied_ind = build_dependent_inductive ind specif in
  let applied_ind_P =
    mkApp (mkInd ind, Array.concat
       [extended_rel_vect (3*nrealargs) paramsctxt1;
        rel_vect 0 nrealargs;
        rel_vect nrealargs nrealargs]) in
  let applied_ind_G =
    mkApp (mkInd ind, Array.concat
       [extended_rel_vect (3*nrealargs+3) paramsctxt1;
        rel_vect (nrealargs+3) nrealargs;
        rel_vect 0 nrealargs]) in
  let realsign_P = lift_rel_context nrealargs realsign in
  let realsign_ind_P =
    name_context env ((Name varH,None,applied_ind_P)::realsign_P) in
  let realsign_ind_G =
    name_context env ((Name varH,None,applied_ind_G)::
                      lift_rel_context (nrealargs+3) realsign) in
  let applied_sym_C n =
     mkApp(sym,
       Array.append (extended_rel_vect n mip.mind_arity_ctxt) [|mkVar varH|]) in
  let applied_sym_G =
     mkApp(sym,
       Array.concat [extended_rel_vect (nrealargs*3+4) paramsctxt1;
                     rel_vect (nrealargs+4) nrealargs;
                     rel_vect 1 nrealargs;
		     [|mkRel 1|]]) in
  let s = mkSort (new_sort_in_family kind) in
  let ci = make_case_info (Global.env()) ind RegularStyle in
  let cieq = make_case_info (Global.env()) (destInd eq) RegularStyle in
  let applied_PC =
    mkApp (mkVar varP,Array.append (extended_rel_vect 1 realsign)
           (if dep then [|cstr (2*nrealargs+1) 1|] else [||])) in
  let applied_PG =
    mkApp (mkVar varP,Array.append (rel_vect 1 nrealargs)
           (if dep then [|applied_sym_G|] else [||])) in
  let applied_PR =
    mkApp (mkVar varP,Array.append (rel_vect (nrealargs+5) nrealargs)
           (if dep then [|mkRel 2|] else [||])) in
  let applied_sym_sym =
         mkApp (sym,Array.concat
	   [extended_rel_vect (2*nrealargs+4) paramsctxt1;
            rel_vect 4 nrealargs;
            rel_vect (nrealargs+4) nrealargs;
            [|mkApp (sym,Array.concat
	      [extended_rel_vect (2*nrealargs+4) paramsctxt1;
	       rel_vect (nrealargs+4) nrealargs;
	       rel_vect 4 nrealargs;
	       [|mkRel 2|]])|]]) in
  let main_body =
    mkCase (ci,
      my_it_mkLambda_or_LetIn_name realsign_ind_G applied_PG,
      applied_sym_C 3,
      [|mkVar varHC|]) in
  (my_it_mkLambda_or_LetIn mib.mind_params_ctxt
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
         Array.append (extended_rel_vect 3 mip.mind_arity_ctxt) [|mkVar varH|]),
       [|main_body|])
   else
     main_body))))))

(**********************************************************************)
(* Build the right-to-left rewriting lemma for hypotheses associated  *)
(* to an inductive type I q1..qm,p1..pn a1..an with one constructor   *)
(* C : I q1..qm,p1..pn p1..pn                                         *)
(* (symmetric equality in dependent cases)                            *)
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
(*       : forall q1..qm p1..pn a1..an                                *)
(*           (H:I q1..qm p1..pn a1..an)                               *)
(*           (P:forall p1..pn, I q1..qm p1..pn a1..an ->kind),        *)
(*           P p1..pn H -> P a1..an C                                 *)
(*                                                                    *)
(**********************************************************************)

let build_r2l_forward_rew_scheme dep env ind kind =
  let (mib,mip as specif),nrealargs,realsign,paramsctxt,paramsctxt1 =
    get_sym_eq_data env ind in
  let cstr n p =
    mkApp (mkConstruct(ind,1),
      Array.concat [extended_rel_vect n paramsctxt1;
                    rel_vect p nrealargs]) in
  let varH = fresh env (default_id_of_sort (snd (mind_arity mip))) in
  let varHC = fresh env (id_of_string "HC") in
  let varP = fresh env (id_of_string "P") in
  let applied_ind = build_dependent_inductive ind specif in
  let applied_ind_P =
    mkApp (mkInd ind, Array.concat
       [extended_rel_vect (4*nrealargs+2) paramsctxt1;
        rel_vect 0 nrealargs;
        rel_vect (nrealargs+1) nrealargs]) in
  let applied_ind_P' =
    mkApp (mkInd ind, Array.concat
       [extended_rel_vect (3*nrealargs+1) paramsctxt1;
        rel_vect 0 nrealargs;
        rel_vect (2*nrealargs+1) nrealargs]) in
  let realsign_P n = lift_rel_context (nrealargs*n+n) realsign in
  let realsign_ind =
    name_context env ((Name varH,None,applied_ind)::realsign) in
  let realsign_ind_P n aP =
    name_context env ((Name varH,None,aP)::realsign_P n) in
  let s = mkSort (new_sort_in_family kind) in
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
  (my_it_mkLambda_or_LetIn mib.mind_params_ctxt
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

(**********************************************************************)
(* Build the left-to-right rewriting lemma for hypotheses associated  *)
(* to an inductive type I q1..qm a1..an with one constructor          *)
(* C : I q1..qm b1..bn  (dependent case)                              *)
(*                                                                    *)
(* ind_rd := fun q1..qm a1..an (H:I q1..qm a1..an)                    *)
(*             (P:forall a1..an, I q1..qm a1..an -> kind)             *)
(*             (HC:P a1..an H) =>                                     *)
(*           match H in I _.._ a1..an return P a1..an H -> P b1..bn C *)
(*           with                                                     *)
(*             C => fun x => x                                        *)
(*           end HC                                                   *)
(*      : forall q1..pm a1..an (H:I q1..qm a1..an)                    *)
(*               (P:forall a1..an, I q1..qm a1..an -> kind),          *)
(*               P a1..an H -> P b1..bn C                             *)
(*                                                                    *)
(* Note that the dependent elimination in ind_rd is not a dependency  *)
(* in the conclusion of the scheme but a dependency in the premise of *)
(* the scheme. This is unfortunately incompatible with the standard   *)
(* pattern for schemes in Coq which expects that the eliminated       *)
(* object is the last premise of the scheme. We then have no choice   *)
(* than following the more liberal pattern of having the eliminated   *)
(* object coming before the premises.                                 *)
(**********************************************************************)

let build_l2r_forward_rew_scheme dep env ind kind =
  let ((mib,mip as specif),constrargs,realsign,nrealargs) =
    get_non_sym_eq_data env ind in
  let cstr n =
    mkApp (mkConstruct(ind,1),extended_rel_vect n mib.mind_params_ctxt) in
  let constrargs_cstr = constrargs@[cstr 0] in
  let varH = fresh env (default_id_of_sort (snd (mind_arity mip))) in
  let varHC = fresh env (id_of_string "HC") in
  let varP = fresh env (id_of_string "P") in
  let applied_ind = build_dependent_inductive ind specif in
  let realsign_ind =
    name_context env ((Name varH,None,applied_ind)::realsign) in
  let s = mkSort (new_sort_in_family kind) in
  let ci = make_case_info (Global.env()) ind RegularStyle in
  let applied_PC =
    applist (mkVar varP,if dep then constrargs_cstr else constrargs) in
  let applied_PG =
    mkApp (mkVar varP,
           if dep then extended_rel_vect 0 realsign_ind
	   else extended_rel_vect 1 realsign) in
  (my_it_mkLambda_or_LetIn mib.mind_params_ctxt
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

(**********************************************************************)
(* This function "repairs" the non-dependent l2r forward rewriting    *)
(* scheme by making it comply with the standard pattern of schemes    *)
(* in Coq. Otherwise said, it turns a scheme of type                  *)
(*                                                                    *)
(*  forall q1..pm a1..an (H:I q1..qm a1..an)                          *)
(*         (P:forall a1..an, I q1..qm a1..an -> kind),                *)
(*         P a1..an H -> P b1..bn C                                   *)
(*                                                                    *)
(* into a scheme of type                                              *)
(*                                                                    *)
(*  forall q1..pm a1..an (P:forall a1..an, I q1..qm a1..an -> kind),  *)
(*         P a1..an H -> forall (H:I q1..qm a1..an), P b1..bn C       *)
(*                                                                    *)
(**********************************************************************)

let fix_l2r_forward_rew_scheme c =
  let t = Retyping.get_type_of (Global.env()) Evd.empty c in
  let ctx,_ = decompose_prod_assum t in
  match ctx with
  | hp :: p :: ind :: indargs ->
      my_it_mkLambda_or_LetIn indargs
	(mkLambda_or_LetIn (map_rel_declaration (liftn (-1) 1) p)
	  (mkLambda_or_LetIn (map_rel_declaration (liftn (-1) 2) hp)
	    (mkLambda_or_LetIn (map_rel_declaration (lift 2) ind)
	      (Reductionops.whd_beta Evd.empty
		(applist (c,
	          extended_rel_list 3 indargs @ [mkRel 1;mkRel 3;mkRel 2]))))))
  | _ -> anomaly "Ill-formed non-dependent left-to-right rewriting scheme"

(**********************************************************************)

let build_r2l_rew_scheme dep env ind k =
  build_case_analysis_scheme env Evd.empty ind dep k

(* Dependent rewrite from left-to-right in conclusion *)
let rew_l2r_dep_scheme_kind =
  declare_individual_scheme_object "_rew_r_dep"
  (fun ind -> build_l2r_rew_scheme true (Global.env()) ind InType)

(* Dependent rewrite from left-to-right in hypotheses *)
let rew_l2r_forward_dep_scheme_kind =
  declare_individual_scheme_object "_rew_fwd_dep"
  (fun ind -> build_l2r_forward_rew_scheme true (Global.env()) ind InType)

(* Dependent rewrite from right-to-left in conclusion *)
let rew_r2l_dep_scheme_kind =
  declare_individual_scheme_object "_rew_dep"
  (fun ind -> build_r2l_rew_scheme true (Global.env()) ind InType)

(* Dependent rewrite from right-to-left in hypotheses *)
let rew_r2l_forward_dep_scheme_kind =
  declare_individual_scheme_object "_rew_fwd_r_dep"
  (fun ind -> build_r2l_forward_rew_scheme true (Global.env()) ind InType)

(* Rewrite from left-to-right in conclusion and right-to-left in hypotheses *)
let rew_l2r_scheme_kind =
  declare_individual_scheme_object "_rew_r"
  (fun ind ->
    (* We cannot use the simply-proved build_l2r_forward_rew_scheme *)
    (* because it is introduced a beta-expansion blocked by the match *)
    (* and may thus block in turn guard condition *)
    build_l2r_rew_scheme false (Global.env()) ind InType)

(* Asymmetric rewrite in hypotheses *)
let rew_asym_scheme_kind =
  declare_individual_scheme_object "_rew_r_asym"
  (fun ind ->
    (* For the asymmetrical non-dependent case, we (currently) have only *)
    (* build_l2r_forward_rew_scheme available, though it may break the   *)
    (* guard condition due to the introduction of a beta-expansion       *)
    (* blocked by a match.                                               *)
    (* Moreover, its standard form needs the inductive hypothesis not    *)
    (* in last position what breaks the order of goals and need a fix!   *)
    fix_l2r_forward_rew_scheme
      (build_l2r_forward_rew_scheme false (Global.env()) ind InType))

(* Rewrite from right-to-left in conclusion and left-to-right in hypotheses *)
let rew_r2l_scheme_kind =
  declare_individual_scheme_object "_rew"
  (fun ind -> build_r2l_rew_scheme false (Global.env()) ind InType)

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

let build_congr env (eq,refl) ind =
  let (mib,mip) = lookup_mind_specif env ind in
  if Array.length mib.mind_packets <> 1 or Array.length mip.mind_nf_lc <> 1 then
    error "Not an inductive type with a single constructor.";
  if mip.mind_nrealargs <> 1 then
    error "Expect an inductive type with one predicate parameter.";
  let i = 1 in
  let realsign,_ = list_chop mip.mind_nrealargs_ctxt mip.mind_arity_ctxt in
  if List.exists (fun (_,b,_) -> b <> None) realsign then
    error "Inductive equalities with local definitions in arity not supported.";
  let env_with_arity = push_rel_context mip.mind_arity_ctxt env in
  let (_,_,ty) = lookup_rel (mip.mind_nrealargs - i + 1) env_with_arity in
  let constrsign,ccl = decompose_prod_assum mip.mind_nf_lc.(0) in
  let _,constrargs = decompose_app ccl in
  if rel_context_length constrsign<>rel_context_length mib.mind_params_ctxt then
    error "Constructor must have no arguments";
  let b = List.nth constrargs (i + mib.mind_nparams - 1) in
  let varB = fresh env (id_of_string "B") in
  let varH = fresh env (id_of_string "H") in
  let varf = fresh env (id_of_string "f") in
  let ci = make_case_info (Global.env()) ind RegularStyle in
  my_it_mkLambda_or_LetIn mib.mind_params_ctxt
     (mkNamedLambda varB (new_Type ())
     (mkNamedLambda varf (mkArrow (lift 1 ty) (mkVar varB))
     (my_it_mkLambda_or_LetIn_name (lift_rel_context 2 realsign)
     (mkNamedLambda varH
        (applist
           (mkInd ind,
	    extended_rel_list (mip.mind_nrealargs+2) mib.mind_params_ctxt @
	    extended_rel_list 0 realsign))
     (mkCase (ci,
       my_it_mkLambda_or_LetIn_name
	 (lift_rel_context (mip.mind_nrealargs+3) realsign)
         (mkLambda
           (Anonymous,
            applist
             (mkInd ind,
	        extended_rel_list (2*mip.mind_nrealargs_ctxt+3)
		  mib.mind_params_ctxt
	        @ extended_rel_list 0 realsign),
            mkApp (eq,
	      [|mkVar varB;
                mkApp (mkVar varf, [|lift (2*mip.mind_nrealargs_ctxt+4) b|]);
		mkApp (mkVar varf, [|mkRel (mip.mind_nrealargs - i + 2)|])|]))),
       mkVar varH,
       [|mkApp (refl,
          [|mkVar varB;
	    mkApp (mkVar varf, [|lift (mip.mind_nrealargs+3) b|])|])|]))))))

let congr_scheme_kind = declare_individual_scheme_object "_congr"
  (fun ind ->
    (* May fail if equality is not defined *)
    build_congr (Global.env()) (get_coq_eq ()) ind)
