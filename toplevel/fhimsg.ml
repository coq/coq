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
open Identifier
open Names
open Term
open Sign
open Environ
open Indtypes
open Type_errors
open Reduction
open G_minicoq

module type Printer = sig
  val pr_term : env -> constr -> std_ppcmds
end

module Make = functor (P : Printer) -> struct

  let print_decl env (s,typ) =
    let ptyp = P.pr_term env (body_of_type typ) in 
    (**)(  spc () ++ pr_id s ++ str" : " ++ ptyp  )(**)
  
  let print_binding env = function
    | Anonymous,ty -> 
	(**)(  spc () ++ str"_"  ++ str" : "  ++ P.pr_term env (body_of_type ty)  )(**)
    | Name id,ty -> 
	(**)(  spc () ++ pr_id id  ++ str" : " ++ P.pr_term env (body_of_type ty)  )(**)

(****
  let sign_it_with f sign e =
    snd (fold_named_context
	   (fun (id,v,t) (sign,e) -> (add_named_decl (id,v,t) sign, f id t sign e))
           sign (empty_named_context,e))

  let dbenv_it_with f env e =
    snd (dbenv_it 
	   (fun na t (env,e) -> (add_rel_decl (na,t) env, f na t env e))
           env (gLOB(get_globals env),e))
****)
      
  let pr_env env =
    let sign_env =
      fold_named_context
	(fun env (id,_,t) pps ->
           let pidt =  print_decl env (id,t) in (**)(   pps  ++ fnl ()  ++ pidt  )(**))
	env (mt ()) 
    in
    let db_env =
      fold_rel_context
	(fun env (na,_,t) pps ->
           let pnat = print_binding env (na,t) in (**)(   pps  ++ fnl ()  ++ pnat  )(**))
	env (mt ())
    in 
    (**)(  sign_env ++ db_env  )(**)
    
  let pr_ne_ctx header env =
    if rel_context env = [] && named_context env = [] then
      (mt ())
    else
      (**)(  header ++ pr_env env  )(**)


let explain_unbound_rel ctx n =
  let pe = pr_ne_ctx (**)(  str"in environment"  )(**) ctx in
  (**)(  str"Unbound reference: " ++ pe ++ fnl () ++
     str"The reference " ++ int n ++ str" is free"  )(**)

let explain_not_type ctx c =
  let pe = pr_ne_ctx (**)(  str"In environment"  )(**) ctx in
  let pc = P.pr_term ctx c in
  (**)(  pe ++ fnl () ++ str "the term" ++ brk(1,1) ++ pc ++ spc () ++
     str"should be typed by Set, Prop or Type."  )(**);;

let explain_bad_assumption ctx c =
  let pc = P.pr_term ctx c in
  (**)(  str "Cannot declare a variable or hypothesis over the term" ++
     brk(1,1) ++ pc ++ spc () ++ str "because this term is not a type."  )(**);;

let explain_reference_variables id =
  (**)(  str "the constant" ++ spc () ++ pr_id id ++ spc () ++ 
     str "refers to variables which are not in the context"  )(**)

let msg_bad_elimination ctx = function
  | Some(ki,kp,explanation) ->
      let pki = P.pr_term ctx ki in
      let pkp = P.pr_term ctx kp in
      (hov 0 
         (**)(  fnl () ++ str "Elimination of an inductive object of sort : " ++
            pki ++ brk(1,0) ++
            str "is not allowed on a predicate in sort : " ++ pkp  ++fnl () ++
            str "because" ++ spc () ++ str explanation  )(**))
  | None -> 
      (mt ())

let explain_elim_arity ctx ind aritylst c pj okinds = 
  let pi = P.pr_term ctx ind in
  let ppar = prlist_with_sep pr_coma (P.pr_term ctx) aritylst in
  let pc = P.pr_term ctx c in
  let pp = P.pr_term ctx pj.uj_val in
  let ppt = P.pr_term ctx pj.uj_type in
  (**)(  str "Incorrect elimination of" ++ brk(1,1) ++ pc ++ spc () ++
     str "in the inductive type" ++ brk(1,1) ++ pi ++ fnl () ++
     str "The elimination predicate" ++ brk(1,1) ++ pp ++ spc () ++
     str "has type" ++ brk(1,1) ++ ppt ++ fnl () ++
     str "It should be one of :" ++ brk(1,1)  ++ hov 0 ppar ++ fnl () ++
     msg_bad_elimination ctx okinds  )(**)

let explain_case_not_inductive ctx cj =
  let pc = P.pr_term ctx cj.uj_val in
  let pct = P.pr_term ctx cj.uj_type in
  (**)(  str "In Cases expression" ++ brk(1,1) ++ pc ++ spc () ++ 
     str "has type" ++ brk(1,1) ++ pct ++ spc () ++ 
     str "which is not an inductive definition"  )(**)
  
let explain_number_branches ctx cj expn =
  let pc = P.pr_term ctx cj.uj_val in
  let pct = P.pr_term ctx cj.uj_type in
  (**)(  str "Cases on term" ++ brk(1,1) ++ pc ++ spc ()  ++
     str "of type" ++ brk(1,1) ++ pct ++ spc () ++
     str "expects " ++  int expn ++ str " branches"  )(**)

let explain_ill_formed_branch ctx c i actty expty =
  let pc = P.pr_term ctx c in
  let pa = P.pr_term ctx actty in
  let pe = P.pr_term ctx expty in
  (**)(  str "In Cases expression on term" ++ brk(1,1) ++ pc ++
     spc () ++ str "the branch "  ++ int (i+1) ++
     str " has type" ++ brk(1,1) ++ pa  ++ spc () ++ 
     str "which should be:" ++ brk(1,1) ++ pe  )(**)

let explain_generalization ctx (name,var) c =
  let pe = pr_ne_ctx (**)(  str"in environment"  )(**) ctx in
  let pv = P.pr_term ctx (body_of_type var) in
  let pc = P.pr_term (push_rel (name,None,var) ctx) c in
  (**)(  str"Illegal generalization: " ++ pe ++ fnl () ++
     str"Cannot generalize" ++ brk(1,1) ++ pv ++ spc () ++
     str"over" ++ brk(1,1) ++ pc ++ spc () ++
     str"which should be typed by Set, Prop or Type."  )(**)

let explain_actual_type ctx c ct pt =
  let pe = pr_ne_ctx (**)(  str"In environment"  )(**) ctx in
  let pc = P.pr_term ctx c in
  let pct = P.pr_term ctx ct in
  let pt = P.pr_term ctx pt in
  (**)(  pe ++ fnl () ++
     str"The term" ++ brk(1,1) ++ pc  ++ spc ()  ++
     str"does not have type" ++ brk(1,1) ++ pt ++ fnl () ++
     str"Actually, it has type"  ++ brk(1,1) ++ pct  )(**)

let explain_cant_apply_bad_type ctx (n,exptyp,actualtyp) rator randl =
(*  let ctx = make_all_name_different ctx in *)
  let pe = pr_ne_ctx (**)(  str"in environment"  )(**) ctx in
  let pr = pr_term ctx rator.uj_val in
  let prt = pr_term ctx (body_of_type rator.uj_type) in
  let term_string = if List.length randl > 1 then "terms" else "term" in
  let many = match n mod 10 with 1 -> "st" | 2 -> "nd" | _ -> "th" in
  let appl = prlist_with_sep pr_fnl 
	       (fun c ->
		  let pc = pr_term ctx c.uj_val in
		  let pct = pr_term ctx (body_of_type c.uj_type) in
		  hov 2 (**)(  pc ++ spc () ++ str": "  ++ pct  )(**)) randl
  in
  (**)(  str"Illegal application (Type Error): " ++ pe ++ fnl () ++
     str"The term" ++ brk(1,1) ++ pr ++ spc () ++
     str"of type" ++ brk(1,1) ++ prt ++ spc ()  ++
     str("cannot be applied to the "^term_string) ++ fnl () ++ 
     str" " ++ v 0 appl ++ fnl () ++
     str"The " ++int n ++ str (many^" term of type ") ++
     pr_term ctx actualtyp ++
     str" should be of type " ++ pr_term ctx exptyp  )(**)

let explain_cant_apply_not_functional ctx rator randl =
(*  let ctx = make_all_name_different ctx in *)
  let pe = pr_ne_ctx (**)(  str"in environment"  )(**) ctx in
  let pr = pr_term ctx rator.uj_val in
  let prt = pr_term ctx (body_of_type rator.uj_type) in
  let term_string = if List.length randl > 1 then "terms" else "term" in
  let appl = prlist_with_sep pr_fnl 
	       (fun c ->
		  let pc = pr_term ctx c.uj_val in
		  let pct = pr_term ctx (body_of_type c.uj_type) in
		  hov 2 (**)(  pc ++ spc () ++ str": "  ++ pct  )(**)) randl
  in
  (**)(  str"Illegal application (Non-functional construction): " ++ pe ++ fnl () ++
     str"The term" ++ brk(1,1) ++ pr ++ spc () ++
     str"of type" ++ brk(1,1) ++ prt ++ spc ()  ++
     str("cannot be applied to the "^term_string) ++ fnl () ++ 
     str" " ++ v 0 appl ++ fnl ()  )(**)

(* (co)fixpoints *)
let explain_ill_formed_rec_body ctx err lna i vdefs =
  let str = match err with

  (* Fixpoint guard errors *)
  | NotEnoughAbstractionInFixBody ->
      (**)(  str "Not enough abstractions in the definition"  )(**)
  | RecursionNotOnInductiveType ->
      (**)(  str "Recursive definition on a non inductive type"  )(**)
  | RecursionOnIllegalTerm ->
      (**)(  str "Recursive call applied to an illegal term"  )(**)
  | NotEnoughArgumentsForFixCall ->
      (**)(  str "Not enough arguments for the recursive call"  )(**)

  (* CoFixpoint guard errors *)
  (* TODO : récupérer le contexte des termes pour pouvoir les afficher *)
  | CodomainNotInductiveType c ->
      (**)(  str "The codomain is" ++ spc () ++ P.pr_term ctx c ++ spc () ++
	 str "which should be a coinductive type"  )(**)
  | NestedRecursiveOccurrences ->
      (**)(  str "Nested recursive occurrences"  )(**)
  | UnguardedRecursiveCall c ->
      (**)(  str "Unguarded recursive call"  )(**)
  | RecCallInTypeOfAbstraction c ->
      (**)(  str "Not allowed recursive call in the domain of an abstraction"  )(**)
  | RecCallInNonRecArgOfConstructor c ->
      (**)(  str "Not allowed recursive call in a non-recursive argument of constructor"  )(**)
  | RecCallInTypeOfDef c ->
      (**)(  str "Not allowed recursive call in the type of a recursive definition"  )(**)
  | RecCallInCaseFun c ->
      (**)(  str "Not allowed recursive call in a branch of cases"  )(**)
  | RecCallInCaseArg c -> 
      (**)(  str "Not allowed recursive call in the argument of cases"  )(**)
  | RecCallInCasePred c ->
      (**)(  str "Not allowed recursive call in the type of cases in"  )(**)
  | NotGuardedForm ->
      (**)(  str "Definition not in guarded form"  )(**)
in
  let pvd = P.pr_term ctx vdefs.(i) in
  let s =
    match lna.(i) with Name id -> string_of_id id | Anonymous -> "_" in
  ( str; fnl (); str"The ";
     if Array.length vdefs = 1 then (mt ()) else (**)( int (i+1) ++ str "-th " )(**) ++
     str"recursive definition" ++ spc () ++ str s ++
	 spc () ++ str":=" ++ spc () ++ pvd ++ spc () ++
     str "is not well-formed" )
    
let explain_ill_typed_rec_body ctx i lna vdefj vargs =
  let pvd = P.pr_term ctx (vdefj.(i)).uj_val in
  let pvdt = P.pr_term ctx (body_of_type (vdefj.(i)).uj_type) in
  let pv = P.pr_term ctx (body_of_type vargs.(i)) in
  ( str"The " ++
     if Array.length vdefj = 1 then (mt ()) else (**)( int (i+1) ++ str "-th" )(**);
     str"recursive definition" ++ spc () ++ pvd ++ spc () ++
     str "has type" ++ spc () ++ pvdt ++ spc ()++ str "it should be" ++ spc () ++ pv )

let explain_not_inductive ctx c =
  let pc = P.pr_term ctx c in
  (**)(  str"The term" ++ brk(1,1) ++ pc ++ spc () ++
     str "is not an inductive definition"  )(**)

let explain_ml_case ctx mes c ct br brt =
  let pc = P.pr_term ctx c in
  let pct = P.pr_term ctx ct in
  let expln =
    match mes with
      | "Inductive" -> (**)(  pct ++ str "is not an inductive definition" )(**)
      | "Predicate" -> (**)(  str "ML case not allowed on a predicate" )(**)
      | "Absurd" -> (**)(  str "Ill-formed case expression on an empty type"  )(**)
      | "Decomp" ->
          let plf = P.pr_term ctx br in
          let pft = P.pr_term ctx brt in
          (**)(  str "The branch " ++ plf ++ ws 1 ++ cut () ++ str "has type " ++ pft ++
             ws 1 ++ cut () ++
             str "does not correspond to the inductive definition"  )(**)
      | "Dependent" ->
          (**)(  str "ML case not allowed for a dependent case elimination" )(**)
      | _ -> (mt ())
  in
  hov 0 (**)(  str "In ML case expression on " ++ pc ++ ws 1 ++ cut ()  ++
           str "of type" ++  ws 1 ++ pct ++ ws 1 ++ cut () ++ 
           str "which is an inductive predicate." ++ fnl () ++ expln  )(**)
(*
let explain_cant_find_case_type loc ctx c =
  let pe = P.pr_term ctx c in
  Ast.user_err_loc
    (loc,"pretype",
     hov 3 (**)( str "Cannot infer type of whole Case expression on" ++ 
	     ws 1 ++ pe  )(**))
*)
let explain_type_error ctx = function
  | UnboundRel n -> 
      explain_unbound_rel ctx n
  | NotAType c -> 
      explain_not_type ctx c.uj_val
  | BadAssumption c -> 
      explain_bad_assumption ctx c
  | ReferenceVariables id -> 
      explain_reference_variables id
  | ElimArity (ind, aritylst, c, pj, okinds) ->
      explain_elim_arity ctx (mkMutInd ind) aritylst c pj okinds 
  | CaseNotInductive cj -> 
      explain_case_not_inductive ctx cj
  | NumberBranches (cj, n) -> 
      explain_number_branches ctx cj n
  | IllFormedBranch (c, i, actty, expty) -> 
      explain_ill_formed_branch ctx c i actty expty 
  | Generalization (nvar, c) ->
      explain_generalization ctx nvar c.uj_val
  | ActualType (c, ct, pt) -> 
      explain_actual_type ctx c ct pt
  | CantApplyBadType (s, rator, randl) ->
      explain_cant_apply_bad_type ctx s rator randl
  | CantApplyNonFunctional (rator, randl) ->
      explain_cant_apply_not_functional ctx rator randl
  | IllFormedRecBody (i, lna, vdefj, vargs) ->
      explain_ill_formed_rec_body ctx i lna vdefj vargs
  | IllTypedRecBody (i, lna, vdefj, vargs) ->
      explain_ill_typed_rec_body ctx i lna vdefj vargs
(*
  | NotInductive c ->
      explain_not_inductive ctx c
  | MLCase (mes,c,ct,br,brt) ->
      explain_ml_case ctx mes c ct br brt
*)
  | _ -> 
      (**)(  str "Unknown type error (TODO)"  )(**)

let explain_refiner_bad_type ctx arg ty conclty =
  errorlabstrm "Logic.conv_leq_goal"
    (**)(  str"refiner was given an argument" ++ brk(1,1) ++ 
       P.pr_term ctx arg ++ spc () ++
       str"of type" ++ brk(1,1) ++ P.pr_term ctx ty ++ spc () ++
       str"instead of" ++ brk(1,1) ++ P.pr_term ctx conclty  )(**)

let explain_refiner_occur_meta ctx t =
  errorlabstrm "Logic.mk_refgoals"
    (**)(  str"cannot refine with term" ++ brk(1,1) ++ P.pr_term ctx t ++
       spc () ++ str"because there are metavariables, and it is" ++
       spc () ++ str"neither an application nor a Case"  )(**)

let explain_refiner_cannot_applt ctx t harg =
  errorlabstrm "Logic.mkARGGOALS"
    (**)(  str"in refiner, a term of type " ++ brk(1,1) ++
       P.pr_term ctx t ++ spc () ++ str"could not be applied to" ++ brk(1,1) ++
       P.pr_term ctx harg  )(**)

let explain_occur_check ctx ev rhs =
  let id = "?" ^ string_of_int ev in
  let pt = P.pr_term ctx rhs in
  errorlabstrm "Trad.occur_check"
    (**)(  str"Occur check failed: tried to define " ++ str id ++
      str" with term" ++ brk(1,1) ++ pt  )(**)

let explain_not_clean ctx sp t =
  let c = mkRel (Intset.choose (free_rels t)) in
  let id = string_of_id (basename sp) in
  let var = P.pr_term ctx c in
  errorlabstrm "Trad.not_clean"
    (**)(  str"Tried to define " ++ str id ++
       str" with a term using variable " ++ var ++ spc () ++
       str"which is not in its scope."  )(**)
    
let inductive_error_to_string = function
  (* These are errors related to inductive constructions *)
  | NonPos (env,c,v) -> "error_non_strictly_positive CCI env c v"
  | NotEnoughArgs (env,c,v) -> "error_ill_formed_inductive CCI env c v"
  | NotConstructor (env,c,v) -> "error_ill_formed_constructor CCI env c v"
  | NonPar (env,c,n,v1,v2) -> "error_bad_ind_parameters CCI env c n v1 v2"
  | SameNamesTypes id -> "error_same_names_types id"
  | SameNamesConstructors (id,cid) -> "error_same_names_constructors id cid"
  | SameNamesOverlap idl -> "error_same_names_overlap idl"
  | NotAnArity id -> "error_not_an_arity id"
  | BadEntry -> "error_bad_entry ()"
  (* These are errors related to recursors *)
  | NotAllowedCaseAnalysis (dep,k,i) -> "error_not_allowed_case_analysis dep k i"
  | BadInduction (dep,indid,kind) -> "error_bad_induction dep indid kind"
  | NotMutualInScheme -> "error_not_mutual_in_scheme ()"

let explain_inductive_error exn = 
  let explanation = inductive_error_to_string exn in
  hov 0 (**)(  str explanation  )(**)

end
