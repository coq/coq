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
open Options
open Identifier
open Names
open Term
open Inductive
open Indtypes
open Sign
open Environ
open Pretype_errors
open Type_errors
open Reduction
open Cases
open Logic
open Printer
open Ast

let guill s = "\""^s^"\""

let explain_unbound_rel ctx n =
  let ctx = make_all_name_different ctx in 
  let pe = pr_ne_context_of [< 'sTR "In environment" >] ctx in
  [< 'sTR"Unbound reference: "; pe;
     'sTR"The reference "; 'iNT n; 'sTR" is free" >]

let explain_not_type ctx j =
  let ctx = make_all_name_different ctx in
  let pe = pr_ne_context_of [< 'sTR"In environment" >] ctx in
  let pc,pt = prjudge_env ctx j in
  [< pe; 'sTR "the term"; 'bRK(1,1); pc; 'sPC;
     'sTR"has type"; 'sPC; pt; 'sPC; 
     'sTR"which should be Set, Prop or Type." >];;

let explain_bad_assumption ctx c =
  let pc = prterm_env ctx c in
  [< 'sTR "Cannot declare a variable or hypothesis over the term";
     'bRK(1,1); pc; 'sPC; 'sTR "because this term is not a type." >];;

let explain_reference_variables id =
  [< 'sTR "the constant"; 'sPC; pr_id id; 'sPC; 
     'sTR "refers to variables which are not in the context" >]

let msg_bad_elimination ctx = function
  | Some(kp,ki,explanation) ->
      let pki = prterm_env ctx ki in
      let pkp = prterm_env ctx kp in
      (hOV 0 
         [< 'fNL; 'sTR "Elimination of an inductive object of sort : ";
            pki; 'bRK(1,0);
            'sTR "is not allowed on a predicate in sort : "; pkp ;'fNL;
            'sTR "because"; 'sPC; 'sTR explanation >])
  | None -> 
      [<>]

let explain_elim_arity ctx ind aritylst c pj okinds = 
  let pi = pr_inductive ctx ind in
  let ppar = prlist_with_sep pr_coma (prterm_env ctx) aritylst in
  let pc = prterm_env ctx c in
  let pp = prterm_env ctx pj.uj_val in
  let ppt = prterm_env ctx pj.uj_type in
  [< 'sTR "Incorrect elimination of"; 'bRK(1,1); pc; 'sPC;
     'sTR "in the inductive type"; 'bRK(1,1); pi; 'fNL;
     'sTR "The elimination predicate"; 'bRK(1,1); pp; 'sPC;
     'sTR "has type"; 'bRK(1,1); ppt; 'fNL;
     'sTR "It should be one of :"; 'bRK(1,1) ; hOV 0 ppar; 'fNL;
     msg_bad_elimination ctx okinds >]

let explain_case_not_inductive ctx cj =
  let pc = prterm_env ctx cj.uj_val in
  let pct = prterm_env ctx cj.uj_type in
  [< 'sTR "In Cases expression, the matched term"; 'bRK(1,1); pc; 'sPC; 
     'sTR "has type"; 'bRK(1,1); pct; 'sPC; 
     'sTR "which is not a (co-)inductive type" >]
  
let explain_number_branches ctx cj expn =
  let pc = prterm_env ctx cj.uj_val in
  let pct = prterm_env ctx cj.uj_type in
  [< 'sTR "Cases on term"; 'bRK(1,1); pc; 'sPC ;
     'sTR "of type"; 'bRK(1,1); pct; 'sPC;
     'sTR "expects ";  'iNT expn; 'sTR " branches" >]

let explain_ill_formed_branch ctx c i actty expty =
  let pc = prterm_env ctx c in
  let pa = prterm_env ctx actty in
  let pe = prterm_env ctx expty in
  [< 'sTR "In Cases expression on term"; 'bRK(1,1); pc;
     'sPC; 'sTR "the branch " ; 'iNT (i+1);
     'sTR " has type"; 'bRK(1,1); pa ; 'sPC; 
     'sTR "which should be"; 'bRK(1,1); pe >]

let explain_generalization ctx (name,var) j =
  let ctx = make_all_name_different ctx in
  let pe = pr_ne_context_of [< 'sTR "In environment" >] ctx in
  let pv = prtype_env ctx var in
  let (pc,pt) = prjudge_env (push_rel_assum (name,var) ctx) j in
  [< 'sTR"Illegal generalization: "; pe;
     'sTR"Cannot generalize"; 'bRK(1,1); pv; 'sPC;
     'sTR"over"; 'bRK(1,1); pc; 'sTR","; 'sPC; 'sTR"it has type"; 'sPC; pt; 
     'sPC; 'sTR"which should be Set, Prop or Type." >]

let explain_actual_type ctx c ct pt =
  let ctx = make_all_name_different ctx in
  let pe = pr_ne_context_of [< 'sTR "In environment" >] ctx in
  let pc = prterm_env ctx c in
  let pct = prterm_env ctx ct in
  let pt = prterm_env ctx pt in
  [< pe;
     'sTR "The term"; 'bRK(1,1); pc ; 'sPC ;
     'sTR "has type" ; 'bRK(1,1); pct; 'bRK(1,1); 
     'sTR "while it is expected to have type"; 'bRK(1,1); pt >]

let explain_cant_apply_bad_type ctx (n,exptyp,actualtyp) rator randl =
  let ctx = make_all_name_different ctx in
(*  let pe = pr_ne_context_of [< 'sTR"in environment" >] ctx in*)
  let pr,prt = prjudge_env ctx rator in
  let term_string1,term_string2 =
    if List.length randl > 1 then
      let many = match n mod 10 with 1 -> "st" | 2 -> "nd" | _ -> "th" in
      "terms", "The "^(string_of_int n)^many^" term"
    else
      "term","This term" in
  let appl = prlist_with_sep pr_fnl 
	       (fun c ->
		  let pc,pct = prjudge_env ctx c in
		  hOV 2 [< pc; 'sPC; 'sTR": " ; pct >]) randl
  in
  [< 'sTR"Illegal application (Type Error): "; (* pe; *) 'fNL;
     'sTR"The term"; 'bRK(1,1); pr; 'sPC;
     'sTR"of type"; 'bRK(1,1); prt; 'sPC ;
     'sTR("cannot be applied to the "^term_string1); 'fNL; 
     'sTR" "; v 0 appl; 'fNL; 'sTR (term_string2^" has type");
     'bRK(1,1); prterm_env ctx actualtyp; 'sPC;
     'sTR"which should be coercible to"; 'bRK(1,1); prterm_env ctx exptyp >]

let explain_cant_apply_not_functional ctx rator randl =
  let ctx = make_all_name_different ctx in
(*  let pe = pr_ne_context_of [< 'sTR"in environment" >] ctx in*)
  let pr = prterm_env ctx rator.uj_val in
  let prt = prterm_env ctx (body_of_type rator.uj_type) in
  let term_string = if List.length randl > 1 then "terms" else "term" in
  let appl = prlist_with_sep pr_fnl 
	       (fun c ->
		  let pc = prterm_env ctx c.uj_val in
		  let pct = prterm_env ctx (body_of_type c.uj_type) in
		  hOV 2 [< pc; 'sPC; 'sTR": " ; pct >]) randl
  in
  [< 'sTR"Illegal application (Non-functional construction): "; (* pe; *) 'fNL;
     'sTR"The expression"; 'bRK(1,1); pr; 'sPC;
     'sTR"of type"; 'bRK(1,1); prt; 'sPC ;
     'sTR("cannot be applied to the "^term_string); 'fNL; 
     'sTR" "; v 0 appl >]

let explain_unexpected_type ctx actual_type expected_type =
  let ctx = make_all_name_different ctx in
  let pract = prterm_env ctx actual_type in
  let prexp = prterm_env ctx expected_type in
  [< 'sTR"This type is"; 'sPC; pract; 'sPC; 'sTR "but is expected to be";
     'sPC; prexp >]

let explain_not_product ctx c =
  let ctx = make_all_name_different ctx in
  let pr = prterm_env ctx c in
  [< 'sTR"The type of this term is a product,"; 'sPC;
     'sTR"but it is casted with type";
     'bRK(1,1); pr >]

(* TODO: use the names *)
(* (co)fixpoints *)
let explain_ill_formed_rec_body ctx err names i vdefs =
  let str = match err with

  (* Fixpoint guard errors *)
  | NotEnoughAbstractionInFixBody ->
      [< 'sTR "Not enough abstractions in the definition" >]
  | RecursionNotOnInductiveType ->
      [< 'sTR "Recursive definition on a non inductive type" >]
  | RecursionOnIllegalTerm ->
      [< 'sTR "Recursive call applied to an illegal term" >]
  | NotEnoughArgumentsForFixCall ->
      [< 'sTR "Not enough arguments for the recursive call" >]

  (* CoFixpoint guard errors *)
  (* TODO : r�cup�rer le contexte des termes pour pouvoir les afficher *)
  | CodomainNotInductiveType c ->
      [< 'sTR "The codomain is"; 'sPC; prterm c; 'sPC;
	 'sTR "which should be a coinductive type" >]
  | NestedRecursiveOccurrences ->
      [< 'sTR "Nested recursive occurrences" >]
  | UnguardedRecursiveCall c ->
      [< 'sTR "Unguarded recursive call" >]
  | RecCallInTypeOfAbstraction c ->
      [< 'sTR "Not allowed recursive call in the domain of an abstraction" >]
  | RecCallInNonRecArgOfConstructor c ->
      [< 'sTR "Not allowed recursive call in a non-recursive argument of constructor" >]
  | RecCallInTypeOfDef c ->
      [< 'sTR "Not allowed recursive call in the type of a recursive definition" >]
  | RecCallInCaseFun c ->
      [< 'sTR "Not allowed recursive call in a branch of cases" >]
  | RecCallInCaseArg c -> 
      [< 'sTR "Not allowed recursive call in the argument of cases" >]
  | RecCallInCasePred c ->
      [< 'sTR "Not allowed recursive call in the type of cases in" >]
  | NotGuardedForm ->
      [< 'sTR "Definition not in guarded form" >]
  in
  let pvd = prterm_env ctx vdefs.(i) in
  let s =
    match names.(i) with Name id -> string_of_id id | Anonymous -> "_" in
  [< str; 'fNL; 'sTR"The ";
     if Array.length vdefs = 1 then [<>] else [<'iNT (i+1); 'sTR "-th ">];
     'sTR"recursive definition"; 'sPC; 'sTR s;
	 'sPC ; 'sTR":="; 'sPC ; pvd; 'sPC;
     'sTR "is not well-formed" >]

let explain_ill_typed_rec_body ctx i names vdefj vargs =
  let pvd,pvdt = prjudge_env ctx (vdefj.(i)) in
  let pv = prterm_env ctx (body_of_type vargs.(i)) in
  [< 'sTR"The " ;
     if Array.length vdefj = 1 then [<>] else [<'iNT (i+1); 'sTR "-th">];
     'sTR"recursive definition" ; 'sPC; pvd; 'sPC;
     'sTR "has type"; 'sPC; pvdt;'sPC; 'sTR "it should be"; 'sPC; pv >]

let explain_not_inductive ctx c =
  let pc = prterm_env ctx c in
  [< 'sTR"The term"; 'bRK(1,1); pc; 'sPC;
     'sTR "is not an inductive definition" >]

let explain_ml_case ctx mes =
  let expln = match mes with
    | MlCaseAbsurd ->
	[< 'sTR "Unable to infer a predicate for an elimination an empty type">]
    | MlCaseDependent ->
        [< 'sTR "Unable to infer a dependent elimination predicate">]
  in
  hOV 0 [< 'sTR "Cannot infer ML Case predicate:"; 'fNL; expln >] 

let explain_cant_find_case_type ctx c =
  let pe = prterm_env ctx c in
  hOV 3 [<'sTR "Cannot infer type of whole Case expression on"; 'wS 1; pe >]

let explain_occur_check ctx ev rhs =
  let id = "?" ^ string_of_int ev in
  let pt = prterm_env ctx rhs in
  [< 'sTR"Occur check failed: tried to define "; 'sTR id;
     'sTR" with term"; 'bRK(1,1); pt >]

let explain_not_clean ctx ev t =
  let c = mkRel (Intset.choose (free_rels t)) in
  let id = "?" ^ string_of_int ev in
  let var = prterm_env ctx c in
  [< 'sTR"Tried to define "; 'sTR id;
     'sTR" with a term using variable "; var; 'sPC;
     'sTR"which is not in its scope." >]

let explain_var_not_found ctx id = 
  [< 'sTR "The variable"; 'sPC; 'sTR (string_of_id id);
     'sPC ; 'sTR "was not found"; 
     'sPC ; 'sTR "in the current"; 'sPC ; 'sTR "environment" >]

let explain_type_error ctx = function
  | UnboundRel n -> 
      explain_unbound_rel ctx n
  | NotAType j -> 
      explain_not_type ctx j
  | BadAssumption c -> 
      explain_bad_assumption ctx c
  | ReferenceVariables id -> 
      explain_reference_variables id
  | ElimArity (ind, aritylst, c, pj, okinds) ->
      explain_elim_arity ctx ind aritylst c pj okinds 
  | CaseNotInductive cj -> 
      explain_case_not_inductive ctx cj
  | NumberBranches (cj, n) -> 
      explain_number_branches ctx cj n
  | IllFormedBranch (c, i, actty, expty) -> 
      explain_ill_formed_branch ctx c i actty expty 
  | Generalization (nvar, c) ->
      explain_generalization ctx nvar c
  | ActualType (c, ct, pt) -> 
      explain_actual_type ctx c ct pt
  | CantApplyBadType (t, rator, randl) ->
      explain_cant_apply_bad_type ctx t rator randl
  | CantApplyNonFunctional (rator, randl) ->
      explain_cant_apply_not_functional ctx rator randl
  | IllFormedRecBody (i, lna, vdefj, vargs) ->
      explain_ill_formed_rec_body ctx i lna vdefj vargs
  | IllTypedRecBody (i, lna, vdefj, vargs) -> 
     explain_ill_typed_rec_body ctx i lna vdefj vargs
(*
  | NotInductive c ->
      explain_not_inductive ctx c
*)
let explain_pretype_error ctx = function
  | MlCase (mes,_,_) ->
      explain_ml_case ctx mes
  | CantFindCaseType c ->
      explain_cant_find_case_type ctx c
  | OccurCheck (n,c) ->
      explain_occur_check ctx n c
  | NotClean (n,c) ->
      explain_not_clean ctx n c
  | VarNotFound id ->
      explain_var_not_found ctx id
  | UnexpectedType (actual,expected) ->
      explain_unexpected_type ctx actual expected
  | NotProduct c ->
      explain_not_product ctx c

(* Refiner errors *)

let explain_refiner_bad_type arg ty conclty =
  [< 'sTR"refiner was given an argument"; 'bRK(1,1); 
     prterm arg; 'sPC;
     'sTR"of type"; 'bRK(1,1); prterm ty; 'sPC;
     'sTR"instead of"; 'bRK(1,1); prterm conclty >]

let explain_refiner_occur_meta t =
  [< 'sTR"cannot refine with term"; 'bRK(1,1); prterm t;
     'sPC; 'sTR"because there are metavariables, and it is";
     'sPC; 'sTR"neither an application nor a Case" >]

let explain_refiner_occur_meta_goal t =
  [< 'sTR"generated subgoal"; 'bRK(1,1); prterm t;
     'sPC; 'sTR"has metavariables in it" >]

let explain_refiner_cannot_applt t harg =
  [< 'sTR"in refiner, a term of type "; 'bRK(1,1);
     prterm t; 'sPC; 'sTR"could not be applied to"; 'bRK(1,1);
     prterm harg >]

let explain_refiner_cannot_unify m n =
  let pm = prterm m in 
  let pn = prterm n in
  [< 'sTR"Impossible to unify"; 'bRK(1,1) ; pm; 'sPC ;
     'sTR"with"; 'bRK(1,1) ; pn >]

let explain_refiner_cannot_generalize ty =
  [< 'sTR "Cannot find a well-typed generalisation of the goal with type : "; 
     prterm ty >]

let explain_refiner_not_well_typed c =
  [< 'sTR"The term " ; prterm c ; 'sTR" is not well-typed" >]

let explain_refiner_bad_tactic_args s l =
  [< 'sTR "Internal tactic "; 'sTR s; 'sTR " cannot be applied to ";
     Tacmach.pr_tactic (s,l) >]

let explain_intro_needs_product () =
  [< 'sTR "Introduction tactics needs products" >]

let explain_does_not_occur_in c hyp =
  [< 'sTR "The term"; 'sPC; prterm c; 'sPC; 'sTR "does not occur in";
     'sPC; pr_id hyp >]

let explain_non_linear_proof c =
  [< 'sTR "cannot refine with term"; 'bRK(1,1); prterm c;
     'sPC; 'sTR"because a metavariable has several occurrences" >]

let explain_refiner_error = function
  | BadType (arg,ty,conclty) -> explain_refiner_bad_type arg ty conclty
  | OccurMeta t -> explain_refiner_occur_meta t
  | OccurMetaGoal t -> explain_refiner_occur_meta_goal t
  | CannotApply (t,harg) -> explain_refiner_cannot_applt t harg
  | CannotUnify (m,n) -> explain_refiner_cannot_unify m n
  | CannotGeneralize ty -> explain_refiner_cannot_generalize ty
  | NotWellTyped c -> explain_refiner_not_well_typed c
  | BadTacticArgs (s,l) -> explain_refiner_bad_tactic_args s l
  | IntroNeedsProduct -> explain_intro_needs_product ()
  | DoesNotOccurIn (c,hyp) -> explain_does_not_occur_in c hyp
  | NonLinearProof c -> explain_non_linear_proof c

(* Inductive errors *)

let error_non_strictly_positive env c v  =
  let pc = prterm_env env c in
  let pv = prterm_env env v in
  [< 'sTR "Non strictly positive occurrence of "; pv; 'sTR " in";
     'bRK(1,1); pc >]

let error_ill_formed_inductive env c v =
  let pc = prterm_env env c in
  let pv = prterm_env env v in
  [< 'sTR "Not enough arguments applied to the "; pv;
     'sTR " in"; 'bRK(1,1); pc >]

let error_ill_formed_constructor env c v =
  let pc = prterm_env env c in
  let pv = prterm_env env v in
  [< 'sTR "The conclusion of"; 'bRK(1,1); pc; 'bRK(1,1); 
     'sTR "is not valid;"; 'bRK(1,1); 'sTR "it must be built from "; pv >]

let str_of_nth n =
  (string_of_int n)^
  (match n mod 10 with
     | 1 -> "st"
     | 2 -> "nd"
     | 3 -> "rd"
     | _ -> "th")

let error_bad_ind_parameters env c n v1 v2  =
  let pc = prterm_env_at_top env c in
  let pv1 = prterm_env env v1 in
  let pv2 = prterm_env env v2 in
  [< 'sTR ("The "^(str_of_nth n)^" argument of "); pv2; 'bRK(1,1);
     'sTR "must be "; pv1; 'sTR " in"; 'bRK(1,1); pc >]

let error_same_names_types id =
  [< 'sTR "The name"; 'sPC; pr_label id; 'sPC; 
     'sTR "is used twice is the inductive types definition." >]

let error_same_names_constructors id cid =
  [< 'sTR "The constructor name"; 'sPC; pr_label cid; 'sPC; 
     'sTR "is used twice is the definition of type"; 'sPC;
     pr_label id >]

let error_same_names_overlap idl = 
  [< 'sTR "The following names"; 'sPC; 
     'sTR" are used both as type names and constructor names:"; 'sPC;
     prlist_with_sep pr_coma (pr_label) idl >]

let error_not_an_arity id =
  [< 'sTR "The type of"; 'sPC; pr_label id; 'sPC; 'sTR "is not an arity." >]

let error_bad_entry () =
  [< 'sTR "Bad inductive definition." >]

let error_not_allowed_case_analysis dep kind i =
  [< 'sTR (if dep then "Dependent" else "Non Dependent");
     'sTR " case analysis on sort: "; print_sort kind; 'fNL;
     'sTR "is not allowed for inductive definition: ";
     pr_inductive (Global.env()) i >]

let error_bad_induction dep indid kind =
  [<'sTR (if dep then "Dependent" else "Non dependent");
    'sTR " induction for type "; pr_id indid;
    'sTR " and sort "; print_sort kind; 'sPC;
    'sTR "is not allowed">]

let error_not_mutual_in_scheme () =
 [< 'sTR "Induction schemes is concerned only with mutually inductive types" >]

let explain_inductive_error = function
  (* These are errors related to inductive constructions *)
  | NonPos (env,c,v) -> error_non_strictly_positive env c v
  | NotEnoughArgs (env,c,v) -> error_ill_formed_inductive env c v
  | NotConstructor (env,c,v) -> error_ill_formed_constructor env c v
  | NonPar (env,c,n,v1,v2) -> error_bad_ind_parameters env c n v1 v2
  | SameNamesTypes lab -> error_same_names_types lab
  | SameNamesConstructors (lab,clab) -> error_same_names_constructors lab clab
  | SameNamesOverlap idl -> error_same_names_overlap idl
  | NotAnArity id -> error_not_an_arity id
  | BadEntry -> error_bad_entry ()
  (* These are errors related to recursors *)
  | NotAllowedCaseAnalysis (dep,s,i) -> error_not_allowed_case_analysis dep s i
  | BadInduction (dep,indid,kind) -> error_bad_induction dep indid kind
  | NotMutualInScheme -> error_not_mutual_in_scheme ()
(* Pattern-matching errors *)

let explain_bad_pattern ctx cstr ty = 
  let pt = prterm_env ctx ty in
  let pc = pr_constructor ctx cstr in
  [< 'sTR "Found the constructor "; pc; 'bRK(1,1); 
     'sTR "while matching a term of type "; pt; 'bRK(1,1); 
     'sTR "which is not an inductive type" >]

let explain_bad_constructor ctx cstr ind =
  let pi = pr_inductive ctx ind in
(*  let pc = pr_constructor ctx cstr in*)
  let pt = pr_inductive ctx (inductive_of_constructor cstr) in
  [< 'sTR "Found a constructor of inductive type "; pt; 'bRK(1,1) ;
     'sTR "while a constructor of " ; pi; 'bRK(1,1) ;
     'sTR "is expected" >]

let explain_wrong_numarg_of_constructor ctx cstr n =
  let pc = pr_constructor ctx (cstr,[||]) in
    [<'sTR "The constructor "; pc; 'sTR " expects " ; 
      if n = 0 then [< 'sTR "no argument.">]
      else [< 'iNT n ; 'sTR " arguments.">]
    >]

let explain_wrong_predicate_arity ctx pred nondep_arity dep_arity=
  let pp = prterm_env ctx pred in
  [<'sTR "The elimination predicate "; 'sPC; pp; 'fNL;
    'sTR "should be of arity" ; 'sPC;
    prterm_env ctx nondep_arity ; 'sPC; 'sTR "(for non dependent case) or" ;
    'sPC; prterm_env ctx dep_arity ; 'sPC; 'sTR "(for dependent case).">]

let explain_needs_inversion ctx x t =
  let px = prterm_env ctx x in
  let pt = prterm_env ctx t in
  [< 'sTR "Sorry, I need inversion to compile pattern matching of term ";
     px ; 'sTR " of type: "; pt>]

let explain_unused_clause env pats =
  let s = if List.length pats > 1 then "s" else "" in
(* Without localisation
  [<'sTR ("Unused clause with pattern"^s); 'sPC;
    hOV 0 (prlist_with_sep pr_spc pr_cases_pattern pats); 'sTR ")" >]
*)
  [<'sTR "This clause is redundant" >]

let explain_non_exhaustive env pats =
  let s = if List.length pats > 1 then "s" else "" in
  [<'sTR ("Non exhaustive pattern-matching: no clause found for pattern"^s);
    'sPC; hOV 0 (prlist_with_sep pr_spc pr_cases_pattern pats) >]

let explain_pattern_matching_error env = function
  | BadPattern (c,t) -> 
      explain_bad_pattern env c t
  | BadConstructor (c,ind) ->
      explain_bad_constructor env c ind
  | WrongNumargConstructor (c,n) ->
      explain_wrong_numarg_of_constructor env c n
  | WrongPredicateArity (pred,n,dep) ->
      explain_wrong_predicate_arity env pred n dep
  | NeedsInversion (x,t) ->
      explain_needs_inversion env x t
  | UnusedClause tms ->
      explain_unused_clause env tms
  | NonExhaustive tms ->
      explain_non_exhaustive env tms
