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
open Names
open Nameops
open Term
open Termops
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
  let pe = pr_ne_context_of (str "In environment") ctx in
  str"Unbound reference: " ++ pe ++
  str"The reference " ++ int n ++ str " is free"

let explain_unbound_var ctx v =
  let var = pr_id v in
  str"No such section variable or assumption : " ++ var

let explain_not_type ctx j =
  let ctx = make_all_name_different ctx in
  let pe = pr_ne_context_of (str"In environment") ctx in
  let pc,pt = prjudge_env ctx j in
  pe ++ str "the term" ++ brk(1,1) ++ pc ++ spc () ++
  str"has type" ++ spc () ++ pt ++ spc () ++ 
  str"which should be Set, Prop or Type."

let explain_bad_assumption ctx j =
  let ctx = make_all_name_different ctx in
  let pe = pr_ne_context_of (str"In environment") ctx in
  let pc,pt = prjudge_env ctx j in
  pe ++ str "cannot declare a variable or hypothesis over the term" ++
  brk(1,1) ++ pc ++ spc () ++ str"of type" ++ spc () ++ pt ++ spc () ++
  str "because this term is not a type."

let explain_reference_variables c =
  let pc = prterm c in
  str "the constant" ++ spc () ++ pc ++ spc () ++ 
  str "refers to variables which are not in the context"

let explain_elim_arity ctx ind aritylst c pj okinds = 
  let pi = pr_inductive ctx ind in
  let ppar = prlist_with_sep pr_coma (prterm_env ctx) aritylst in
  let pc = prterm_env ctx c in
  let pp = prterm_env ctx pj.uj_val in
  let ppt = prterm_env ctx pj.uj_type in
  let msg = match okinds with
  | Some(kp,ki,explanation) ->
      let pki = prterm_env ctx ki in
      let pkp = prterm_env ctx kp in
      let explanation =	match explanation with
	| NonInformativeToInformative ->
	  "non-informative objects may not construct informative ones."
	| StrongEliminationOnNonSmallType ->
          "strong elimination on non-small inductive types leads to paradoxes."
	| WrongArity ->
	  "wrong arity" in
	(hov 0 
           (fnl () ++ str "Elimination of an inductive object of sort : " ++
            pki ++ brk(1,0) ++
            str "is not allowed on a predicate in sort : " ++ pkp  ++fnl () ++
            str "because" ++ spc () ++ str explanation))
  | None -> 
      mt ()
  in
  str "Incorrect elimination of" ++ brk(1,1) ++ pc ++ spc () ++
  str "in the inductive type" ++ brk(1,1) ++ pi ++ fnl () ++
  str "The elimination predicate" ++ brk(1,1) ++ pp ++ spc () ++
  str "has type" ++ brk(1,1) ++ ppt ++ fnl () ++
  str "It should be one of :" ++ brk(1,1)  ++ hov 0 ppar ++ fnl () ++
  msg

let explain_case_not_inductive ctx cj =
  let pc = prterm_env ctx cj.uj_val in
  let pct = prterm_env ctx cj.uj_type in
    match kind_of_term cj.uj_type with
      | Evar _ -> 
	  str "Cannot infer a type for this expression"
      | _ ->
	  str "This term" ++ brk(1,1) ++ pc ++ spc () ++ 
	  str "has type" ++ brk(1,1) ++ pct ++ spc () ++ 
	  str "which is not a (co-)inductive type"

let explain_number_branches ctx cj expn =
  let pc = prterm_env ctx cj.uj_val in
  let pct = prterm_env ctx cj.uj_type in
  str "Cases on term" ++ brk(1,1) ++ pc ++ spc ()  ++
  str "of type" ++ brk(1,1) ++ pct ++ spc () ++
  str "expects " ++  int expn ++ str " branches"

let explain_ill_formed_branch ctx c i actty expty =
  let pc = prterm_env ctx c in
  let pa = prterm_env ctx actty in
  let pe = prterm_env ctx expty in
  str "In Cases expression on term" ++ brk(1,1) ++ pc ++
  spc () ++ str "the branch "  ++ int (i+1) ++
  str " has type" ++ brk(1,1) ++ pa  ++ spc () ++ 
  str "which should be" ++ brk(1,1) ++ pe

let explain_generalization ctx (name,var) j =
  let ctx = make_all_name_different ctx in
  let pe = pr_ne_context_of (str "In environment") ctx in
  let pv = prtype_env ctx var in
  let (pc,pt) = prjudge_env (push_rel_assum (name,var) ctx) j in
  str"Illegal generalization: " ++ pe ++
  str"Cannot generalize" ++ brk(1,1) ++ pv ++ spc () ++
  str"over" ++ brk(1,1) ++ pc ++ str"," ++ spc () ++ 
  str"it has type" ++ spc () ++ pt ++ 
  spc () ++ str"which should be Set, Prop or Type."

let explain_actual_type ctx j pt =
  let ctx = make_all_name_different ctx in
  let pe = pr_ne_context_of (str "In environment") ctx in
  let (pc,pct) = prjudge_env ctx j in
  let pt = prterm_env ctx pt in
  pe ++
  str "The term" ++ brk(1,1) ++ pc  ++ spc ()  ++
  str "has type"  ++ brk(1,1) ++ pct ++ brk(1,1) ++ 
  str "while it is expected to have type" ++ brk(1,1) ++ pt

let explain_cant_apply_bad_type ctx (n,exptyp,actualtyp) rator randl =
  let randl = Array.to_list randl in
  let ctx = make_all_name_different ctx in
(*  let pe = pr_ne_context_of (str"in environment") ctx in*)
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
		  hov 2 (pc ++ spc () ++ str": "  ++ pct)) randl
  in
  str"Illegal application (Type Error): " ++ (* pe ++ *) fnl () ++
  str"The term" ++ brk(1,1) ++ pr ++ spc () ++
  str"of type" ++ brk(1,1) ++ prt ++ spc ()  ++
  str("cannot be applied to the "^term_string1) ++ fnl () ++ 
  str" " ++ v 0 appl ++ fnl () ++ str (term_string2^" has type") ++
  brk(1,1) ++ prterm_env ctx actualtyp ++ spc () ++
  str"which should be coercible to" ++ brk(1,1) ++ prterm_env ctx exptyp

let explain_cant_apply_not_functional ctx rator randl =
  let randl = Array.to_list randl in
  let ctx = make_all_name_different ctx in
(*  let pe = pr_ne_context_of (str"in environment") ctx in*)
  let pr = prterm_env ctx rator.uj_val in
  let prt = prterm_env ctx (body_of_type rator.uj_type) in
  let term_string = if List.length randl > 1 then "terms" else "term" in
  let appl = prlist_with_sep pr_fnl 
	       (fun c ->
		  let pc = prterm_env ctx c.uj_val in
		  let pct = prterm_env ctx (body_of_type c.uj_type) in
		  hov 2 (pc ++ spc () ++ str": "  ++ pct)) randl
  in
  str"Illegal application (Non-functional construction): " ++ 
  (* pe ++ *) fnl () ++
  str"The expression" ++ brk(1,1) ++ pr ++ spc () ++
  str"of type" ++ brk(1,1) ++ prt ++ spc ()  ++
  str("cannot be applied to the "^term_string) ++ fnl () ++ 
  str" " ++ v 0 appl

let explain_unexpected_type ctx actual_type expected_type =
  let ctx = make_all_name_different ctx in
  let pract = prterm_env ctx actual_type in
  let prexp = prterm_env ctx expected_type in
  str"This type is" ++ spc () ++ pract ++ spc () ++ 
  str "but is expected to be" ++
  spc () ++ prexp

let explain_not_product ctx c =
  let ctx = make_all_name_different ctx in
  let pr = prterm_env ctx c in
  str"The type of this term is a product," ++ spc () ++
  str"but it is casted with type" ++
  brk(1,1) ++ pr

(* TODO: use the names *)
(* (co)fixpoints *)
let explain_ill_formed_rec_body ctx err names i vdefs =
  let st = match err with

  (* Fixpoint guard errors *)
  | NotEnoughAbstractionInFixBody ->
      str "Not enough abstractions in the definition"
  | RecursionNotOnInductiveType ->
      str "Recursive definition on a non inductive type"
  | RecursionOnIllegalTerm ->
      str "Recursive call applied to an illegal term"
  | NotEnoughArgumentsForFixCall ->
      str "Not enough arguments for the recursive call"

  (* CoFixpoint guard errors *)
  (* TODO : r�cup�rer le contexte des termes pour pouvoir les afficher *)
  | CodomainNotInductiveType c ->
      str "The codomain is" ++ spc () ++ prterm c ++ spc () ++
      str "which should be a coinductive type"
  | NestedRecursiveOccurrences ->
      str "Nested recursive occurrences"
  | UnguardedRecursiveCall c ->
      str "Unguarded recursive call"
  | RecCallInTypeOfAbstraction c ->
      str "Not allowed recursive call in the domain of an abstraction"
  | RecCallInNonRecArgOfConstructor c ->
      str "Not allowed recursive call in a non-recursive argument of constructor"
  | RecCallInTypeOfDef c ->
      str "Not allowed recursive call in the type of a recursive definition"
  | RecCallInCaseFun c ->
      str "Not allowed recursive call in a branch of cases"
  | RecCallInCaseArg c -> 
      str "Not allowed recursive call in the argument of cases"
  | RecCallInCasePred c ->
      str "Not allowed recursive call in the type of cases in"
  | NotGuardedForm ->
      str "Definition not in guarded form"
  in
  let pvd = prterm_env ctx vdefs.(i) in
  let s = match names.(i) with Name id -> string_of_id id | Anonymous -> "_" in
  st ++ fnl () ++ str"The " ++
  (if Array.length vdefs = 1 then mt () else (int (i+1) ++ str "-th ")) ++
  str"recursive definition" ++ spc () ++ str s ++
  spc ()  ++ str":=" ++ spc ()  ++ pvd ++ spc () ++
  str "is not well-formed"

let explain_ill_typed_rec_body ctx i names vdefj vargs =
  let pvd,pvdt = prjudge_env ctx (vdefj.(i)) in
  let pv = prterm_env ctx (body_of_type vargs.(i)) in
  str"The "  ++
  (if Array.length vdefj = 1 then mt () else int (i+1) ++ str "-th") ++
  str"recursive definition"  ++ spc () ++ pvd ++ spc () ++
  str "has type" ++ spc () ++ pvdt ++spc () ++ 
  str "it should be" ++ spc () ++ pv 

let explain_not_inductive ctx c =
  let pc = prterm_env ctx c in
  str"The term" ++ brk(1,1) ++ pc ++ spc () ++
  str "is not an inductive definition"

let explain_cant_find_case_type ctx c =
  let pe = prterm_env ctx c in
  hov 3 (str "Cannot infer type of pattern-matching on" ++ ws 1 ++ pe)

let explain_occur_check ctx ev rhs =
  let id = "?" ^ string_of_int ev in
  let pt = prterm_env ctx rhs in
  str"Occur check failed: tried to define " ++ str id ++
  str" with term" ++ brk(1,1) ++ pt

let explain_not_clean ctx ev t =
  let c = mkRel (Intset.choose (free_rels t)) in
  let id = "?" ^ string_of_int ev in
  let var = prterm_env ctx c in
  str"Tried to define " ++ str id ++
  str" with a term using variable " ++ var ++ spc () ++
  str"which is not in its scope."

let explain_var_not_found ctx id = 
  str "The variable" ++ spc () ++ str (string_of_id id) ++
  spc ()  ++ str "was not found" ++ 
  spc ()  ++ str "in the current" ++ spc ()  ++ str "environment"

let explain_wrong_case_info ctx ind ci =
  let pi = prterm (mkInd ind) in
  if ci.ci_ind = ind then
    str"Cases expression on an object of inductive" ++ spc () ++ pi ++
    spc () ++ str"has invalid information"
  else
    let pc = prterm (mkInd ci.ci_ind) in
    str"A term of inductive type" ++ spc () ++ pi ++ spc () ++
    str"was given to a Cases expression on the inductive type" ++
    spc () ++ pc
       

let explain_type_error ctx = function
  | UnboundRel n -> 
      explain_unbound_rel ctx n
  | UnboundVar v -> 
      explain_unbound_var ctx v
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
  | ActualType (j, pt) -> 
      explain_actual_type ctx j pt
  | CantApplyBadType (t, rator, randl) ->
      explain_cant_apply_bad_type ctx t rator randl
  | CantApplyNonFunctional (rator, randl) ->
      explain_cant_apply_not_functional ctx rator randl
  | IllFormedRecBody (i, lna, vdefj, vargs) ->
      explain_ill_formed_rec_body ctx i lna vdefj vargs
  | IllTypedRecBody (i, lna, vdefj, vargs) -> 
     explain_ill_typed_rec_body ctx i lna vdefj vargs
  | WrongCaseInfo (ind,ci) ->
      explain_wrong_case_info ctx ind ci
(*
  | NotInductive c ->
      explain_not_inductive ctx c
*)
let explain_pretype_error ctx = function
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
  str"refiner was given an argument" ++ brk(1,1) ++ 
  prterm arg ++ spc () ++
  str"of type" ++ brk(1,1) ++ prterm ty ++ spc () ++
  str"instead of" ++ brk(1,1) ++ prterm conclty

let explain_refiner_occur_meta t =
  str"cannot refine with term" ++ brk(1,1) ++ prterm t ++
  spc () ++ str"because there are metavariables, and it is" ++
  spc () ++ str"neither an application nor a Case"

let explain_refiner_occur_meta_goal t =
  str"generated subgoal" ++ brk(1,1) ++ prterm t ++
  spc () ++ str"has metavariables in it"

let explain_refiner_cannot_applt t harg =
  str"in refiner, a term of type " ++ brk(1,1) ++
  prterm t ++ spc () ++ str"could not be applied to" ++ brk(1,1) ++
  prterm harg

let explain_refiner_cannot_unify m n =
  let pm = prterm m in 
  let pn = prterm n in
  str"Impossible to unify" ++ brk(1,1)  ++ pm ++ spc ()  ++
  str"with" ++ brk(1,1)  ++ pn

let explain_refiner_cannot_generalize ty =
  str "Cannot find a well-typed generalisation of the goal with type : " ++ 
  prterm ty

let explain_refiner_not_well_typed c =
  str"The term "  ++ prterm c  ++ str" is not well-typed"

let explain_intro_needs_product () =
  str "Introduction tactics needs products"

let explain_does_not_occur_in c hyp =
  str "The term" ++ spc () ++ prterm c ++ spc () ++ str "does not occur in" ++
  spc () ++ pr_id hyp

let explain_non_linear_proof c =
  str "cannot refine with term" ++ brk(1,1) ++ prterm c ++
  spc () ++ str"because a metavariable has several occurrences"

let explain_refiner_error = function
  | BadType (arg,ty,conclty) -> explain_refiner_bad_type arg ty conclty
  | OccurMeta t -> explain_refiner_occur_meta t
  | OccurMetaGoal t -> explain_refiner_occur_meta_goal t
  | CannotApply (t,harg) -> explain_refiner_cannot_applt t harg
  | CannotUnify (m,n) -> explain_refiner_cannot_unify m n
  | CannotGeneralize ty -> explain_refiner_cannot_generalize ty
  | NotWellTyped c -> explain_refiner_not_well_typed c
  | IntroNeedsProduct -> explain_intro_needs_product ()
  | DoesNotOccurIn (c,hyp) -> explain_does_not_occur_in c hyp
  | NonLinearProof c -> explain_non_linear_proof c

(* Inductive errors *)

let error_non_strictly_positive env c v  =
  let pc = prterm_env env c in
  let pv = prterm_env env v in
  str "Non strictly positive occurrence of " ++ pv ++ str " in" ++
  brk(1,1) ++ pc

let error_ill_formed_inductive env c v =
  let pc = prterm_env env c in
  let pv = prterm_env env v in
  str "Not enough arguments applied to the " ++ pv ++
  str " in" ++ brk(1,1) ++ pc

let error_ill_formed_constructor env c v =
  let pc = prterm_env env c in
  let pv = prterm_env env v in
  str "The conclusion of" ++ brk(1,1) ++ pc ++ brk(1,1) ++ 
  str "is not valid;" ++ brk(1,1) ++ str "it must be built from " ++ pv

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
  str ("The "^(str_of_nth n)^" argument of ") ++ pv2 ++ brk(1,1) ++
  str "must be " ++ pv1 ++ str " in" ++ brk(1,1) ++ pc

let error_same_names_types id =
  str "The name" ++ spc () ++ pr_id id ++ spc () ++ 
  str "is used twice is the inductive types definition."

let error_same_names_constructors id cid =
  str "The constructor name" ++ spc () ++ pr_id cid ++ spc () ++ 
  str "is used twice is the definition of type" ++ spc () ++
  pr_id id

let error_not_an_arity id =
  str "The type of" ++ spc () ++ pr_id id ++ spc () ++ str "is not an arity."

let error_bad_entry () =
  str "Bad inductive definition."

let error_not_allowed_case_analysis dep kind i =
  str (if dep then "Dependent" else "Non Dependent") ++
  str " case analysis on sort: " ++ print_sort kind ++ fnl () ++
  str "is not allowed for inductive definition: " ++
  pr_inductive (Global.env()) i

let error_bad_induction dep indid kind =
  str (if dep then "Dependent" else "Non dependent") ++
  str " induction for type " ++ pr_id indid ++
  str " and sort " ++ print_sort kind ++ spc () ++
  str "is not allowed"

let error_not_mutual_in_scheme () =
 str "Induction schemes is concerned only with mutually inductive types"

let explain_inductive_error = function
  (* These are errors related to inductive constructions *)
  | NonPos (env,c,v) -> error_non_strictly_positive env c v
  | NotEnoughArgs (env,c,v) -> error_ill_formed_inductive env c v
  | NotConstructor (env,c,v) -> error_ill_formed_constructor env c v
  | NonPar (env,c,n,v1,v2) -> error_bad_ind_parameters env c n v1 v2
  | SameNamesTypes id -> error_same_names_types id
  | SameNamesConstructors (id,cid) -> error_same_names_constructors id cid
  | NotAnArity id -> error_not_an_arity id
  | BadEntry -> error_bad_entry ()
  (* These are errors related to recursors *)
  | NotAllowedCaseAnalysis (dep,k,i) ->
      error_not_allowed_case_analysis dep k i
  | BadInduction (dep,indid,kind) -> error_bad_induction dep indid kind
  | NotMutualInScheme -> error_not_mutual_in_scheme ()

(* Pattern-matching errors *)

let explain_bad_pattern ctx cstr ty = 
  let pt = prterm_env ctx ty in
  let pc = pr_constructor ctx cstr in
  str "Found the constructor " ++ pc ++ brk(1,1) ++ 
  str "while matching a term of type " ++ pt ++ brk(1,1) ++ 
  str "which is not an inductive type"

let explain_bad_constructor ctx cstr ind =
  let pi = pr_inductive ctx ind in
(*  let pc = pr_constructor ctx cstr in*)
  let pt = pr_inductive ctx (inductive_of_constructor cstr) in
  str "Found a constructor of inductive type " ++ pt ++ brk(1,1)  ++
  str "while a constructor of "  ++ pi ++ brk(1,1)  ++
  str "is expected"

let explain_wrong_numarg_of_constructor ctx cstr n =
  let pc = pr_constructor ctx cstr in
  str "The constructor " ++ pc ++ str " expects "  ++
  (if n = 0 then str "no argument." else if n = 1 then str "1 argument."
   else (int n  ++ str " arguments."))

let explain_wrong_predicate_arity ctx pred nondep_arity dep_arity=
  let pp = prterm_env ctx pred in
  str "The elimination predicate " ++ spc () ++ pp ++ fnl () ++
  str "should be of arity"  ++ spc () ++
  prterm_env ctx nondep_arity  ++ spc () ++ 
  str "(for non dependent case) or"  ++
  spc () ++ prterm_env ctx dep_arity  ++ spc () ++ str "(for dependent case)."

let explain_needs_inversion ctx x t =
  let px = prterm_env ctx x in
  let pt = prterm_env ctx t in
  str "Sorry, I need inversion to compile pattern matching of term " ++
  px  ++ str " of type: " ++ pt

let explain_unused_clause env pats =
  let s = if List.length pats > 1 then "s" else "" in
(* Without localisation
  (str ("Unused clause with pattern"^s) ++ spc () ++
    hov 0 (prlist_with_sep pr_spc pr_cases_pattern pats) ++ str ")")
*)
  str "This clause is redundant"

let explain_non_exhaustive env pats =
  let s = if List.length pats > 1 then "s" else "" in
  str ("Non exhaustive pattern-matching: no clause found for pattern"^s) ++
  spc () ++ hov 0 (prlist_with_sep pr_spc pr_cases_pattern pats)

let explain_cannot_infer_predicate env typs =
  let pr_branch (cstr,typ) =
    let cstr,_ = decompose_app cstr in
    str "For " ++ prterm_env env cstr ++ str " : " ++ prterm_env env typ
  in
  str "Unable to unify the types found in the branches:" ++
  spc () ++ hov 0 (prlist_with_sep pr_fnl pr_branch (Array.to_list typs))

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
  | CannotInferPredicate typs ->
      explain_cannot_infer_predicate env typs
