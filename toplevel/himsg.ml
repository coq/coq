(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Pp
open Util
open Flags
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
open Typeclasses_errors
open Indrec
open Reduction
open Cases
open Logic
open Printer
open Rawterm
open Evd

let pr_lconstr c = quote (pr_lconstr c)
let pr_lconstr_env e c = quote (pr_lconstr_env e c)
let pr_lconstr_env_at_top e c = quote (pr_lconstr_env_at_top e c)
let pr_ljudge_env e c = let v,t = pr_ljudge_env e c in (quote v,quote t)

let pr_db env i =
  try
    match lookup_rel i env with
        Name id, _, _ -> pr_id id
      | Anonymous, _, _ -> str "<>"
  with Not_found -> str "UNBOUND_REL_" ++ int i

let explain_unbound_rel env n =
  let pe = pr_ne_context_of (str "In environment") env in
  str "Unbound reference: " ++ pe ++
  str "The reference " ++ int n ++ str " is free."

let explain_unbound_var env v =
  let var = pr_id v in
  str "No such section variable or assumption: " ++ var ++ str "."

let explain_not_type env j =
  let pe = pr_ne_context_of (str "In environment") env in
  let pc,pt = pr_ljudge_env env j in
  pe ++ str "The term" ++ brk(1,1) ++ pc ++ spc () ++
  str "has type" ++ spc () ++ pt ++ spc () ++
  str "which should be Set, Prop or Type."

let explain_bad_assumption env j =
  let pe = pr_ne_context_of (str "In environment") env in
  let pc,pt = pr_ljudge_env env j in
  pe ++ str "Cannot declare a variable or hypothesis over the term" ++
  brk(1,1) ++ pc ++ spc () ++ str "of type" ++ spc () ++ pt ++ spc () ++
  str "because this term is not a type."

let explain_reference_variables c =
  let pc = pr_lconstr c in
  str "The constant" ++ spc () ++ pc ++ spc () ++
  str "refers to variables which are not in the context."

let rec pr_disjunction pr = function
  | [a] -> pr  a
  | [a;b] -> pr a ++ str " or" ++ spc () ++ pr b
  | a::l -> pr a ++ str "," ++ spc () ++ pr_disjunction pr l
  | [] -> assert false

let explain_elim_arity env ind sorts c pj okinds =
  let env = make_all_name_different env in
  let pi = pr_inductive env ind in
  let pc = pr_lconstr_env env c in
  let msg = match okinds with
  | Some(kp,ki,explanation) ->
      let pki = pr_sort_family ki in
      let pkp = pr_sort_family kp in
      let explanation =	match explanation with
	| NonInformativeToInformative ->
          "proofs can be eliminated only to build proofs"
	| StrongEliminationOnNonSmallType ->
          "strong elimination on non-small inductive types leads to paradoxes"
	| WrongArity ->
	  "wrong arity" in
      let ppar = pr_disjunction (fun s -> quote (pr_sort_family s)) sorts in
      let ppt = pr_lconstr_env env (snd (decompose_prod_assum pj.uj_type)) in
      hov 0
	(str "the return type has sort" ++ spc () ++ ppt ++ spc () ++
	 str "while it" ++ spc () ++ str "should be " ++ ppar ++ str ".") ++
      fnl () ++
      hov 0
	(str "Elimination of an inductive object of sort " ++
	 pki ++ brk(1,0) ++
         str "is not allowed on a predicate in sort " ++ pkp ++ fnl () ++
         str "because" ++ spc () ++ str explanation ++ str ".")
  | None ->
      str "ill-formed elimination predicate."
  in
  hov 0 (
    str "Incorrect elimination of" ++ spc () ++ pc ++ spc () ++
    str "in the inductive type" ++ spc () ++ quote pi ++ str ":") ++
  fnl () ++ msg

let explain_case_not_inductive env cj =
  let env = make_all_name_different env in
  let pc = pr_lconstr_env env cj.uj_val in
  let pct = pr_lconstr_env env cj.uj_type in
    match kind_of_term cj.uj_type with
      | Evar _ ->
	  str "Cannot infer a type for this expression."
      | _ ->
	  str "The term" ++ brk(1,1) ++ pc ++ spc () ++
	  str "has type" ++ brk(1,1) ++ pct ++ spc () ++
	  str "which is not a (co-)inductive type."

let explain_number_branches env cj expn =
  let env = make_all_name_different env in
  let pc = pr_lconstr_env env cj.uj_val in
  let pct = pr_lconstr_env env cj.uj_type in
  str "Matching on term" ++ brk(1,1) ++ pc ++ spc () ++
  str "of type" ++ brk(1,1) ++ pct ++ spc () ++
  str "expects " ++  int expn ++ str " branches."

let explain_ill_formed_branch env c i actty expty =
  let env = make_all_name_different env in
  let pc = pr_lconstr_env env c in
  let pa = pr_lconstr_env env actty in
  let pe = pr_lconstr_env env expty in
  str "In pattern-matching on term" ++ brk(1,1) ++ pc ++
  spc () ++ str "the " ++ nth (i+1) ++ str " branch has type" ++
  brk(1,1) ++ pa ++ spc () ++
  str "which should be" ++ brk(1,1) ++ pe ++ str "."

let explain_generalization env (name,var) j =
  let pe = pr_ne_context_of (str "In environment") env in
  let pv = pr_ltype_env env var in
  let (pc,pt) = pr_ljudge_env (push_rel_assum (name,var) env) j in
  pe ++ str "Cannot generalize" ++ brk(1,1) ++ pv ++ spc () ++
  str "over" ++ brk(1,1) ++ pc ++ str "," ++ spc () ++
  str "it has type" ++ spc () ++ pt ++
  spc () ++ str "which should be Set, Prop or Type."

let explain_actual_type env j pt =
  let pe = pr_ne_context_of (str "In environment") env in
  let (pc,pct) = pr_ljudge_env env j in
  let pt = pr_lconstr_env env pt in
  pe ++
  str "The term" ++ brk(1,1) ++ pc ++ spc () ++
  str "has type" ++ brk(1,1) ++ pct ++ brk(1,1) ++
  str "while it is expected to have type" ++ brk(1,1) ++ pt ++ str "."

let explain_cant_apply_bad_type env (n,exptyp,actualtyp) rator randl =
  let env = make_all_name_different env in
  let nargs = Array.length randl in
(*  let pe = pr_ne_context_of (str "in environment") env in*)
  let pr,prt = pr_ljudge_env env rator in
  let term_string1 = str (plural nargs "term") in
  let term_string2 =
    if nargs>1 then str "The " ++ nth n ++ str " term" else str "This term" in
  let appl = prvect_with_sep pr_fnl
	       (fun c ->
		  let pc,pct = pr_ljudge_env env c in
		  hov 2 (pc ++ spc () ++ str ": " ++ pct)) randl
  in
  str "Illegal application (Type Error): " ++ (* pe ++ *) fnl () ++
  str "The term" ++ brk(1,1) ++ pr ++ spc () ++
  str "of type" ++ brk(1,1) ++ prt ++ spc () ++
  str "cannot be applied to the " ++ term_string1 ++ fnl () ++
  str " " ++ v 0 appl ++ fnl () ++ term_string2 ++ str " has type" ++
  brk(1,1) ++ pr_lconstr_env env actualtyp ++ spc () ++
  str "which should be coercible to" ++ brk(1,1) ++
  pr_lconstr_env env exptyp ++ str "."

let explain_cant_apply_not_functional env rator randl =
  let env = make_all_name_different env in
  let nargs = Array.length randl in
(*  let pe = pr_ne_context_of (str "in environment") env in*)
  let pr = pr_lconstr_env env rator.uj_val in
  let prt = pr_lconstr_env env rator.uj_type in
  let appl = prvect_with_sep pr_fnl
	       (fun c ->
		  let pc = pr_lconstr_env env c.uj_val in
		  let pct = pr_lconstr_env env c.uj_type in
		  hov 2 (pc ++ spc () ++ str ": " ++ pct)) randl
  in
  str "Illegal application (Non-functional construction): " ++
  (* pe ++ *) fnl () ++
  str "The expression" ++ brk(1,1) ++ pr ++ spc () ++
  str "of type" ++ brk(1,1) ++ prt ++ spc () ++
  str "cannot be applied to the " ++ str (plural nargs "term") ++ fnl () ++
  str " " ++ v 0 appl

let explain_unexpected_type env actual_type expected_type =
  let pract = pr_lconstr_env env actual_type in
  let prexp = pr_lconstr_env env expected_type in
  str "This type is" ++ spc () ++ pract ++ spc () ++
  str "but is expected to be" ++
  spc () ++ prexp ++ str "."

let explain_not_product env c =
  let pr = pr_lconstr_env env c in
  str "The type of this term is a product" ++ spc () ++
  str "while it is expected to be" ++
  (if is_Type c then str " a sort" else (brk(1,1) ++ pr)) ++ str "."

(* TODO: use the names *)
(* (co)fixpoints *)
let explain_ill_formed_rec_body env err names i =
  let prt_name i =
    match names.(i) with
        Name id -> str "Recursive definition of " ++ pr_id id
      | Anonymous -> str "The " ++ nth i ++ str " definition" in

  let st = match err with

  (* Fixpoint guard errors *)
  | NotEnoughAbstractionInFixBody ->
      str "Not enough abstractions in the definition"
  | RecursionNotOnInductiveType c ->
      str "Recursive definition on" ++ spc () ++ pr_lconstr_env env c ++ spc () ++
      str "which should be an inductive type"
  | RecursionOnIllegalTerm(j,arg,le,lt) ->
      let called =
        match names.(j) with
            Name id -> pr_id id
          | Anonymous -> str "the " ++ nth i ++ str " definition" in
      let vars =
        match (lt,le) with
            ([],[]) -> assert false
          | ([],[x]) ->
              str "a subterm of " ++ pr_db env x
          | ([],_) ->
              str "a subterm of the following variables: " ++
              prlist_with_sep pr_spc (pr_db env) le
          | ([x],_) -> pr_db env x
          | _ ->
              str "one of the following variables: " ++
              prlist_with_sep pr_spc (pr_db env) lt in
      str "Recursive call to " ++ called ++ spc () ++
      str "has principal argument equal to" ++ spc () ++
      pr_lconstr_env env arg ++ fnl () ++ str "instead of " ++ vars

  | NotEnoughArgumentsForFixCall j ->
      let called =
        match names.(j) with
            Name id -> pr_id id
          | Anonymous -> str "the " ++ nth i ++ str " definition" in
     str "Recursive call to " ++ called ++ str " has not enough arguments"

  (* CoFixpoint guard errors *)
  | CodomainNotInductiveType c ->
      str "The codomain is" ++ spc () ++ pr_lconstr_env env c ++ spc () ++
      str "which should be a coinductive type"
  | NestedRecursiveOccurrences ->
      str "Nested recursive occurrences"
  | UnguardedRecursiveCall c ->
      str "Unguarded recursive call in" ++ spc () ++ pr_lconstr_env env c
  | RecCallInTypeOfAbstraction c ->
      str "Recursive call forbidden in the domain of an abstraction:" ++
      spc () ++ pr_lconstr_env env c
  | RecCallInNonRecArgOfConstructor c ->
      str "Recursive call on a non-recursive argument of constructor" ++
      spc () ++ pr_lconstr_env env c
  | RecCallInTypeOfDef c ->
      str "Recursive call forbidden in the type of a recursive definition" ++
      spc () ++ pr_lconstr_env env c
  | RecCallInCaseFun c ->
      str "Recursive call in a branch of" ++ spc () ++ pr_lconstr_env env c
  | RecCallInCaseArg c ->
      str "Recursive call in the argument of cases in" ++ spc () ++
      pr_lconstr_env env c
  | RecCallInCasePred c ->
      str "Recursive call in the type of cases in" ++  spc () ++
      pr_lconstr_env env c
  | NotGuardedForm c ->
      str "Sub-expression " ++ pr_lconstr_env env c ++
      strbrk " not in guarded form (should be a constructor," ++
      strbrk " an abstraction, a match, a cofix or a recursive call)"
  in
  prt_name i ++ str " is ill-formed." ++ fnl () ++
  pr_ne_context_of (str "In environment") env ++
  st ++ str "."

let explain_ill_typed_rec_body env i names vdefj vargs =
  let env = make_all_name_different env in
  let pvd,pvdt = pr_ljudge_env env (vdefj.(i)) in
  let pv = pr_lconstr_env env vargs.(i) in
  str "The " ++
  (if Array.length vdefj = 1 then mt () else nth (i+1) ++ spc ()) ++
  str "recursive definition" ++ spc () ++ pvd ++ spc () ++
  str "has type" ++ spc () ++ pvdt ++ spc () ++
  str "while it should be" ++ spc () ++ pv ++ str "."

let explain_cant_find_case_type env c =
  let env = make_all_name_different env in
  let pe = pr_lconstr_env env c in
  str "Cannot infer type of pattern-matching on" ++ ws 1 ++ pe ++ str "."

let explain_occur_check env ev rhs =
  let env = make_all_name_different env in
  let id = Evd.string_of_existential ev in
  let pt = pr_lconstr_env env rhs in
  str "Cannot define " ++ str id ++ str " with term" ++ brk(1,1) ++
  pt ++ spc () ++ str "that would depend on itself."

let explain_hole_kind env = function
  | QuestionMark _ -> str "this placeholder"
  | CasesType ->
      str "the type of this pattern-matching problem"
  | BinderType (Name id) ->
      str "the type of " ++ Nameops.pr_id id
  | BinderType Anonymous ->
      str "the type of this anonymous binder"
  | ImplicitArg (c,(n,ido)) ->
      let id = Option.get ido in
      str "the implicit parameter " ++
      pr_id id ++ spc () ++ str "of" ++
      spc () ++ Nametab.pr_global_env Idset.empty c
  | InternalHole ->
      str "an internal placeholder"
  | TomatchTypeParameter (tyi,n) ->
      str "the " ++ nth n ++
      str " argument of the inductive type (" ++ pr_inductive env tyi ++
      str ") of this term"
  | GoalEvar ->
      str "an existential variable"

let explain_not_clean env ev t k =
  let env = make_all_name_different env in
  let id = Evd.string_of_existential ev in
  let var = pr_lconstr_env env t in
  str "Tried to instantiate " ++ explain_hole_kind env k ++
  str " (" ++ str id ++ str ")" ++ spc () ++
  str "with a term using variable " ++ var ++ spc () ++
  str "which is not in its scope."

let pr_ne_context_of header footer env =
  if Environ.rel_context env = empty_rel_context &
    Environ.named_context env = empty_named_context  then footer
  else pr_ne_context_of header env

let explain_typeclass_resolution env evi k =
  match k with
      InternalHole | ImplicitArg _ ->
	(match Typeclasses.class_of_constr evi.evar_concl with
	  | Some c -> 
	      let env = Evd.evar_env evi in
		str"." ++ fnl () ++ str "Could not find an instance for " ++ 
		  pr_lconstr_env env evi.evar_concl ++ 
		  pr_ne_context_of (str " in environment:"++ fnl ()) (str ".") env
	  | None -> str ".")
    | _ -> str "."

let explain_unsolvable_implicit env evi k =
  str "Cannot infer " ++ explain_hole_kind env k ++ explain_typeclass_resolution env evi k

let explain_var_not_found env id =
  str "The variable" ++ spc () ++ pr_id id ++
  spc () ++ str "was not found" ++
  spc () ++ str "in the current" ++ spc () ++ str "environment" ++ str "."

let explain_wrong_case_info env ind ci =
  let pi = pr_inductive (Global.env()) ind in
  if ci.ci_ind = ind then
    str "Pattern-matching expression on an object of inductive type" ++
    spc () ++ pi ++ spc () ++ str "has invalid information."
  else
    let pc = pr_inductive (Global.env()) ci.ci_ind in
    str "A term of inductive type" ++ spc () ++ pi ++ spc () ++
    str "was given to a pattern-matching expression on the inductive type" ++
    spc () ++ pc ++ str "."

let explain_cannot_unify env m n =
  let pm = pr_lconstr_env env m in
  let pn = pr_lconstr_env env n in
  str "Impossible to unify" ++ brk(1,1) ++ pm ++ spc () ++
  str "with" ++ brk(1,1) ++ pn

let explain_cannot_unify_local env m n subn =
  let pm = pr_lconstr_env env m in
  let pn = pr_lconstr_env env n in
  let psubn = pr_lconstr_env env subn in
    str "Impossible to unify" ++ brk(1,1) ++ pm ++ spc () ++
      str "with" ++ brk(1,1) ++ pn ++ spc () ++ str "as" ++ brk(1,1) ++
      psubn ++ str " contains local variables"

let explain_refiner_cannot_generalize env ty =
  str "Cannot find a well-typed generalisation of the goal with type : " ++
  pr_lconstr_env env ty

let explain_no_occurrence_found env c =
  str "Found no subterm matching " ++ pr_lconstr_env env c ++
  str " in the current goal"

let explain_cannot_unify_binding_type env m n =
  let pm = pr_lconstr_env env m in
  let pn = pr_lconstr_env env n in
  str "This binding has type" ++ brk(1,1) ++ pm ++ spc () ++
  str "which should be unifiable with" ++ brk(1,1) ++ pn

let explain_type_error env err =
  let env = make_all_name_different env in
  match err with
  | UnboundRel n ->
      explain_unbound_rel env n
  | UnboundVar v ->
      explain_unbound_var env v
  | NotAType j ->
      explain_not_type env j
  | BadAssumption c ->
      explain_bad_assumption env c
  | ReferenceVariables id ->
      explain_reference_variables id
  | ElimArity (ind, aritylst, c, pj, okinds) ->
      explain_elim_arity env ind aritylst c pj okinds
  | CaseNotInductive cj ->
      explain_case_not_inductive env cj
  | NumberBranches (cj, n) ->
      explain_number_branches env cj n
  | IllFormedBranch (c, i, actty, expty) ->
      explain_ill_formed_branch env c i actty expty
  | Generalization (nvar, c) ->
      explain_generalization env nvar c
  | ActualType (j, pt) ->
      explain_actual_type env j pt
  | CantApplyBadType (t, rator, randl) ->
      explain_cant_apply_bad_type env t rator randl
  | CantApplyNonFunctional (rator, randl) ->
      explain_cant_apply_not_functional env rator randl
  | IllFormedRecBody (err, lna, i) ->
      explain_ill_formed_rec_body env err lna i
  | IllTypedRecBody (i, lna, vdefj, vargs) ->
     explain_ill_typed_rec_body env i lna vdefj vargs
  | WrongCaseInfo (ind,ci) ->
      explain_wrong_case_info env ind ci

let explain_pretype_error env err =
  let env = make_all_name_different env in
  match err with
  | CantFindCaseType c -> explain_cant_find_case_type env c
  | OccurCheck (n,c) -> explain_occur_check env n c
  | NotClean (n,c,k) -> explain_not_clean env n c k
  | UnsolvableImplicit (evi,k) -> explain_unsolvable_implicit env evi k
  | VarNotFound id -> explain_var_not_found env id
  | UnexpectedType (actual,expect) -> explain_unexpected_type env actual expect
  | NotProduct c -> explain_not_product env c
  | CannotUnify (m,n) -> explain_cannot_unify env m n
  | CannotUnifyLocal (m,n,sn) -> explain_cannot_unify_local env m n sn
  | CannotGeneralize ty -> explain_refiner_cannot_generalize env ty
  | NoOccurrenceFound c -> explain_no_occurrence_found env c
  | CannotUnifyBindingType (m,n) -> explain_cannot_unify_binding_type env m n

      
(* Typeclass errors *)

let explain_unbound_class env (_,id) =
  str "Unbound class name " ++ Nameops.pr_id id

let explain_unbound_method env cid id =
  str "Unbound method name " ++ Nameops.pr_id (snd id) ++ spc () ++ str"of class" ++ spc () ++ 
    Nameops.pr_id cid

let pr_constr_exprs exprs = 
  hv 0 (List.fold_right 
	 (fun d pps -> ws 2 ++ Ppconstr.pr_constr_expr d ++ pps)
         exprs (mt ()))

let explain_no_instance env (_,id) l =
  str "No instance found for class " ++ Nameops.pr_id id ++ spc () ++
  str "applied to arguments" ++ spc () ++ 
    prlist_with_sep pr_spc (pr_lconstr_env env) l

let explain_mismatched_contexts env c i j = 
  str"Mismatched contexts while declaring instance: " ++ brk (1,1) ++
    hov 1 (str"Expected:" ++ brk (1, 1) ++ pr_named_context env j) ++ fnl () ++ brk (1,1) ++ 
    hov 1 (str"Found:" ++ brk (1, 1) ++ pr_constr_exprs i)

let explain_typeclass_error env err = 
  match err with
    | UnboundClass id -> explain_unbound_class env id
    | UnboundMethod (cid, id) -> explain_unbound_method env cid id
    | NoInstance (id, l) -> explain_no_instance env id l
    | MismatchedContextInstance (c, i, j) -> explain_mismatched_contexts env c i j
	
(* Refiner errors *)

let explain_refiner_bad_type arg ty conclty =
  str "refiner was given an argument" ++ brk(1,1) ++
  pr_lconstr arg ++ spc () ++
  str "of type" ++ brk(1,1) ++ pr_lconstr ty ++ spc () ++
  str "instead of" ++ brk(1,1) ++ pr_lconstr conclty

let explain_refiner_occur_meta t =
  str "cannot refine with term" ++ brk(1,1) ++ pr_lconstr t ++
  spc () ++ str "because there are metavariables, and it is" ++
  spc () ++ str "neither an application nor a Case"

let explain_refiner_occur_meta_goal t =
  str "generated subgoal" ++ brk(1,1) ++ pr_lconstr t ++
  spc () ++ str "has metavariables in it"

let explain_refiner_cannot_apply t harg =
  str "in refiner, a term of type " ++ brk(1,1) ++
  pr_lconstr t ++ spc () ++ str "could not be applied to" ++ brk(1,1) ++
  pr_lconstr harg

let explain_refiner_not_well_typed c =
  str "The term " ++ pr_lconstr c ++ str " is not well-typed"

let explain_intro_needs_product () =
  str "Introduction tactics needs products."

let explain_does_not_occur_in c hyp =
  str "The term" ++ spc () ++ pr_lconstr c ++ spc () ++
  str "does not occur in" ++ spc () ++ pr_id hyp ++ str "."

let explain_non_linear_proof c =
  str "cannot refine with term" ++ brk(1,1) ++ pr_lconstr c ++
  spc () ++ str "because a metavariable has several occurrences."

let explain_refiner_error = function
  | BadType (arg,ty,conclty) -> explain_refiner_bad_type arg ty conclty
  | OccurMeta t -> explain_refiner_occur_meta t
  | OccurMetaGoal t -> explain_refiner_occur_meta_goal t
  | CannotApply (t,harg) -> explain_refiner_cannot_apply t harg
  | NotWellTyped c -> explain_refiner_not_well_typed c
  | IntroNeedsProduct -> explain_intro_needs_product ()
  | DoesNotOccurIn (c,hyp) -> explain_does_not_occur_in c hyp
  | NonLinearProof c -> explain_non_linear_proof c

(* Inductive errors *)

let error_non_strictly_positive env c v  =
  let pc = pr_lconstr_env env c in
  let pv = pr_lconstr_env env v in
  str "Non strictly positive occurrence of " ++ pv ++ str " in" ++
  brk(1,1) ++ pc ++ str "."

let error_ill_formed_inductive env c v =
  let pc = pr_lconstr_env env c in
  let pv = pr_lconstr_env env v in
  str "Not enough arguments applied to the " ++ pv ++
  str " in" ++ brk(1,1) ++ pc ++ str "."

let error_ill_formed_constructor env id c v nparams nargs =
  let pv = pr_lconstr_env env v in
  let atomic = (nb_prod c = 0) in
  str "The type of constructor" ++ brk(1,1) ++ pr_id id ++ brk(1,1) ++
  str "is not valid;" ++ brk(1,1) ++ 
  strbrk (if atomic then "it must be " else "its conclusion must be ") ++ 
  pv ++ 
  (* warning: because of implicit arguments it is difficult to say which
     parameters must be explicitly given *)
  (if nparams<>0 then
    strbrk " applied to its " ++ str (plural nparams "parameter")
  else
    mt()) ++
  (if nargs<>0 then
     str (if nparams<>0 then " and" else " applied") ++
     strbrk " to some " ++ str (plural nargs "argument")
   else
     mt()) ++ str "."

let error_bad_ind_parameters env c n v1 v2  =
  let pc = pr_lconstr_env_at_top env c in
  let pv1 = pr_lconstr_env env v1 in
  let pv2 = pr_lconstr_env env v2 in
  str "The " ++ nth n ++ str " argument of " ++ pv2 ++ brk(1,1) ++
  str "must be " ++ pv1 ++ str " in" ++ brk(1,1) ++ pc ++ str "."

let error_same_names_types id =
  str "The name" ++ spc () ++ pr_id id ++ spc () ++
  str "is used more than once."

let error_same_names_constructors id =
  str "The constructor name" ++ spc () ++ pr_id id ++ spc () ++
  str "is used more than once."

let error_same_names_overlap idl =
  strbrk "The following names are used both as type names and constructor " ++
  str "names:" ++ spc () ++
  prlist_with_sep pr_coma pr_id idl ++ str "."

let error_not_an_arity id =
  str "The type of" ++ spc () ++ pr_id id ++ spc () ++ str "is not an arity."

let error_bad_entry () =
  str "Bad inductive definition."

let error_not_allowed_case_analysis dep kind i =
  str (if dep then "Dependent" else "Non Dependent") ++
  str " case analysis on sort: " ++ pr_sort kind ++ fnl () ++
  str "is not allowed for inductive definition: " ++
  pr_inductive (Global.env()) i ++ str "."

let error_bad_induction dep indid kind =
  str (if dep then "Dependent" else "Non dependent") ++
  str " induction for type " ++ pr_id indid ++
  str " and sort " ++ pr_sort kind ++ spc () ++
  str "is not allowed."

let error_not_mutual_in_scheme ind ind' =
  if ind = ind' then
    str "The inductive type " ++ pr_inductive (Global.env()) ind ++
    str "occurs twice."
  else
    str "The inductive types " ++ pr_inductive (Global.env()) ind ++ spc () ++
    str "and" ++ spc () ++ pr_inductive (Global.env()) ind' ++ spc () ++
    str "are not mutually defined."

(* Inductive constructions errors *)

let explain_inductive_error = function
  | NonPos (env,c,v) -> error_non_strictly_positive env c v
  | NotEnoughArgs (env,c,v) -> error_ill_formed_inductive env c v
  | NotConstructor (env,id,c,v,n,m) ->
      error_ill_formed_constructor env id c v n m
  | NonPar (env,c,n,v1,v2) -> error_bad_ind_parameters env c n v1 v2
  | SameNamesTypes id -> error_same_names_types id
  | SameNamesConstructors id -> error_same_names_constructors id
  | SameNamesOverlap idl -> error_same_names_overlap idl
  | NotAnArity id -> error_not_an_arity id
  | BadEntry -> error_bad_entry ()

(* Recursion schemes errors *)

let explain_recursion_scheme_error = function
  | NotAllowedCaseAnalysis (dep,k,i) ->
      error_not_allowed_case_analysis dep k i
  | BadInduction (dep,indid,kind) -> error_bad_induction dep indid kind
  | NotMutualInScheme (ind,ind')-> error_not_mutual_in_scheme ind ind'

(* Pattern-matching errors *)

let explain_bad_pattern env cstr ty =
  let env = make_all_name_different env in
  let pt = pr_lconstr_env env ty in
  let pc = pr_constructor env cstr in
  str "Found the constructor " ++ pc ++ brk(1,1) ++
  str "while matching a term of type " ++ pt ++ brk(1,1) ++
  str "which is not an inductive type."

let explain_bad_constructor env cstr ind =
  let pi = pr_inductive env ind in
(*  let pc = pr_constructor env cstr in*)
  let pt = pr_inductive env (inductive_of_constructor cstr) in
  str "Found a constructor of inductive type " ++ pt ++ brk(1,1) ++
  str "while a constructor of " ++ pi ++ brk(1,1) ++
  str "is expected."

let decline_string n s =
  if n = 0 then "no "^s
  else if n = 1 then "1 "^s
  else (string_of_int n^" "^s^"s")

let explain_wrong_numarg_constructor env cstr n =
  str "The constructor " ++ pr_constructor env cstr ++
  str " expects " ++ str (decline_string n "argument") ++ str "."

let explain_wrong_numarg_inductive env ind n =
  str "The inductive type " ++ pr_inductive env ind ++
  str " expects " ++ str (decline_string n "argument") ++ str "."

let explain_wrong_predicate_arity env pred nondep_arity dep_arity=
  let env = make_all_name_different env in
  let pp = pr_lconstr_env env pred in
  str "The elimination predicate " ++ spc () ++ pp ++ fnl () ++
  str "should be of arity" ++ spc () ++
  pr_lconstr_env env nondep_arity ++ spc () ++
  str "(for non dependent case) or" ++
  spc () ++ pr_lconstr_env env dep_arity ++ spc () ++ str "(for dependent case)."

let explain_needs_inversion env x t =
  let env = make_all_name_different env in
  let px = pr_lconstr_env env x in
  let pt = pr_lconstr_env env t in
  str "Sorry, I need inversion to compile pattern matching on term " ++
  px ++ str " of type: " ++ pt ++ str "."

let explain_unused_clause env pats =
(* Without localisation
  let s = if List.length pats > 1 then "s" else "" in
  (str ("Unused clause with pattern"^s) ++ spc () ++
    hov 0 (prlist_with_sep pr_spc pr_cases_pattern pats) ++ str ")")
*)
  str "This clause is redundant."

let explain_non_exhaustive env pats =
  str "Non exhaustive pattern-matching: no clause found for " ++
  str (plural (List.length pats) "pattern") ++
  spc () ++ hov 0 (prlist_with_sep pr_spc pr_cases_pattern pats)

let explain_cannot_infer_predicate env typs =
  let env = make_all_name_different env in
  let pr_branch (cstr,typ) =
    let cstr,_ = decompose_app cstr in
    str "For " ++ pr_lconstr_env env cstr ++ str " : " ++ pr_lconstr_env env typ
  in
  str "Unable to unify the types found in the branches:" ++
  spc () ++ hov 0 (prlist_with_sep pr_fnl pr_branch (Array.to_list typs))

let explain_pattern_matching_error env = function
  | BadPattern (c,t) ->
      explain_bad_pattern env c t
  | BadConstructor (c,ind) ->
      explain_bad_constructor env c ind
  | WrongNumargConstructor (c,n) ->
      explain_wrong_numarg_constructor env c n
  | WrongNumargInductive (c,n) ->
      explain_wrong_numarg_inductive env c n
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

let explain_reduction_tactic_error = function
  | Tacred.InvalidAbstraction (env,c,(env',e)) ->
      str "The abstracted term" ++ spc () ++ pr_lconstr_env_at_top env c ++
      spc () ++ str "is not well typed." ++ fnl () ++
      explain_type_error env' e
