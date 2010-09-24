(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
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
open Namegen
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
      let ppt = pr_lconstr_env env ((strip_prod_assum pj.uj_type)) in
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
let explain_ill_formed_rec_body env err names i fixenv vdefj =
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
      let pr_db x = quote (pr_db env x) in
      let vars =
        match (lt,le) with
            ([],[]) -> assert false
          | ([],[x]) -> str "a subterm of " ++ pr_db x
          | ([],_) -> str "a subterm of the following variables: " ++
              prlist_with_sep pr_spc pr_db le
          | ([x],_) -> pr_db x
          | _ ->
              str "one of the following variables: " ++
              prlist_with_sep pr_spc pr_db lt in
      str "Recursive call to " ++ called ++ spc () ++
      strbrk "has principal argument equal to" ++ spc () ++
      pr_lconstr_env env arg ++ strbrk " instead of " ++ vars

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
  st ++ str "." ++ fnl () ++
  (try (* May fail with unresolved globals. *)
      let fixenv = make_all_name_different fixenv in
      let pvd = pr_lconstr_env fixenv vdefj.(i).uj_val in
	str"Recursive definition is:" ++ spc () ++ pvd ++ str "."
    with _ -> mt ())

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

let pr_ne_context_of header footer env =
  if Environ.rel_context env = empty_rel_context &
    Environ.named_context env = empty_named_context
  then footer
  else pr_ne_context_of header env

let explain_hole_kind env evi = function
  | QuestionMark _ -> str "this placeholder"
  | CasesType ->
      str "the type of this pattern-matching problem"
  | BinderType (Name id) ->
      str "the type of " ++ Nameops.pr_id id
  | BinderType Anonymous ->
      str "the type of this anonymous binder"
  | ImplicitArg (c,(n,ido),b) ->
      let id = Option.get ido in
      str "the implicit parameter " ++
      pr_id id ++ spc () ++ str "of" ++
      spc () ++ Nametab.pr_global_env Idset.empty c
  | InternalHole ->
      str "an internal placeholder" ++
	Option.cata (fun evi ->
	  let env = Evd.evar_env evi in
	    str " of type "  ++ pr_lconstr_env env evi.evar_concl ++
	      pr_ne_context_of (str " in environment:"++ fnl ()) (mt ()) env)
	(mt ()) evi
  | TomatchTypeParameter (tyi,n) ->
      str "the " ++ nth n ++
      str " argument of the inductive type (" ++ pr_inductive env tyi ++
      str ") of this term"
  | GoalEvar ->
      str "an existential variable"
  | ImpossibleCase ->
      str "the type of an impossible pattern-matching clause"
  | MatchingVar _ ->
      assert false

let explain_not_clean env ev t k =
  let env = make_all_name_different env in
  let id = Evd.string_of_existential ev in
  let var = pr_lconstr_env env t in
  str "Tried to instantiate " ++ explain_hole_kind env None k ++
  str " (" ++ str id ++ str ")" ++ spc () ++
  str "with a term using variable " ++ var ++ spc () ++
  str "which is not in its scope."

let explain_unsolvability = function
  | None -> mt()
  | Some (SeveralInstancesFound n) ->
      strbrk " (several distinct possible instances found)"

let explain_typeclass_resolution env evi k =
  match k with
  | GoalEvar | InternalHole | ImplicitArg _ ->
      (match Typeclasses.class_of_constr evi.evar_concl with
      | Some c ->
	  let env = Evd.evar_env evi in
	    fnl () ++ str "Could not find an instance for " ++
	      pr_lconstr_env env evi.evar_concl ++
	      pr_ne_context_of (str " in environment:"++ fnl ()) (str ".") env
      | None -> mt())
  | _ -> mt()

let explain_unsolvable_implicit env evi k explain =
  str "Cannot infer " ++ explain_hole_kind env (Some evi) k ++
  explain_unsolvability explain ++ str "." ++
  explain_typeclass_resolution env evi k

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
  str "with" ++ brk(1,1) ++ pn ++ str "."

let explain_cannot_unify_local env m n subn =
  let pm = pr_lconstr_env env m in
  let pn = pr_lconstr_env env n in
  let psubn = pr_lconstr_env env subn in
    str "Impossible to unify" ++ brk(1,1) ++ pm ++ spc () ++
      str "with" ++ brk(1,1) ++ pn ++ spc () ++ str "as" ++ brk(1,1) ++
      psubn ++ str " contains local variables."

let explain_refiner_cannot_generalize env ty =
  str "Cannot find a well-typed generalisation of the goal with type: " ++
  pr_lconstr_env env ty ++ str "."

let explain_no_occurrence_found env c id =
  str "Found no subterm matching " ++ pr_lconstr_env env c ++
  str " in " ++
    (match id with
      | Some id -> pr_id id
      | None -> str"the current goal") ++ str "."

let explain_cannot_unify_binding_type env m n =
  let pm = pr_lconstr_env env m in
  let pn = pr_lconstr_env env n in
  str "This binding has type" ++ brk(1,1) ++ pm ++ spc () ++
  str "which should be unifiable with" ++ brk(1,1) ++ pn ++ str "."

let explain_cannot_find_well_typed_abstraction env p l =
  str "Abstracting over the " ++
  str (plural (List.length l) "term") ++ spc () ++
  hov 0 (pr_enum (pr_lconstr_env env) l) ++ spc () ++
  str "leads to a term" ++ spc () ++ pr_lconstr_env env p ++ spc () ++
  str "which is ill-typed."

let explain_abstraction_over_meta _ m n =
  strbrk "Too complex unification problem: cannot find a solution for both " ++
  pr_name m ++ spc () ++ str "and " ++ pr_name n ++ str "."

let explain_non_linear_unification env m t =
  strbrk "Cannot unambiguously instantiate " ++
  pr_name m ++ str ":" ++
  strbrk " which would require to abstract twice on " ++
  pr_lconstr_env env t ++ str "."

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
  | IllFormedRecBody (err, lna, i, fixenv, vdefj) ->
      explain_ill_formed_rec_body env err lna i fixenv vdefj
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
  | UnsolvableImplicit (evi,k,exp) -> explain_unsolvable_implicit env evi k exp
  | VarNotFound id -> explain_var_not_found env id
  | UnexpectedType (actual,expect) -> explain_unexpected_type env actual expect
  | NotProduct c -> explain_not_product env c
  | CannotUnify (m,n) -> explain_cannot_unify env m n
  | CannotUnifyLocal (m,n,sn) -> explain_cannot_unify_local env m n sn
  | CannotGeneralize ty -> explain_refiner_cannot_generalize env ty
  | NoOccurrenceFound (c, id) -> explain_no_occurrence_found env c id
  | CannotUnifyBindingType (m,n) -> explain_cannot_unify_binding_type env m n
  | CannotFindWellTypedAbstraction (p,l) ->
      explain_cannot_find_well_typed_abstraction env p l
  | AbstractionOverMeta (m,n) -> explain_abstraction_over_meta env m n
  | NonLinearUnification (m,c) -> explain_non_linear_unification env m c

(* Typeclass errors *)

let explain_not_a_class env c =
  pr_constr_env env c ++ str" is not a declared type class."

let explain_unbound_method env cid id =
  str "Unbound method name " ++ Nameops.pr_id (snd id) ++ spc () ++ str"of class" ++ spc () ++
    pr_global cid ++ str "."

let pr_constr_exprs exprs =
  hv 0 (List.fold_right
	 (fun d pps -> ws 2 ++ Ppconstr.pr_constr_expr d ++ pps)
         exprs (mt ()))

let explain_no_instance env (_,id) l =
  str "No instance found for class " ++ Nameops.pr_id id ++ spc () ++
  str "applied to arguments" ++ spc () ++
    prlist_with_sep pr_spc (pr_lconstr_env env) l

let pr_constraints printenv env evm =
  let l = Evd.to_list evm in
  let (ev, evi) = List.hd l in
    if List.for_all (fun (ev', evi') ->
      eq_named_context_val evi.evar_hyps evi'.evar_hyps) l
    then
      let pe = pr_ne_context_of (str "In environment:") (mt ())
	(reset_with_named_context evi.evar_hyps env) in
	(if printenv then pe ++ fnl () else mt ()) ++
	  prlist_with_sep (fun () -> fnl ())
	  (fun (ev, evi) -> str(string_of_existential ev)++ str " == " ++ pr_constr evi.evar_concl) l
    else
      pr_evar_map evm

let explain_unsatisfiable_constraints env evd constr =
  let evm = Evarutil.nf_evars evd in
  let undef = Evd.undefined_evars evm in
  match constr with
  | None ->
      str"Unable to satisfy the following constraints:" ++ fnl() ++
	pr_constraints true env undef
  | Some (ev, k) ->
      explain_unsolvable_implicit env (Evd.find evm ev) k None ++ fnl () ++
	if List.length (Evd.to_list undef) > 1 then
	  str"With the following constraints:" ++ fnl() ++
	    pr_constraints false env (Evd.remove undef ev)
	else mt ()

let explain_mismatched_contexts env c i j =
  str"Mismatched contexts while declaring instance: " ++ brk (1,1) ++
    hov 1 (str"Expected:" ++ brk (1, 1) ++ pr_rel_context env j) ++ fnl () ++ brk (1,1) ++
    hov 1 (str"Found:" ++ brk (1, 1) ++ pr_constr_exprs i)

let explain_typeclass_error env err =
  match err with
    | NotAClass c -> explain_not_a_class env c
    | UnboundMethod (cid, id) -> explain_unbound_method env cid id
    | NoInstance (id, l) -> explain_no_instance env id l
    | UnsatisfiableConstraints (evd, c) -> explain_unsatisfiable_constraints env evd c
    | MismatchedContextInstance (c, i, j) -> explain_mismatched_contexts env c i j

(* Refiner errors *)

let explain_refiner_bad_type arg ty conclty =
  str "Refiner was given an argument" ++ brk(1,1) ++
  pr_lconstr arg ++ spc () ++
  str "of type" ++ brk(1,1) ++ pr_lconstr ty ++ spc () ++
  str "instead of" ++ brk(1,1) ++ pr_lconstr conclty ++ str "."

let explain_refiner_unresolved_bindings l =
  str "Unable to find an instance for the " ++
  str (plural (List.length l) "variable") ++ spc () ++
  prlist_with_sep pr_comma pr_name l ++ str"."

let explain_refiner_cannot_apply t harg =
  str "In refiner, a term of type" ++ brk(1,1) ++
  pr_lconstr t ++ spc () ++ str "could not be applied to" ++ brk(1,1) ++
  pr_lconstr harg ++ str "."

let explain_refiner_not_well_typed c =
  str "The term " ++ pr_lconstr c ++ str " is not well-typed."

let explain_intro_needs_product () =
  str "Introduction tactics needs products."

let explain_does_not_occur_in c hyp =
  str "The term" ++ spc () ++ pr_lconstr c ++ spc () ++
  str "does not occur in" ++ spc () ++ pr_id hyp ++ str "."

let explain_non_linear_proof c =
  str "Cannot refine with term" ++ brk(1,1) ++ pr_lconstr c ++
  spc () ++ str "because a metavariable has several occurrences."

let explain_meta_in_type c =
  str "In refiner, a meta appears in the type " ++ brk(1,1) ++ pr_lconstr c ++
  str " of another meta"

let explain_refiner_error = function
  | BadType (arg,ty,conclty) -> explain_refiner_bad_type arg ty conclty
  | UnresolvedBindings t -> explain_refiner_unresolved_bindings t
  | CannotApply (t,harg) -> explain_refiner_cannot_apply t harg
  | NotWellTyped c -> explain_refiner_not_well_typed c
  | IntroNeedsProduct -> explain_intro_needs_product ()
  | DoesNotOccurIn (c,hyp) -> explain_does_not_occur_in c hyp
  | NonLinearProof c -> explain_non_linear_proof c
  | MetaInType c -> explain_meta_in_type c

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
  str "Last occurrence of " ++ pv2 ++ str " must have " ++ pv1 ++
  str " as " ++ nth n ++ str " argument in " ++ brk(1,1) ++ pc ++ str "."

let error_same_names_types id =
  str "The name" ++ spc () ++ pr_id id ++ spc () ++
  str "is used more than once."

let error_same_names_constructors id =
  str "The constructor name" ++ spc () ++ pr_id id ++ spc () ++
  str "is used more than once."

let error_same_names_overlap idl =
  strbrk "The following names are used both as type names and constructor " ++
  str "names:" ++ spc () ++
  prlist_with_sep pr_comma pr_id idl ++ str "."

let error_not_an_arity id =
  str "The type of" ++ spc () ++ pr_id id ++ spc () ++ str "is not an arity."

let error_bad_entry () =
  str "Bad inductive definition."

let error_large_non_prop_inductive_not_in_type () =
  str "Large non-propositional inductive types must be in Type."

(* Recursion schemes errors *)

let error_not_allowed_case_analysis isrec kind i =
  str (if isrec then "Induction" else "Case analysis") ++
  strbrk " on sort " ++ pr_sort kind ++
  strbrk " is not allowed for inductive definition " ++
  pr_inductive (Global.env()) i ++ str "."

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
  | LargeNonPropInductiveNotInType -> error_large_non_prop_inductive_not_in_type ()

(* Recursion schemes errors *)

let explain_recursion_scheme_error = function
  | NotAllowedCaseAnalysis (isrec,k,i) ->
      error_not_allowed_case_analysis isrec k i
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
  if n = 0 then "no "^s^"s"
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
    str "For " ++ pr_lconstr_env env cstr ++ str ": " ++ pr_lconstr_env env typ
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

let explain_ltac_call_trace (nrep,last,trace,loc) =
  let calls =
    (nrep,last) :: List.rev (List.map(fun(n,_,ck)->(n,ck))trace) in
  let pr_call (n,ck) =
    (match ck with
       | Proof_type.LtacNotationCall s -> quote (str s)
       | Proof_type.LtacNameCall cst -> quote (Pptactic.pr_ltac_constant cst)
       | Proof_type.LtacVarCall (id,t) ->
	   quote (Nameops.pr_id id) ++ strbrk " (bound to " ++
	     Pptactic.pr_glob_tactic (Global.env()) t ++ str ")"
       | Proof_type.LtacAtomCall (te,otac) -> quote
	   (Pptactic.pr_glob_tactic (Global.env())
	      (Tacexpr.TacAtom (dummy_loc,te)))
	   ++ (match !otac with
		 | Some te' when (Obj.magic te' <> te) ->
		     strbrk " (expanded to " ++ quote
		       (Pptactic.pr_tactic (Global.env())
			  (Tacexpr.TacAtom (dummy_loc,te')))
		     ++ str ")"
		 | _ -> mt ())
       | Proof_type.LtacConstrInterp (c,(vars,unboundvars)) ->
	   let filter =
	     function (id,None) -> None | (id,Some id') -> Some(id,([],mkVar id')) in
	   let unboundvars = list_map_filter filter unboundvars in
	   quote (pr_rawconstr_env (Global.env()) c) ++
	     (if unboundvars <> [] or vars <> [] then
		strbrk " (with " ++
		  prlist_with_sep pr_comma
		  (fun (id,c) ->
		     pr_id id ++ str ":=" ++ Printer.pr_lconstr_under_binders c)
		  (List.rev vars @ unboundvars) ++ str ")"
	      else mt())) ++
      (if n=2 then str " (repeated twice)"
       else if n>2 then str " (repeated "++int n++str" times)"
       else mt()) in
    if calls <> [] then
      let kind_of_last_call = match list_last calls with
    | (_,Proof_type.LtacConstrInterp _) -> ", last term evaluation failed."
    | _ -> ", last call failed." in
    hov 0 (str "In nested Ltac calls to " ++
           pr_enum pr_call calls ++ strbrk kind_of_last_call)
  else
    mt ()
