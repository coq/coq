
(* $Id$ *)

open Pp
open Util
open Names
open Term
open Sign
open Environ
open Type_errors
open Reduction
open G_minicoq

module type Printer = sig
  val pr_term : path_kind -> env -> constr -> std_ppcmds
end

module Make = functor (P : Printer) -> struct

  let print_decl k env (s,typ) =
    let ptyp = P.pr_term k env (body_of_type typ) in 
    [< 'sPC; print_id s; 'sTR" : "; ptyp >]
  
  let print_binding k env = function
    | Anonymous,ty -> 
	[< 'sPC; 'sTR"_" ; 'sTR" : " ; P.pr_term k env (body_of_type ty) >]
    | Name id,ty -> 
	[< 'sPC; print_id id ; 'sTR" : "; P.pr_term k env (body_of_type ty) >]

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
      
  let pr_env k env =
    let sign_env =
      fold_named_context
	(fun env (id,_,t) pps ->
           let pidt =  print_decl k env (id,t) in [<  pps ; 'fNL ; pidt >])
	env [< >] 
    in
    let db_env =
      fold_rel_context
	(fun env (na,_,t) pps ->
           let pnat = print_binding k env (na,t) in [<  pps ; 'fNL ; pnat >])
	env [< >]
    in 
    [< sign_env; db_env >]
    
  let pr_ne_ctx header k env =
    if rel_context env = [] && named_context env = [] then
      [< >]
    else
      [< header; pr_env k env >]


let explain_unbound_rel k ctx n =
  let pe = pr_ne_ctx [< 'sTR"in environment" >] k ctx in
  [< 'sTR"Unbound reference: "; pe; 'fNL;
     'sTR"The reference "; 'iNT n; 'sTR" is free" >]

let explain_not_type k ctx c =
  let pe = pr_ne_ctx [< 'sTR"In environment" >] k ctx in
  let pc = P.pr_term k ctx c in
  [< pe; 'cUT; 'sTR "the term"; 'bRK(1,1); pc; 'sPC;
     'sTR"should be typed by Set, Prop or Type." >];;

let explain_bad_assumption k ctx c =
  let pc = P.pr_term k ctx c in
  [< 'sTR "Cannot declare a variable or hypothesis over the term";
     'bRK(1,1); pc; 'sPC; 'sTR "because this term is not a type." >];;

let explain_reference_variables id =
  [< 'sTR "the constant"; 'sPC; print_id id; 'sPC; 
     'sTR "refers to variables which are not in the context" >]

let msg_bad_elimination ctx k = function
  | Some(ki,kp,explanation) ->
      let pki = P.pr_term k ctx ki in
      let pkp = P.pr_term k ctx kp in
      (hOV 0 
         [< 'fNL; 'sTR "Elimination of an inductive object of sort : ";
            pki; 'bRK(1,0);
            'sTR "is not allowed on a predicate in sort : "; pkp ;'fNL;
            'sTR "because"; 'sPC; 'sTR explanation >])
  | None -> 
      [<>]

let explain_elim_arity k ctx ind aritylst c p pt okinds = 
  let pi = P.pr_term k ctx ind in
  let ppar = prlist_with_sep pr_coma (P.pr_term k ctx) aritylst in
  let pc = P.pr_term k ctx c in
  let pp = P.pr_term k ctx p in
  let ppt = P.pr_term k ctx pt in
  [< 'sTR "Incorrect elimination of"; 'bRK(1,1); pc; 'sPC;
     'sTR "in the inductive type"; 'bRK(1,1); pi; 'fNL;
     'sTR "The elimination predicate"; 'bRK(1,1); pp; 'sPC;
     'sTR "has type"; 'bRK(1,1); ppt; 'fNL;
     'sTR "It should be one of :"; 'bRK(1,1) ; hOV 0 ppar; 'fNL;
     msg_bad_elimination ctx k okinds >]

let explain_case_not_inductive k ctx c ct =
  let pc = P.pr_term k ctx c in
  let pct = P.pr_term k ctx ct in
  [< 'sTR "In Cases expression"; 'bRK(1,1); pc; 'sPC; 
     'sTR "has type"; 'bRK(1,1); pct; 'sPC; 
     'sTR "which is not an inductive definition" >]
  
let explain_number_branches k ctx c ct expn =
  let pc = P.pr_term k ctx c in
  let pct = P.pr_term k ctx ct in
  [< 'sTR "Cases on term"; 'bRK(1,1); pc; 'sPC ;
     'sTR "of type"; 'bRK(1,1); pct; 'sPC;
     'sTR "expects ";  'iNT expn; 'sTR " branches" >]

let explain_ill_formed_branch k ctx c i actty expty =
  let pc = P.pr_term k ctx c in
  let pa = P.pr_term k ctx actty in
  let pe = P.pr_term k ctx expty in
  [< 'sTR "In Cases expression on term"; 'bRK(1,1); pc;
     'sPC; 'sTR "the branch " ; 'iNT (i+1);
     'sTR " has type"; 'bRK(1,1); pa ; 'sPC; 
     'sTR "which should be:"; 'bRK(1,1); pe >]

let explain_generalization k ctx (name,var) c =
  let pe = pr_ne_ctx [< 'sTR"in environment" >] k ctx in
  let pv = P.pr_term k ctx (body_of_type var) in
  let pc = P.pr_term k (push_rel (name,None,var) ctx) c in
  [< 'sTR"Illegal generalization: "; pe; 'fNL;
     'sTR"Cannot generalize"; 'bRK(1,1); pv; 'sPC;
     'sTR"over"; 'bRK(1,1); pc; 'sPC;
     'sTR"which should be typed by Set, Prop or Type." >]

let explain_actual_type k ctx c ct pt =
  let pe = pr_ne_ctx [< 'sTR"In environment" >] k ctx in
  let pc = P.pr_term k ctx c in
  let pct = P.pr_term k ctx ct in
  let pt = P.pr_term k ctx pt in
  [< pe; 'fNL;
     'sTR"The term"; 'bRK(1,1); pc ; 'sPC ;
     'sTR"does not have type"; 'bRK(1,1); pt; 'fNL;
     'sTR"Actually, it has type" ; 'bRK(1,1); pct >]

let explain_cant_apply_bad_type k ctx (n,exptyp,actualtyp) rator randl =
  let ctx = make_all_name_different ctx in
  let pe = pr_ne_ctx [< 'sTR"in environment" >] k ctx in
  let pr = pr_term k ctx rator.uj_val in
  let prt = pr_term k ctx (body_of_type rator.uj_type) in
  let term_string = if List.length randl > 1 then "terms" else "term" in
  let many = match n mod 10 with 1 -> "st" | 2 -> "nd" | _ -> "th" in
  let appl = prlist_with_sep pr_fnl 
	       (fun c ->
		  let pc = pr_term k ctx c.uj_val in
		  let pct = pr_term k ctx (body_of_type c.uj_type) in
		  hOV 2 [< pc; 'sPC; 'sTR": " ; pct >]) randl
  in
  [< 'sTR"Illegal application (Type Error): "; pe; 'fNL;
     'sTR"The term"; 'bRK(1,1); pr; 'sPC;
     'sTR"of type"; 'bRK(1,1); prt; 'sPC ;
     'sTR("cannot be applied to the "^term_string); 'fNL; 
     'sTR" "; v 0 appl; 'fNL;
     'sTR"The ";'iNT n; 'sTR (many^" term of type ");
     pr_term k ctx actualtyp;
     'sTR" should be of type "; pr_term k ctx exptyp >]

let explain_cant_apply_not_functional k ctx rator randl =
  let ctx = make_all_name_different ctx in
  let pe = pr_ne_ctx [< 'sTR"in environment" >] k ctx in
  let pr = pr_term k ctx rator.uj_val in
  let prt = pr_term k ctx (body_of_type rator.uj_type) in
  let term_string = if List.length randl > 1 then "terms" else "term" in
  let appl = prlist_with_sep pr_fnl 
	       (fun c ->
		  let pc = pr_term k ctx c.uj_val in
		  let pct = pr_term k ctx (body_of_type c.uj_type) in
		  hOV 2 [< pc; 'sPC; 'sTR": " ; pct >]) randl
  in
  [< 'sTR"Illegal application (Non-functional construction): "; pe; 'fNL;
     'sTR"The term"; 'bRK(1,1); pr; 'sPC;
     'sTR"of type"; 'bRK(1,1); prt; 'sPC ;
     'sTR("cannot be applied to the "^term_string); 'fNL; 
     'sTR" "; v 0 appl; 'fNL >]

(* (co)fixpoints *)
let explain_ill_formed_rec_body k ctx err lna i vdefs =
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
  (* TODO : récupérer le contexte des termes pour pouvoir les afficher *)
  | CodomainNotInductiveType c ->
      [< 'sTR "The codomain is"; 'sPC; P.pr_term k ctx c; 'sPC;
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
  let pvd = P.pr_term k ctx vdefs.(i) in
  let s =
    match List.nth lna i with Name id -> string_of_id id | Anonymous -> "_" in
  [< str; 'fNL; 'sTR"The ";
     if Array.length vdefs = 1 then [<>] else [<'iNT (i+1); 'sTR "-th ">];
     'sTR"recursive definition"; 'sPC; 'sTR s;
	 'sPC ; 'sTR":="; 'sPC ; pvd; 'sPC;
     'sTR "is not well-formed" >]
    
let explain_ill_typed_rec_body k ctx i lna vdefj vargs =
  let pvd = P.pr_term k ctx (vdefj.(i)).uj_val in
  let pvdt = P.pr_term k ctx (body_of_type (vdefj.(i)).uj_type) in
  let pv = P.pr_term k ctx (body_of_type vargs.(i)) in
  [< 'sTR"The " ;
     if Array.length vdefj = 1 then [<>] else [<'iNT (i+1); 'sTR "-th">];
     'sTR"recursive definition" ; 'sPC; pvd; 'sPC;
     'sTR "has type"; 'sPC; pvdt;'sPC; 'sTR "it should be"; 'sPC; pv >]

let explain_not_inductive k ctx c =
  let pc = P.pr_term k ctx c in
  [< 'sTR"The term"; 'bRK(1,1); pc; 'sPC;
     'sTR "is not an inductive definition" >]

let explain_ml_case k ctx mes c ct br brt =
  let pc = P.pr_term k ctx c in
  let pct = P.pr_term k ctx ct in
  let expln =
    match mes with
      | "Inductive" -> [< pct; 'sTR "is not an inductive definition">]
      | "Predicate" -> [< 'sTR "ML case not allowed on a predicate">]
      | "Absurd" -> [< 'sTR "Ill-formed case expression on an empty type" >]
      | "Decomp" ->
          let plf = P.pr_term k ctx br in
          let pft = P.pr_term k ctx brt in
          [< 'sTR "The branch "; plf; 'wS 1; 'cUT; 'sTR "has type "; pft;
             'wS 1; 'cUT;
             'sTR "does not correspond to the inductive definition" >]
      | "Dependent" ->
          [< 'sTR "ML case not allowed for a dependent case elimination">]
      | _ -> [<>]
  in
  hOV 0 [< 'sTR "In ML case expression on "; pc; 'wS 1; 'cUT ;
           'sTR "of type";  'wS 1; pct; 'wS 1; 'cUT; 
           'sTR "which is an inductive predicate."; 'fNL; expln >]
(*
let explain_cant_find_case_type loc k ctx c =
  let pe = P.pr_term k ctx c in
  Ast.user_err_loc
    (loc,"pretype",
     hOV 3 [<'sTR "Cannot infer type of whole Case expression on"; 
	     'wS 1; pe >])
*)
let explain_type_error k ctx = function
  | UnboundRel n -> 
      explain_unbound_rel k ctx n
  | NotAType c -> 
      explain_not_type k ctx c.uj_val
  | BadAssumption c -> 
      explain_bad_assumption k ctx c
  | ReferenceVariables id -> 
      explain_reference_variables id
  | ElimArity (ind, aritylst, c, p, pt, okinds) ->
      explain_elim_arity k ctx (mkMutInd ind) aritylst c p pt okinds 
  | CaseNotInductive (c, ct) -> 
      explain_case_not_inductive k ctx c ct
  | NumberBranches (c, ct, n) -> 
      explain_number_branches k ctx c ct n
  | IllFormedBranch (c, i, actty, expty) -> 
      explain_ill_formed_branch k ctx c i actty expty 
  | Generalization (nvar, c) ->
      explain_generalization k ctx nvar c.uj_val
  | ActualType (c, ct, pt) -> 
      explain_actual_type k ctx c ct pt
  | CantApplyBadType (s, rator, randl) ->
      explain_cant_apply_bad_type k ctx s rator randl
  | CantApplyNonFunctional (rator, randl) ->
      explain_cant_apply_not_functional k ctx rator randl
  | IllFormedRecBody (i, lna, vdefj, vargs) ->
      explain_ill_formed_rec_body k ctx i lna vdefj vargs
  | IllTypedRecBody (i, lna, vdefj, vargs) ->
      explain_ill_typed_rec_body k ctx i lna vdefj vargs
  | NotInductive c ->
      explain_not_inductive k ctx c
  | MLCase (mes,c,ct,br,brt) ->
      explain_ml_case k ctx mes c ct br brt
  | _ -> 
      [< 'sTR "Unknown type error (TODO)" >]

let explain_refiner_bad_type k ctx arg ty conclty =
  errorlabstrm "Logic.conv_leq_goal"
    [< 'sTR"refiner was given an argument"; 'bRK(1,1); 
       P.pr_term k ctx arg; 'sPC;
       'sTR"of type"; 'bRK(1,1); P.pr_term k ctx ty; 'sPC;
       'sTR"instead of"; 'bRK(1,1); P.pr_term k ctx conclty >]

let explain_refiner_occur_meta k ctx t =
  errorlabstrm "Logic.mk_refgoals"
    [< 'sTR"cannot refine with term"; 'bRK(1,1); P.pr_term k ctx t;
       'sPC; 'sTR"because there are metavariables, and it is";
       'sPC; 'sTR"neither an application nor a Case" >]

let explain_refiner_cannot_applt k ctx t harg =
  errorlabstrm "Logic.mkARGGOALS"
    [< 'sTR"in refiner, a term of type "; 'bRK(1,1);
       P.pr_term k ctx t; 'sPC; 'sTR"could not be applied to"; 'bRK(1,1);
       P.pr_term k ctx harg >]

let explain_occur_check k ctx ev rhs =
  let id = "?" ^ string_of_int ev in
  let pt = P.pr_term k ctx rhs in
  errorlabstrm "Trad.occur_check"
    [< 'sTR"Occur check failed: tried to define "; 'sTR id;
      'sTR" with term"; 'bRK(1,1); pt >]

let explain_not_clean k ctx sp t =
  let c = Rel (Intset.choose (free_rels t)) in
  let id = string_of_id (Names.basename sp) in
  let var = P.pr_term k ctx c in
  errorlabstrm "Trad.not_clean"
    [< 'sTR"Tried to define "; 'sTR id;
       'sTR" with a term using variable "; var; 'sPC;
       'sTR"which is not in its scope." >]

end
