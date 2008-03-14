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
    let ptyp = P.pr_term k env typ in 
    (spc () ++ pr_id s ++ str" : " ++ ptyp)
  
  let print_binding k env = function
    | Anonymous,ty -> 
	(spc () ++ str"_" ++ str" : " ++ P.pr_term k env ty)
    | Name id,ty -> 
	(spc () ++ pr_id id ++ str" : " ++ P.pr_term k env ty)

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
           let pidt =  print_decl k env (id,t) in (pps ++ fnl () ++ pidt))
	env (mt ()) 
    in
    let db_env =
      fold_rel_context
	(fun env (na,_,t) pps ->
           let pnat = print_binding k env (na,t) in (pps ++ fnl () ++ pnat))
	env (mt ())
    in 
    (sign_env ++ db_env)
    
  let pr_ne_ctx header k env =
    if rel_context env = [] && named_context env = [] then
      (mt ())
    else
      (header ++ pr_env k env)


let explain_unbound_rel k ctx n =
  let pe = pr_ne_ctx (str"in environment") k ctx in
  (str"Unbound reference: " ++ pe ++ fnl () ++
     str"The reference " ++ int n ++ str" is free")

let explain_not_type k ctx c =
  let pe = pr_ne_ctx (str"In environment") k ctx in
  let pc = P.pr_term k ctx c in
  (pe ++ cut () ++ str "the term" ++ brk(1,1) ++ pc ++ spc () ++
     str"should be typed by Set, Prop or Type.");;

let explain_bad_assumption k ctx c =
  let pc = P.pr_term k ctx c in
  (str "Cannot declare a variable or hypothesis over the term" ++
     brk(1,1) ++ pc ++ spc () ++ str "because this term is not a type.");;

let explain_reference_variables id =
  (str "the constant" ++ spc () ++ pr_id id ++ spc () ++ 
     str "refers to variables which are not in the context")

let msg_bad_elimination ctx k = function
  | Some(ki,kp,explanation) ->
      let pki = P.pr_term k ctx ki in
      let pkp = P.pr_term k ctx kp in
      (hov 0 
         (fnl () ++ str "Elimination of an inductive object of sort : " ++
            pki ++ brk(1,0) ++
            str "is not allowed on a predicate in sort : " ++ pkp ++fnl () ++
            str "because" ++ spc () ++ str explanation))
  | None -> 
      (mt ())

let explain_elim_arity k ctx ind aritylst c pj okinds = 
  let pi = P.pr_term k ctx ind in
  let ppar = prlist_with_sep pr_coma (P.pr_term k ctx) aritylst in
  let pc = P.pr_term k ctx c in
  let pp = P.pr_term k ctx pj.uj_val in
  let ppt = P.pr_term k ctx pj.uj_type in
  (str "Incorrect elimination of" ++ brk(1,1) ++ pc ++ spc () ++
     str "in the inductive type" ++ brk(1,1) ++ pi ++ fnl () ++
     str "The elimination predicate" ++ brk(1,1) ++ pp ++ spc () ++
     str "has type" ++ brk(1,1) ++ ppt ++ fnl () ++
     str "It should be one of :" ++ brk(1,1) ++ hov 0 ppar ++ fnl () ++
     msg_bad_elimination ctx k okinds)

let explain_case_not_inductive k ctx cj =
  let pc = P.pr_term k ctx cj.uj_val in
  let pct = P.pr_term k ctx cj.uj_type in
  (str "In Cases expression" ++ brk(1,1) ++ pc ++ spc () ++ 
     str "has type" ++ brk(1,1) ++ pct ++ spc () ++ 
     str "which is not an inductive definition")
  
let explain_number_branches k ctx cj expn =
  let pc = P.pr_term k ctx cj.uj_val in
  let pct = P.pr_term k ctx cj.uj_val in
  (str "Cases on term" ++ brk(1,1) ++ pc ++ spc () ++
     str "of type" ++ brk(1,1) ++ pct ++ spc () ++
     str "expects " ++  int expn ++ str " branches")

let explain_ill_formed_branch k ctx c i actty expty =
  let pc = P.pr_term k ctx c in
  let pa = P.pr_term k ctx actty in
  let pe = P.pr_term k ctx expty in
  (str "In Cases expression on term" ++ brk(1,1) ++ pc ++
     spc () ++ str "the branch " ++ int (i+1) ++
     str " has type" ++ brk(1,1) ++ pa ++ spc () ++ 
     str "which should be:" ++ brk(1,1) ++ pe)

let explain_generalization k ctx (name,var) c =
  let pe = pr_ne_ctx (str"in environment") k ctx in
  let pv = P.pr_term k ctx var in
  let pc = P.pr_term k (push_rel (name,None,var) ctx) c in
  (str"Illegal generalization: " ++ pe ++ fnl () ++
     str"Cannot generalize" ++ brk(1,1) ++ pv ++ spc () ++
     str"over" ++ brk(1,1) ++ pc ++ spc () ++
     str"which should be typed by Set, Prop or Type.")

let explain_actual_type k ctx c ct pt =
  let pe = pr_ne_ctx (str"In environment") k ctx in
  let pc = P.pr_term k ctx c in
  let pct = P.pr_term k ctx ct in
  let pt = P.pr_term k ctx pt in
  (pe ++ fnl () ++
     str"The term" ++ brk(1,1) ++ pc ++ spc () ++
     str"does not have type" ++ brk(1,1) ++ pt ++ fnl () ++
     str"Actually, it has type" ++ brk(1,1) ++ pct)

let explain_cant_apply_bad_type k ctx (n,exptyp,actualtyp) rator randl =
  let ctx = make_all_name_different ctx in
  let pe = pr_ne_ctx (str"in environment") k ctx in
  let pr = pr_term k ctx rator.uj_val in
  let prt = pr_term k ctx rator.uj_type in
  let term_string = if List.length randl > 1 then "terms" else "term" in
  let many = match n mod 10 with 1 -> "st" | 2 -> "nd" | _ -> "th" in
  let appl = prlist_with_sep pr_fnl 
	       (fun c ->
		  let pc = pr_term k ctx c.uj_val in
		  let pct = pr_term k ctx c.uj_type in
		  hov 2 (pc ++ spc () ++ str": " ++ pct)) randl
  in
  (str"Illegal application (Type Error): " ++ pe ++ fnl () ++
     str"The term" ++ brk(1,1) ++ pr ++ spc () ++
     str"of type" ++ brk(1,1) ++ prt ++ spc () ++
     str("cannot be applied to the "^term_string) ++ fnl () ++ 
     str" " ++ v 0 appl ++ fnl () ++
     str"The " ++int n ++ str (many^" term of type ") ++
     pr_term k ctx actualtyp ++
     str" should be of type " ++ pr_term k ctx exptyp)

let explain_cant_apply_not_functional k ctx rator randl =
  let ctx = make_all_name_different ctx in
  let pe = pr_ne_ctx (str"in environment") k ctx in
  let pr = pr_term k ctx rator.uj_val in
  let prt = pr_term k ctx rator.uj_type in
  let term_string = if List.length randl > 1 then "terms" else "term" in
  let appl = prlist_with_sep pr_fnl 
	       (fun c ->
		  let pc = pr_term k ctx c.uj_val in
		  let pct = pr_term k ctx c.uj_type in
		  hov 2 (pc ++ spc () ++ str": " ++ pct)) randl
  in
  (str"Illegal application (Non-functional construction): " ++ pe ++ fnl () ++
     str"The term" ++ brk(1,1) ++ pr ++ spc () ++
     str"of type" ++ brk(1,1) ++ prt ++ spc () ++
     str("cannot be applied to the "^term_string) ++ fnl () ++ 
     str" " ++ v 0 appl ++ fnl ())

(* (co)fixpoints *)
let explain_ill_formed_rec_body k ctx err names i vdefs =
  let str = match err with

  (* Fixpoint guard errors *)
  | NotEnoughAbstractionInFixBody ->
      (str "Not enough abstractions in the definition")
  | RecursionNotOnInductiveType ->
      (str "Recursive definition on a non inductive type")
  | RecursionOnIllegalTerm ->
      (str "Recursive call applied to an illegal term")
  | NotEnoughArgumentsForFixCall ->
      (str "Not enough arguments for the recursive call")

  (* CoFixpoint guard errors *)
  (* TODO : récupérer le contexte des termes pour pouvoir les afficher *)
  | CodomainNotInductiveType c ->
      (str "The codomain is" ++ spc () ++ P.pr_term k ctx c ++ spc () ++
	 str "which should be a coinductive type")
  | NestedRecursiveOccurrences ->
      (str "Nested recursive occurrences")
  | UnguardedRecursiveCall c ->
      (str "Unguarded recursive call")
  | RecCallInTypeOfAbstraction c ->
      (str "Not allowed recursive call in the domain of an abstraction")
  | RecCallInNonRecArgOfConstructor c ->
      (str "Not allowed recursive call in a non-recursive argument of constructor")
  | RecCallInTypeOfDef c ->
      (str "Not allowed recursive call in the type of a recursive definition")
  | RecCallInCaseFun c ->
      (str "Not allowed recursive call in a branch of cases")
  | RecCallInCaseArg c -> 
      (str "Not allowed recursive call in the argument of cases")
  | RecCallInCasePred c ->
      (str "Not allowed recursive call in the type of cases in")
  | NotGuardedForm c ->
      str "Sub-expression " ++ pr_lconstr_env ctx c ++ spc() ++
      str "not in guarded form (should be a constructor, Cases or CoFix)"
in
  let pvd = P.pr_term k ctx vdefs.(i) in
  let s =
    match names.(i) with Name id -> string_of_id id | Anonymous -> "_" in
  (str ++ fnl () ++ str"The " ++
     if Array.length vdefs = 1 then (mt ()) else (int (i+1) ++ str "-th ") ++
     str"recursive definition" ++ spc () ++ str s ++
	 spc () ++ str":=" ++ spc () ++ pvd ++ spc () ++
     str "is not well-formed")
    
let explain_ill_typed_rec_body k ctx i lna vdefj vargs =
  let pvd = P.pr_term k ctx (vdefj.(i)).uj_val in
  let pvdt = P.pr_term k ctx (vdefj.(i)).uj_type in
  let pv = P.pr_term k ctx vargs.(i) in
  (str"The " ++
     if Array.length vdefj = 1 then (mt ()) else (int (i+1) ++ str "-th") ++
     str"recursive definition" ++ spc () ++ pvd ++ spc () ++
     str "has type" ++ spc () ++ pvdt ++spc () ++ str "it should be" ++ spc () ++ pv)

let explain_not_inductive k ctx c =
  let pc = P.pr_term k ctx c in
  (str"The term" ++ brk(1,1) ++ pc ++ spc () ++
     str "is not an inductive definition")

let explain_ml_case k ctx mes c ct br brt =
  let pc = P.pr_term k ctx c in
  let pct = P.pr_term k ctx ct in
  let expln =
    match mes with
      | "Inductive" -> (pct ++ str "is not an inductive definition")
      | "Predicate" -> (str "ML case not allowed on a predicate")
      | "Absurd" -> (str "Ill-formed case expression on an empty type")
      | "Decomp" ->
          let plf = P.pr_term k ctx br in
          let pft = P.pr_term k ctx brt in
          (str "The branch " ++ plf ++ ws 1 ++ cut () ++ str "has type " ++ pft ++
             ws 1 ++ cut () ++
             str "does not correspond to the inductive definition")
      | "Dependent" ->
          (str "ML case not allowed for a dependent case elimination")
      | _ -> (mt ())
  in
  hov 0 (str "In ML case expression on " ++ pc ++ ws 1 ++ cut () ++
           str "of type" ++  ws 1 ++ pct ++ ws 1 ++ cut () ++ 
           str "which is an inductive predicate." ++ fnl () ++ expln)

let explain_type_error k ctx = function
  | UnboundRel n -> 
      explain_unbound_rel k ctx n
  | NotAType c -> 
      explain_not_type k ctx c.uj_val
  | BadAssumption c -> 
      explain_bad_assumption k ctx c
  | ReferenceVariables id -> 
      explain_reference_variables id
  | ElimArity (ind, aritylst, c, pj, okinds) ->
      explain_elim_arity k ctx (mkMutInd ind) aritylst c pj okinds 
  | CaseNotInductive cj -> 
      explain_case_not_inductive k ctx cj
  | NumberBranches (cj, n) -> 
      explain_number_branches k ctx cj n
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
(*
  | NotInductive c ->
      explain_not_inductive k ctx c
  | MLCase (mes,c,ct,br,brt) ->
      explain_ml_case k ctx mes c ct br brt
*)
  | _ -> 
      (str "Unknown type error (TODO)")

let explain_refiner_bad_type k ctx arg ty conclty =
  errorlabstrm "Logic.conv_leq_goal"
    (str"refiner was given an argument" ++ brk(1,1) ++ 
       P.pr_term k ctx arg ++ spc () ++
       str"of type" ++ brk(1,1) ++ P.pr_term k ctx ty ++ spc () ++
       str"instead of" ++ brk(1,1) ++ P.pr_term k ctx conclty)

let explain_refiner_occur_meta k ctx t =
  errorlabstrm "Logic.mk_refgoals"
    (str"cannot refine with term" ++ brk(1,1) ++ P.pr_term k ctx t ++
       spc () ++ str"because there are metavariables, and it is" ++
       spc () ++ str"neither an application nor a Case")

let explain_refiner_cannot_applt k ctx t harg =
  errorlabstrm "Logic.mkARGGOALS"
    (str"in refiner, a term of type " ++ brk(1,1) ++
       P.pr_term k ctx t ++ spc () ++ str"could not be applied to" ++ brk(1,1) ++
       P.pr_term k ctx harg)

let explain_occur_check k ctx ev rhs =
  let id = "?" ^ string_of_int ev in
  let pt = P.pr_term k ctx rhs in
  errorlabstrm "Trad.occur_check"
    (str"Occur check failed: tried to define " ++ str id ++
      str" with term" ++ brk(1,1) ++ pt)

let explain_not_clean k ctx sp t =
  let c = mkRel (Intset.choose (free_rels t)) in
  let id = string_of_id (Names.basename sp) in
  let var = P.pr_term k ctx c in
  errorlabstrm "Trad.not_clean"
    (str"Tried to define " ++ str id ++
       str" with a term using variable " ++ var ++ spc () ++
       str"which is not in its scope.")

end
