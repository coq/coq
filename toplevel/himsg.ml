
(* $Id$ *)

open Pp
open Util
open Names
open Generic
open Term
open Sign
open Environ
open Type_errors
open Reduction

module type Printer = sig
  val pr_term : path_kind -> context -> constr -> std_ppcmds
  val pr_ne_ctx : std_ppcmds -> path_kind -> context -> std_ppcmds
end

module Make = functor (P : Printer) -> struct

let explain_unbound_rel k ctx n =
  let pe = P.pr_ne_ctx [< 'sTR"in environment" >] k ctx in
  errorlabstrm "unbound rel"
    [< 'sTR"Unbound reference: "; pe; 'fNL;
       'sTR"The reference "; 'iNT n; 'sTR" is free" >]

let explain_cant_execute k ctx c =
  let tc = P.pr_term k ctx c in
  errorlabstrm "Cannot execute"
    [< 'sTR"Cannot execute term:"; 'bRK(1,1); tc >]

let explain_not_type k ctx c =
  let pe = P.pr_ne_ctx [< 'sTR"In environment" >] k ctx in
  let pc = P.pr_term k ctx c in
  errorlabstrm "Not a type"
    [< pe; 'cUT; 'sTR "the term"; 'bRK(1,1); pc; 'sPC;
       'sTR"should be typed by Set, Prop or Type." >];;

let explain_bad_assumption k ctx c =
  let pc = P.pr_term k ctx c in
  errorlabstrm "Bad assumption"
    [< 'sTR "Cannot declare a variable or hypothesis over the term";
       'bRK(1,1); pc; 'sPC; 'sTR "because this term is not a type." >];;

let explain_reference_variables id =
  errorlabstrm "construct_reference" 
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
  | None -> [<>]

let explain_elim_arity k ctx ind aritylst c p pt okinds = 
  let pi = P.pr_term k ctx ind in
  let ppar = prlist_with_sep pr_coma (P.pr_term k ctx) aritylst in
  let pc = P.pr_term k ctx c in
  let pp = P.pr_term k ctx p in
  let ppt = P.pr_term k ctx pt in
  errorlabstrm "incorrect elimimnation arity"
    [< 'sTR "Incorrect elimination of"; 'bRK(1,1); pc; 'sPC;
       'sTR "in the inductive type"; 'bRK(1,1); pi; 'fNL;
       'sTR "The elimination predicate"; 'bRK(1,1); pp; 'sPC;
       'sTR "has type"; 'bRK(1,1); ppt; 'fNL;
       'sTR "It should be one of :"; 'bRK(1,1) ; hOV 0 ppar; 'fNL;
       msg_bad_elimination ctx k okinds >]

let explain_case_not_inductive k ctx c ct =
  let pc = P.pr_term k ctx c in
  let pct = P.pr_term k ctx ct in
  errorlabstrm "Cases on non inductive type"
    [< 'sTR "In Cases expression"; 'bRK(1,1); pc; 'sPC; 
       'sTR "has type"; 'bRK(1,1); pct; 'sPC; 
       'sTR "which is not an inductive definition" >]

let explain_number_branches k ctx c ct expn =
  let pc = P.pr_term k ctx c in
  let pct = P.pr_term k ctx ct in
  errorlabstrm "Cases with wrong number of cases"
    [< 'sTR "Cases on term"; 'bRK(1,1); pc; 'sPC ;
       'sTR "of type"; 'bRK(1,1); pct; 'sPC;
       'sTR "expects ";  'iNT expn; 'sTR " branches" >]

let explain_ill_formed_branch k ctx c i actty expty =
  let pc = P.pr_term k ctx c in
  let pa = P.pr_term k ctx actty in
  let pe = P.pr_term k ctx expty in
  errorlabstrm "Ill-formed branches" 
    [< 'sTR "In Cases expression on term"; 'bRK(1,1); pc;
       'sPC; 'sTR "the branch " ; 'iNT (i+1);
       'sTR " has type"; 'bRK(1,1); pa ; 'sPC; 
       'sTR "which should be:"; 'bRK(1,1); pe >]

let explain_generalization k ctx (name,var) c =
  let pe = P.pr_ne_ctx [< 'sTR"in environment" >] k ctx in
  let pv = P.pr_term k ctx var.body in
  let pc = P.pr_term k (add_rel (name,var) ctx) c in
  errorlabstrm "P.rel"
    [< 'sTR"Illegal generalization: "; pe; 'fNL;
       'sTR"Cannot generalize"; 'bRK(1,1); pv; 'sPC;
       'sTR"over"; 'bRK(1,1); pc; 'sPC;
       'sTR"which should be typed by Set, Prop or Type." >]

let explain_actual_type k ctx c ct pt =
  let pe = P.pr_ne_ctx [< 'sTR"In environment" >] k ctx in
  let pc = P.pr_term k ctx c in
  let pct = P.pr_term k ctx ct in
  let pt = P.pr_term k ctx pt in
  errorlabstrm "Bad cast"
    [< pe; 'fNL;
       'sTR"The term"; 'bRK(1,1); pc ; 'sPC ;
       'sTR"does not have type"; 'bRK(1,1); pt; 'fNL;
       'sTR"Actually, it has type" ; 'bRK(1,1); pct >]

let explain_cant_apply k ctx s rator randl =
  let pe = P.pr_ne_ctx [< 'sTR"in environment" >] k ctx in
  let pr = P.pr_term k ctx rator.uj_val in
  let prt = P.pr_term k ctx rator.uj_type in
  let term_string = if List.length randl > 1 then "terms" else "term" in
  let appl = 
    prlist_with_sep pr_fnl
      (fun c ->
         let pc = P.pr_term k ctx c.uj_val in
         let pct = P.pr_term k ctx c.uj_type in
         hOV 2 [< pc; 'sPC; 'sTR": " ; pct >]) randl 
  in
  errorlabstrm "Illegal application"
    [< 'sTR"Illegal application ("; 'sTR s; 'sTR"): "; pe; 'fNL;
       'sTR"The term"; 'bRK(1,1); pr; 'sPC;
       'sTR"of type"; 'bRK(1,1); prt; 'sPC ;
       'sTR("cannot be applied to the "^term_string); 'fNL; 
       'sTR" "; v 0 appl >]

(* (co)fixpoints *)
let explain_ill_formed_rec_body k ctx str lna i vdefs =
  let pvd = P.pr_term k ctx vdefs.(i) in
  errorlabstrm "Ill-formed rec body"
    [< str; 'fNL; 'sTR"The ";
       if Array.length vdefs = 1 then [<>] else [<'iNT (i+1); 'sTR "-th ">];
       'sTR"recursive definition"; 'sPC ; pvd; 'sPC;
       'sTR "is not well-formed" >]
    
let explain_ill_typed_rec_body k ctx i lna vdefj vargs =
  let pvd = P.pr_term k ctx (vdefj.(i)).uj_val in
  let pvdt = P.pr_term k ctx (vdefj.(i)).uj_type in
  let pv = P.pr_term k ctx (body_of_type vargs.(i)) in
  errorlabstrm "Ill-typed rec body"
    [< 'sTR"The " ;
       if Array.length vdefj = 1 then [<>] else [<'iNT (i+1); 'sTR "-th">];
       'sTR"recursive definition" ; 'sPC; pvd; 'sPC;
       'sTR "has type"; 'sPC; pvdt;'sPC; 'sTR "it should be"; 'sPC; pv >]

let explain_type_error k ctx = function
  | UnboundRel n -> 
      explain_unbound_rel k ctx n
  | CantExecute c -> 
      explain_cant_execute k ctx c
  | NotAType c -> 
      explain_not_type k ctx c
  | BadAssumption c -> 
      explain_bad_assumption k ctx c
  | ReferenceVariables id -> 
      explain_reference_variables id
  | ElimArity (ind, aritylst, c, p, pt, okinds) ->
      explain_elim_arity k ctx ind aritylst c p pt okinds 
  | CaseNotInductive (c, ct) -> 
      explain_case_not_inductive k ctx c ct
  | NumberBranches (c, ct, n) -> 
      explain_number_branches k ctx c ct n
  | IllFormedBranch (c, i, actty, expty) -> 
      explain_ill_formed_branch k ctx c i actty expty 
  | Generalization (nvar, c) ->
      explain_generalization k ctx nvar c
  | ActualType (c, ct, pt) -> 
      explain_actual_type k ctx c ct pt
  | CantAply (s, rator, randl) ->
      explain_cant_apply k ctx s rator randl
  | IllFormedRecBody (i, lna, vdefj, vargs) ->
      explain_ill_formed_rec_body k ctx i lna vdefj vargs
  | IllTypedRecBody (i, lna, vdefj, vargs) ->
      explain_ill_typed_rec_body k ctx i lna vdefj vargs

end
