
(* $Id$ *)

open Pp
open Util
open Printer
open Generic
open Term
open Sign
open Environ
open Reduction

let error_unbound_rel k env n =
  let ctx = context env in
  let pe = pr_ne_env [< 'sTR"in environment" >] k ctx in
  errorlabstrm "unbound rel"
    [< 'sTR"Unbound reference: "; pe; 'fNL;
       'sTR"The reference "; 'iNT n; 'sTR" is free" >]

let error_cant_execute k env c =
  let tc = gen_pr_term k env c in
  errorlabstrm "Cannot execute"
    [< 'sTR"Cannot execute term:"; 'bRK(1,1); tc >]

let error_not_type k env c =
  let ctx = context env in
  let pe = pr_ne_env [< 'sTR"In environment" >] k ctx in
  let pc = gen_pr_term k env c in
  errorlabstrm "Not a type"
    [< pe; 'cUT; 'sTR "the term"; 'bRK(1,1); pc; 'sPC;
       'sTR"should be typed by Set, Prop or Type." >];;

let error_assumption k env c =
  let pc = gen_pr_term k env c in
  errorlabstrm "Bad assumption"
    [< 'sTR "Cannot declare a variable or hypothesis over the term";
       'bRK(1,1); pc; 'sPC; 'sTR "because this term is not a type." >];;

let error_reference_variables id =
  errorlabstrm "construct_reference" 
    [< 'sTR "the constant"; 'sPC; pr_id id; 'sPC; 
       'sTR "refers to variables which are not in the context" >]

let error_elim_expln env kp ki=
  if is_info_sort env kp && not (is_info_sort env ki) then
    "non-informative objects may not construct informative ones."
  else 
    match (kp,ki) with 
      | (DOP0(Sort (Type _)), DOP0(Sort (Prop _))) ->
          "strong elimination on non-small inductive types leads to paradoxes."
      | _ -> "wrong arity"

let msg_bad_elimination env k = function
  | Some(ki,kp,explanation) ->
      let pki = gen_pr_term k env ki in
      let pkp = gen_pr_term k env kp in
      (hOV 0 
         [< 'fNL; 'sTR "Elimination of an inductive object of sort : ";
            pki; 'bRK(1,0);
            'sTR "is not allowed on a predicate in sort : "; pkp ;'fNL;
            'sTR "because"; 'sPC; 'sTR explanation >])
  | None -> [<>]

let error_elim_arity k env ind aritylst c p pt okinds = 
  let pi = gen_pr_term k env ind in
  let ppar = prlist_with_sep pr_coma (gen_pr_term k env) aritylst in
  let pc = gen_pr_term k env c in
  let pp = gen_pr_term k env p in
  let ppt = gen_pr_term k env pt in
  errorlabstrm "incorrect elimimnation arity"
    [< 'sTR "Incorrect elimination of"; 'bRK(1,1); pc; 'sPC;
       'sTR "in the inductive type"; 'bRK(1,1); pi; 'fNL;
       'sTR "The elimination predicate"; 'bRK(1,1); pp; 'sPC;
       'sTR "has type"; 'bRK(1,1); ppt; 'fNL;
       'sTR "It should be one of :"; 'bRK(1,1) ; hOV 0 ppar; 'fNL;
       msg_bad_elimination env k okinds >]

let error_case_not_inductive k env c ct =
  let pc = gen_pr_term k env c in
  let pct = gen_pr_term k env ct in
  errorlabstrm "Cases on non inductive type"
    [< 'sTR "In Cases expression"; 'bRK(1,1); pc; 'sPC; 
       'sTR "has type"; 'bRK(1,1); pct; 'sPC; 
       'sTR "which is not an inductive definition" >]

let error_number_branches k env c ct expn =
  let pc = gen_pr_term k env c in
  let pct = gen_pr_term k env ct in
  errorlabstrm "Cases with wrong number of cases"
    [< 'sTR "Cases on term"; 'bRK(1,1); pc; 'sPC ;
       'sTR "of type"; 'bRK(1,1); pct; 'sPC;
       'sTR "expects ";  'iNT expn; 'sTR " branches" >]

let error_ill_formed_branch k env c i actty expty =
  let pc = gen_pr_term k env c in
  let pa = gen_pr_term k env actty in
  let pe = gen_pr_term k env expty in
  errorlabstrm "Ill-formed branches" 
    [< 'sTR "In Cases expression on term"; 'bRK(1,1); pc;
       'sPC; 'sTR "the branch " ; 'iNT (i+1);
       'sTR " has type"; 'bRK(1,1); pa ; 'sPC; 
       'sTR "which should be:"; 'bRK(1,1); pe >]

let error_generalization k env (name,var) c =
  let pe = pr_ne_env [< 'sTR"in environment" >] k (context env) in
  let pv = gen_pr_term k env var.body in
  let pc = gen_pr_term k (push_rel (name,var) env) c in
  errorlabstrm "gen_rel"
    [< 'sTR"Illegal generalization: "; pe; 'fNL;
       'sTR"Cannot generalize"; 'bRK(1,1); pv; 'sPC;
       'sTR"over"; 'bRK(1,1); pc; 'sPC;
       'sTR"which should be typed by Set, Prop or Type." >]

let error_actual_type k env cj tj =
  let pe = pr_ne_env [< 'sTR"In environment" >] k (context env) in
  let pc = gen_pr_term k env cj.uj_val in
  let pct = gen_pr_term k env cj.uj_type in
  let pt = gen_pr_term k env tj.uj_val in
  errorlabstrm "Bad cast"
    [< pe; 'fNL;
       'sTR"The term"; 'bRK(1,1); pc ; 'sPC ;
       'sTR"does not have type"; 'bRK(1,1); pt; 'fNL;
       'sTR"Actually, it has type" ; 'bRK(1,1); pct >]

let error_cant_apply s k env rator randl =
  let pe = pr_ne_env [< 'sTR"in environment" >] k (context env) in
  let pr = gen_pr_term k env rator.uj_val in
  let prt = gen_pr_term k env rator.uj_type in
  let term_string = if List.length randl > 1 then "terms" else "term" in
  let appl = 
    prlist_with_sep pr_fnl
      (fun c ->
         let pc = gen_pr_term k env c.uj_val in
         let pct = gen_pr_term k env c.uj_type in
         hOV 2 [< pc; 'sPC; 'sTR": " ; pct >]) randl 
  in
  errorlabstrm "Illegal application"
    [< 'sTR"Illegal application ("; 'sTR s; 'sTR"): "; pe; 'fNL;
       'sTR"The term"; 'bRK(1,1); pr; 'sPC;
       'sTR"of type"; 'bRK(1,1); prt; 'sPC ;
       'sTR("cannot be applied to the "^term_string); 'fNL; 
       'sTR" "; v 0 appl >]

(* (co)fixpoints *)
let error_ill_formed_rec_body str k env lna i vdefs =
  let pvd = gen_pr_term k env vdefs.(i) in
  errorlabstrm "Ill-formed rec body"
    [< str; 'fNL; 'sTR"The ";
       if Array.length vdefs = 1 then [<>] else [<'iNT (i+1); 'sTR "-th ">];
       'sTR"recursive definition"; 'sPC ; pvd; 'sPC;
       'sTR "is not well-formed" >]
    
let error_ill_typed_rec_body k env i lna vdefj vargs =
  let pvd = gen_pr_term k env (vdefj.(i)).uj_val in
  let pvdt = gen_pr_term k env (vdefj.(i)).uj_type in
  let pv = gen_pr_term k env (body_of_type vargs.(i)) in
  errorlabstrm "Ill-typed rec body"
    [< 'sTR"The " ;
       if Array.length vdefj = 1 then [<>] else [<'iNT (i+1); 'sTR "-th">];
       'sTR"recursive definition" ; 'sPC; pvd; 'sPC;
       'sTR "has type"; 'sPC; pvdt;'sPC; 'sTR "it should be"; 'sPC; pv >]
