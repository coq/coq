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
open Names
open Nameops
open Term
open Termops
open Sign
open Environ
open Global
open Declare
open Coqast
open Ast
open Termast
open Nametab

let emacs_str s = if !Options.print_emacs then s else "" 

let dfltpr ast = (str"#GENTERM " ++ print_ast ast);;

let pr_global ref = pr_global_env (Global.env()) ref

let global_const_name sp =
  try pr_global (ConstRef sp)
  with Not_found -> (* May happen in debug *)
    (str ("CONST("^(string_of_path sp)^")"))

let global_ind_name (sp,tyi) =
  try pr_global (IndRef (sp,tyi))
  with Not_found -> (* May happen in debug *)
    (str ("IND("^(string_of_path sp)^","^(string_of_int tyi)^")"))

let global_constr_name ((sp,tyi),i) =
  try pr_global (ConstructRef ((sp,tyi),i))
  with Not_found -> (* May happen in debug *)
    (str ("CONSTRUCT("^(string_of_path sp)^","^(string_of_int tyi)
		  ^","^(string_of_int i)^")"))

let globpr gt = match gt with
  | Nvar(_,s) -> (pr_id s)
  | Node(_,"EVAR", [Num (_,ev)]) -> (str ("?" ^ (string_of_int ev)))
  | Node(_,"CONST",[Path(_,sl)]) ->
      global_const_name (section_path sl)
  | Node(_,"MUTIND",[Path(_,sl); Num(_,tyi)]) ->
      global_ind_name (section_path sl, tyi)
  | Node(_,"MUTCONSTRUCT",[Path(_,sl); Num(_,tyi); Num(_,i)]) ->
      global_constr_name ((section_path sl, tyi), i)
  | Dynamic(_,d) ->
    if (Dyn.tag d) = "constr" then (str"<dynamic [constr]>")
    else dfltpr gt
  | gt -> dfltpr gt

let wrap_exception = function
    Anomaly (s1,s2) ->
      warning ("Anomaly ("^s1^")"); pp s2;
      str"<PP error: non-printable term>"
  | Failure _ | UserError _ | Not_found ->
      str"<PP error: non-printable term>"
  | s -> raise s

(* These are the names of the universes where the pp rules for constr and
   tactic are put (must be consistent with files PPConstr.v and PPTactic.v *)

let constr_syntax_universe = "constr"
let tactic_syntax_universe = "tactic"

(* This is starting precedence for printing constructions or tactics *)
(* Level 9 means no parentheses except for applicative terms (at level 10) *)
let constr_initial_prec = Some ((constr_syntax_universe,(9,0,0)),Extend.L)
let tactic_initial_prec = Some ((tactic_syntax_universe,(9,0,0)),Extend.L)

let gentermpr_fail gt =
  Esyntax.genprint globpr constr_syntax_universe constr_initial_prec gt

let gentermpr gt =
  try gentermpr_fail gt
  with s -> wrap_exception s

(* [at_top] means ids of env must be avoided in bound variables *)
let gentermpr_core at_top env t =
  gentermpr (Termast.ast_of_constr at_top env t)

let prterm_env_at_top env = gentermpr_core true env
let prterm_env env = gentermpr_core false env
let prterm = prterm_env empty_env

let prtype_env env typ = prterm_env env typ
let prtype = prtype_env empty_env

let prjudge_env env j =
  (prterm_env env j.uj_val, prterm_env env j.uj_type)
let prjudge = prjudge_env empty_env

let fprterm_env a =
  warning "Fw printing not implemented, use CCI printing 1"; prterm_env a
let fprterm a =
  warning "Fw printing not implemented, use CCI printing 2"; prterm a

let fprtype_env env typ =
  warning "Fw printing not implemented, use CCI printing 3"; prtype_env env typ
let fprtype a =
  warning "Fw printing not implemented, use CCI printing 4"; prtype a

(* For compatibility *)
let fterm0 = fprterm_env

let pr_constant env cst = gentermpr (ast_of_constant env cst)
let pr_existential env ev = gentermpr (ast_of_existential env ev)
let pr_inductive env ind = gentermpr (ast_of_inductive env ind)
let pr_constructor env cstr =
  gentermpr (ast_of_constructor env cstr)

open Pattern
let pr_ref_label = function (* On triche sur le contexte *)
  | ConstNode sp -> pr_constant (Global.env()) sp
  | IndNode sp -> pr_inductive (Global.env()) sp
  | CstrNode sp -> pr_constructor (Global.env()) sp
  | VarNode id -> pr_id id

let pr_cases_pattern t = gentermpr (Termast.ast_of_cases_pattern t)
let pr_rawterm t = gentermpr (Termast.ast_of_rawconstr t)
let pr_pattern_env tenv env t =
  gentermpr (Termast.ast_of_pattern tenv env t)
let pr_pattern t = pr_pattern_env (Global.env()) empty_names_context t

let rec gentacpr gt =
  Esyntax.genprint default_tacpr tactic_syntax_universe tactic_initial_prec gt

and default_tacpr = function
    | Nvar(_,s) -> (pr_id s)

    (* constr's may occur inside tac expressions ! *)
    | Node(_,"EVAR", [Num (_,ev)]) -> (str ("?" ^ (string_of_int ev)))
    | Node(_,"CONST",[Path(_,sl)]) ->
	let sp = section_path sl in
	pr_global (ConstRef sp)
    | Node(_,"MUTIND",[Path(_,sl); Num(_,tyi)]) ->
	let sp = section_path sl in
	pr_global (IndRef (sp,tyi))
    | Node(_,"MUTCONSTRUCT",[Path(_,sl); Num(_,tyi); Num(_,i)]) ->
	let sp = section_path sl in
	pr_global (ConstructRef ((sp,tyi),i))

    (* This should be tactics *)
    | Node(_,s,[]) -> (str s)
    | Node(_,s,ta) ->
	(str s ++ brk(1,2) ++ hov 0 (prlist_with_sep pr_spc gentacpr ta))
    | Dynamic(_,d) as gt ->
      let tg = Dyn.tag d in
      if tg = "tactic" then (str"<dynamic [tactic]>")
      else if tg = "value" then (str"<dynamic [value]>")
      else if tg = "constr" then (str"<dynamic [constr]>")
      else dfltpr gt
    | gt -> dfltpr gt 

let pr_var_decl env (id,c,typ) =
  let pbody = match c with
    | None ->  (mt ())
    | Some c ->
	(* Force evaluation *) 
	let pb = prterm_env env c in
	(str" := " ++ pb) in
  let pt = prtype_env env typ in
  let ptyp = (str" : " ++ pt) in
  (pr_id id ++ hov 0 (pbody ++ ptyp))

let pr_rel_decl env (na,c,typ) =
  let pbody = match c with
    | None ->  (mt ())
    | Some c ->
	(* Force evaluation *) 
	let pb = prterm_env env c in
	(str":=" ++ spc () ++ pb ++ spc ()) in
  let ptyp = prtype_env env typ in
  match na with
    | Anonymous -> (str"<>" ++ spc () ++ pbody ++ str":" ++ spc () ++ ptyp)
    | Name id -> (pr_id id ++ spc () ++ pbody ++ str":" ++ spc () ++ ptyp)


(* Prints out an "env" in a nice format.  We print out the
 * signature,then a horizontal bar, then the debruijn environment.
 * It's printed out from outermost to innermost, so it's readable. *)

(* Prints a signature, all declarations on the same line if possible *)
let pr_named_context_of env =
  hv 0 (fold_named_context
	  (fun env d pps -> pps ++ ws 2 ++ pr_var_decl env d)
          env ~init:(mt ()))

let pr_rel_context env rel_context =
  let rec prec env = function
    | [] -> (mt ()) 
    | [b] -> pr_rel_decl env b
    | b::rest ->
        let pb = pr_rel_decl env b in
        let penvtl = prec (push_rel b env) rest in
        (pb ++ str";" ++ spc () ++ penvtl)
  in 
  prec env (List.rev rel_context)

(* Prints an env (variables and de Bruijn). Separator: newline *)
let pr_context_unlimited env =
  let sign_env =
    fold_named_context
      (fun env d pps ->
         let pidt =  pr_var_decl env d in (pps ++ fnl () ++ pidt))
      env ~init:(mt ()) 
  in
  let db_env =
    fold_rel_context
      (fun env d pps ->
         let pnat = pr_rel_decl env d in (pps ++ fnl () ++ pnat))
      env ~init:(mt ())
  in 
  (sign_env ++ db_env)

let pr_ne_context_of header env =
  if Environ.rel_context env = empty_rel_context &
    Environ.named_context env = empty_named_context  then (mt ())
  else let penv = pr_context_unlimited env in (header ++ penv ++ fnl ())

let pr_context_limit n env =
  let named_context = Environ.named_context env in
  let lgsign = List.length named_context in
  if n >= lgsign then 
    pr_context_unlimited env
  else
    let k = lgsign-n in
    let _,sign_env =
      fold_named_context
        (fun env d (i,pps) ->
           if i < k then 
	     (i+1, (pps ++str "."))
	   else
             let pidt = pr_var_decl env d in
	     (i+1, (pps ++ fnl () ++
		      str (emacs_str (String.make 1 (Char.chr 253))) ++
		      pidt)))
        env ~init:(0,(mt ())) 
    in
    let db_env =
      fold_rel_context
        (fun env d pps ->
           let pnat = pr_rel_decl env d in
	   (pps ++ fnl () ++
	      str (emacs_str (String.make 1 (Char.chr 253))) ++
	      pnat))
        env ~init:(mt ())
    in 
    (sign_env ++ db_env)

let pr_context_of env = match Options.print_hyps_limit () with 
  | None -> hv 0 (pr_context_unlimited env)
  | Some n -> hv 0 (pr_context_limit n env)
