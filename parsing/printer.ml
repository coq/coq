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
open Libnames
open Extend
open Nametab
open Ppconstr

let emacs_str s = if !Options.print_emacs then s else "" 

(**********************************************************************)
(* Old Ast printing *)

let constr_syntax_universe = "constr"
(* This is starting precedence for printing constructions or tactics *)
(* Level 9 means no parentheses except for applicative terms (at level 10) *)
let constr_initial_prec_v7 = Some (9,Ppextend.L)
let constr_initial_prec = Some (200,Ppextend.E)

let dfltpr ast = (str"#GENTERM " ++ print_ast ast);;

let global_const_name kn =
  try pr_global Idset.empty (ConstRef kn)
  with Not_found -> (* May happen in debug *)
    (str ("CONST("^(string_of_kn kn)^")"))

let global_var_name id =
  try pr_global Idset.empty (VarRef id)
  with Not_found -> (* May happen in debug *)
    (str ("SECVAR("^(string_of_id id)^")"))

let global_ind_name (kn,tyi) =
  try pr_global Idset.empty (IndRef (kn,tyi))
  with Not_found -> (* May happen in debug *)
    (str ("IND("^(string_of_kn kn)^","^(string_of_int tyi)^")"))

let global_constr_name ((kn,tyi),i) =
  try pr_global Idset.empty (ConstructRef ((kn,tyi),i))
  with Not_found -> (* May happen in debug *)
    (str ("CONSTRUCT("^(string_of_kn kn)^","^(string_of_int tyi)
		  ^","^(string_of_int i)^")"))

let globpr gt = match gt with
  | Nvar(_,s) -> (pr_id s)
  | Node(_,"EVAR", [Num (_,ev)]) -> (str ("?" ^ (string_of_int ev)))
  | Node(_,"CONST",[Path(_,sl)]) ->
      global_const_name (section_path sl)
  | Node(_,"SECVAR",[Nvar(_,s)]) ->
      global_var_name s
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

let gentermpr_fail gt =
  let prec =
    if !Options.v7 then constr_initial_prec_v7 else constr_initial_prec in
  Esyntax.genprint globpr constr_syntax_universe prec gt

let gentermpr gt =
  try gentermpr_fail gt
  with s -> wrap_exception s

(**********************************************************************)
(* Generic printing: choose old or new printers *)

(* [at_top] means ids of env must be avoided in bound variables *)
let gentermpr_core at_top env t =
  if !Options.v7 then gentermpr (Termast.ast_of_constr at_top env t)
  else Ppconstrnew.pr_lconstr (Constrextern.extern_constr at_top env t)
let pr_cases_pattern t =
  if !Options.v7 then gentermpr (Termast.ast_of_cases_pattern t)
  else Ppconstrnew.pr_cases_pattern
    (Constrextern.extern_cases_pattern Idset.empty t)
let pr_pattern_env tenv env t =
  if !Options.v7 then gentermpr (Termast.ast_of_pattern tenv env t)
  else Ppconstrnew.pr_constr
    (Constrextern.extern_pattern tenv env t)

(**********************************************************************)
(* Derived printers *)
  
let prterm_env_at_top env = gentermpr_core true env
let prterm_env env = gentermpr_core false env
let prtype_env env typ = prterm_env env typ
let prjudge_env env j =
  (prterm_env env j.uj_val, prterm_env env j.uj_type)

(* NB do not remove the eta-redexes! Global.env() has side-effects... *)
let prterm t = prterm_env (Global.env()) t
let prtype t = prtype_env (Global.env()) t
let prjudge j = prjudge_env (Global.env()) j

let pr_constant env cst = prterm_env env (mkConst cst)
let pr_existential env ev = prterm_env env (mkEvar ev)
let pr_inductive env ind = prterm_env env (mkInd ind)
let pr_constructor env cstr = prterm_env env (mkConstruct cstr)
let pr_global = pr_global Idset.empty

let pr_rawterm t =
  if !Options.v7 then gentermpr (Termast.ast_of_rawconstr t)
  else Ppconstrnew.pr_lconstr (Constrextern.extern_rawconstr Idset.empty t)

open Pattern
let pr_ref_label = function (* On triche sur le contexte *)
  | ConstNode sp -> pr_constant (Global.env()) sp
  | IndNode sp -> pr_inductive (Global.env()) sp
  | CstrNode sp -> pr_constructor (Global.env()) sp
  | VarNode id -> pr_id id

let pr_pattern t = pr_pattern_env (Global.env()) empty_names_context t

let pr_var_decl env (id,c,typ) =
  let pbody = match c with
    | None ->  (mt ())
    | Some c ->
	(* Force evaluation *) 
	let pb = prterm_env env c in
	(str" := " ++ pb ++ cut () ) in
  let pt = prtype_env env typ in
  let ptyp = (str" : " ++ pt) in
  (pr_id id ++ hov 0 (pbody ++ ptyp))

let pr_rel_decl env (na,c,typ) =
  let pbody = match c with
    | None -> mt ()
    | Some c ->
	(* Force evaluation *) 
	let pb = prterm_env env c in
	(str":=" ++ spc () ++ pb ++ spc ()) in
  let ptyp = prtype_env env typ in
  match na with
  | Anonymous -> hov 0 (str"<>" ++ spc () ++ pbody ++ str":" ++ spc () ++ ptyp)
  | Name id -> hov 0 (pr_id id ++ spc () ++ pbody ++ str":" ++ spc () ++ ptyp)


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
    | [b] -> 
	if !Options.v7 then pr_rel_decl env b
	else str "(" ++ pr_rel_decl env b ++ str")"
    | b::rest ->
        let pb = pr_rel_decl env b in
        let penvtl = prec (push_rel b env) rest in
	if !Options.v7 then
          (pb ++ str";" ++ spc () ++ penvtl)
	else 
          (str "(" ++ pb ++ str")" ++ spc () ++ penvtl)
  in 
  hov 0 (prec env (List.rev rel_context))

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
