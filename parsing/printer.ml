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
open Evd
open Proof_type
open Refiner
open Pfedit

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
    (str ("CONST("^(string_of_con kn)^")"))

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
  | Node(_,"CONST",[ConPath(_,sl)]) ->
      global_const_name sl
  | Node(_,"SECVAR",[Nvar(_,s)]) ->
      global_var_name s
  | Node(_,"MUTIND",[Path(_,sl); Num(_,tyi)]) ->
      global_ind_name (sl, tyi)
  | Node(_,"MUTCONSTRUCT",[Path(_,sl); Num(_,tyi); Num(_,i)]) ->
      global_constr_name ((sl, tyi), i)
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

let _ = Termops.set_print_constr prterm_env
(*let _ = Tactic_debug.set_pattern_printer pr_pattern_env*)

let pr_constant env cst = prterm_env env (mkConst cst)
let pr_existential env ev = prterm_env env (mkEvar ev)
let pr_inductive env ind = prterm_env env (mkInd ind)
let pr_constructor env cstr = prterm_env env (mkConstruct cstr)
let pr_global = pr_global Idset.empty
let pr_evaluable_reference ref =
 let ref' = match ref with
  | EvalConstRef const -> ConstRef const
  | EvalVarRef sp -> VarRef sp in
 pr_global ref'

let pr_rawterm t =
  if !Options.v7 then gentermpr (Termast.ast_of_rawconstr t)
  else Ppconstrnew.pr_lconstr (Constrextern.extern_rawconstr Idset.empty t)

open Pattern

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


(* display complete goal *)
let pr_goal g =
  let env = evar_env g in
  let penv = pr_context_of env in
  let pc = prterm_env_at_top env g.evar_concl in
  str"  " ++ hv 0 (penv ++ fnl () ++
		   str (emacs_str (String.make 1 (Char.chr 253)))  ++
                   str "============================" ++ fnl ()  ++
                   str" "  ++ pc) ++ fnl ()

(* display the conclusion of a goal *)
let pr_concl n g =
  let env = evar_env g in
  let pc = prterm_env_at_top env g.evar_concl in
  str (emacs_str (String.make 1 (Char.chr 253)))  ++
  str "subgoal " ++ int n ++ str " is:" ++ cut () ++ str" "  ++ pc

(* display evar type: a context and a type *)
let pr_evgl_sign gl = 
  let ps = pr_named_context_of (evar_env gl) in
  let pc = prterm gl.evar_concl in
  hov 0 (str"["  ++ ps ++ spc () ++ str"|- "  ++ pc ++ str"]")

(* Print an enumerated list of existential variables *)
let rec pr_evars_int i = function
  | [] -> (mt ())
  | (ev,evd)::rest ->
      let pegl = pr_evgl_sign evd in 
      let pei = pr_evars_int (i+1) rest in
      (hov 0 (str "Existential " ++ int i ++ str " =" ++ spc () ++
              str (string_of_existential ev)  ++ str " : " ++ pegl)) ++ 
      fnl () ++ pei

let pr_subgoal n =
  let rec prrec p = function
    | [] -> error "No such goal"
    | g::rest ->
       	if p = 1 then
          let pg = pr_goal g in
          v 0 (str "subgoal " ++ int n ++ str " is:" ++ cut () ++ pg)
       	else 
	  prrec (p-1) rest
  in 
  prrec n

(* Print open subgoals. Checks for uninstantiated existential variables *)
let pr_subgoals sigma = function 
  | [] -> 
      let exl = Evarutil.non_instantiated sigma in 
      if exl = [] then 
	(str"Proof completed."  ++ fnl ())
      else
        let pei = pr_evars_int 1 exl in
        (str "No more subgoals but non-instantiated existential " ++
           str "variables :"  ++fnl () ++ (hov 0 pei))
  | [g] ->
      let pg = pr_goal g in
      v 0 (str ("1 "^"subgoal") ++cut () ++ pg)
  | g1::rest ->
      let rec pr_rec n = function
        | [] -> (mt ())
        | g::rest ->
            let pc = pr_concl n g in
            let prest = pr_rec (n+1) rest in
            (cut () ++ pc ++ prest) 
      in
      let pg1 = pr_goal g1 in
      let prest = pr_rec 2 rest in
      v 0 (int(List.length rest+1) ++ str" subgoals" ++ cut () 
	   ++ pg1 ++ prest ++ fnl ())


let pr_subgoals_of_pfts pfts = 
  let gls = fst (Refiner.frontier (proof_of_pftreestate pfts)) in 
  let sigma = (top_goal_of_pftreestate pfts).sigma in
  pr_subgoals sigma gls

let pr_open_subgoals () =
  let pfts = get_pftreestate () in
  match focus() with
    | 0 -> 
	pr_subgoals_of_pfts pfts
    | n -> 
	let pf = proof_of_pftreestate pfts in
	let gls = fst (frontier pf) in 
	assert (n > List.length gls);
	if List.length gls < 2 then 
	  pr_subgoal n gls
	else 
	  v 0 (int(List.length gls) ++ str" subgoals" ++ cut () ++
	  pr_subgoal n gls)

let pr_nth_open_subgoal n =
  let pf = proof_of_pftreestate (get_pftreestate ()) in
  pr_subgoal n (fst (frontier pf))

(* Elementary tactics *)

let pr_prim_rule_v7 = function
  | Intro id -> 
      str"Intro " ++ pr_id id
	
  | Intro_replacing id -> 
      (str"intro replacing "  ++ pr_id id)
	
  | Cut (b,id,t) ->
      if b then
        (str"Assert " ++ print_constr t)
      else
        (str"Cut " ++ print_constr t ++ str ";[Intro " ++ pr_id id ++ str "|Idtac]")
	
  | FixRule (f,n,[]) ->
      (str"Fix " ++ pr_id f ++ str"/" ++ int n)
      
  | FixRule (f,n,others) -> 
      let rec print_mut = function
	| (f,n,ar)::oth -> 
           pr_id f ++ str"/" ++ int n ++ str" : " ++ print_constr ar ++ print_mut oth
        | [] -> mt () in
      (str"Fix " ++ pr_id f ++ str"/" ++ int n ++
         str" with " ++ print_mut others)

  | Cofix (f,[]) ->
      (str"Cofix " ++ pr_id f)

  | Cofix (f,others) ->
      let rec print_mut = function
	| (f,ar)::oth ->
	  (pr_id f ++ str" : " ++ print_constr ar ++ print_mut oth)
        | [] -> mt () in
      (str"Cofix " ++ pr_id f ++  str" with " ++ print_mut others)

  | Refine c -> 
      str(if occur_meta c then "Refine " else "Exact ") ++
      Constrextern.with_meta_as_hole print_constr c
      
  | Convert_concl c ->
      (str"Change "  ++ print_constr c)
      
  | Convert_hyp (id,None,t) ->
      (str"Change "  ++ print_constr t  ++ spc ()  ++ str"in "  ++ pr_id id)

  | Convert_hyp (id,Some c,t) ->
      (str"Change "  ++ print_constr c  ++ spc ()  ++ str"in "
       ++ pr_id id ++ str" (Type of "  ++ pr_id id ++ str ")")
      
  | Thin ids ->
      (str"Clear "  ++ prlist_with_sep pr_spc pr_id ids)
      
  | ThinBody ids ->
      (str"ClearBody "  ++ prlist_with_sep pr_spc pr_id ids)
      
  | Move (withdep,id1,id2) ->
      (str (if withdep then "Dependent " else "") ++
	 str"Move "  ++ pr_id id1 ++ str " after " ++ pr_id id2)

  | Rename (id1,id2) ->
      (str "Rename " ++ pr_id id1 ++ str " into " ++ pr_id id2)

let pr_prim_rule_v8 = function
  | Intro id -> 
      str"intro " ++ pr_id id
	
  | Intro_replacing id -> 
      (str"intro replacing "  ++ pr_id id)
	
  | Cut (b,id,t) ->
      if b then
        (str"assert " ++ print_constr t)
      else
        (str"cut " ++ print_constr t ++ str ";[intro " ++ pr_id id ++ str "|idtac]")
	
  | FixRule (f,n,[]) ->
      (str"fix " ++ pr_id f ++ str"/" ++ int n)
      
  | FixRule (f,n,others) -> 
      let rec print_mut = function
	| (f,n,ar)::oth -> 
           pr_id f ++ str"/" ++ int n ++ str" : " ++ print_constr ar ++ print_mut oth
        | [] -> mt () in
      (str"fix " ++ pr_id f ++ str"/" ++ int n ++
         str" with " ++ print_mut others)

  | Cofix (f,[]) ->
      (str"cofix " ++ pr_id f)

  | Cofix (f,others) ->
      let rec print_mut = function
	| (f,ar)::oth ->
	  (pr_id f ++ str" : " ++ print_constr ar ++ print_mut oth)
        | [] -> mt () in
      (str"cofix " ++ pr_id f ++  str" with " ++ print_mut others)

  | Refine c -> 
      str(if occur_meta c then "refine " else "exact ") ++
      Constrextern.with_meta_as_hole print_constr c
      
  | Convert_concl c ->
      (str"change "  ++ print_constr c)
      
  | Convert_hyp (id,None,t) ->
      (str"change "  ++ print_constr t  ++ spc ()  ++ str"in "  ++ pr_id id)

  | Convert_hyp (id,Some c,t) ->
      (str"change "  ++ print_constr c  ++ spc ()  ++ str"in "
       ++ pr_id id ++ str" (type of "  ++ pr_id id ++ str ")")
      
  | Thin ids ->
      (str"clear "  ++ prlist_with_sep pr_spc pr_id ids)
      
  | ThinBody ids ->
      (str"clearbody "  ++ prlist_with_sep pr_spc pr_id ids)
      
  | Move (withdep,id1,id2) ->
      (str (if withdep then "dependent " else "") ++
	 str"move "  ++ pr_id id1 ++ str " after " ++ pr_id id2)

  | Rename (id1,id2) ->
      (str "rename " ++ pr_id id1 ++ str " into " ++ pr_id id2)

let pr_prim_rule t =
  if! Options.v7 then pr_prim_rule_v7 t else pr_prim_rule_v8 t
