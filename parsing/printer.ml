
(* $Id$ *)

open Pp
open Util
open Names
open Term
open Sign
open Environ
open Global
open Declare
open Coqast
open Termast

let emacs_str s = if !Options.print_emacs then s else "" 

let dfltpr ast = [< 'sTR"#GENTERM " ; Ast.print_ast ast >];;

(*
let section_path sl s =
  let sl = List.rev sl in
  make_path (List.tl sl) (id_of_string (List.hd sl)) (kind_of_string s)

let pr_global k oper =
  let id = id_of_global oper in
  [< 'sTR (string_of_id id) >]
*)

let globpr k gt = match gt with
  | Nvar(_,s) -> [< 'sTR s >]
(*
  | Node(_,"EVAR", (Num (_,ev))::_) ->
      if !print_arguments then dfltpr gt
      else pr_existential (ev,[])
  | Node(_,"CONST",(Path(_,sl,s))::_) ->
      if !print_arguments then dfltpr gt
      else pr_constant (section_path sl s,[])
  | Node(_,"MUTIND",(Path(_,sl,s))::(Num(_,tyi))::_) ->
      if !print_arguments then (dfltpr gt)
      else pr_inductive ((section_path sl s,tyi),[])
  | Node(_,"MUTCONSTRUCT",(Path(_,sl,s))::(Num(_,tyi))::(Num(_,i))::_) ->
      if !print_arguments then (dfltpr gt)
      else pr_constructor (((section_path sl s,tyi),i),[])
*)
  | gt -> dfltpr gt

let wrap_exception = function
    Anomaly (s1,s2) ->
      warning ("Anomaly ("^s1^")");pP s2;
      [< 'sTR"<PP error: non-printable term>" >]
  | Failure _ | UserError _ | Not_found ->
      [< 'sTR"<PP error: non-printable term>" >]
  | s -> raise s

(* These are the names of the universes where the pp rules for constr and
   tactic are put (must be consistent with files PPConstr.v and PPTactic.v *)

let constr_syntax_universe = "constr"
let tactic_syntax_universe = "tactic"

(* This is starting precedence for printing constructions or tactics *)
(* Level 9 means no parentheses except for applicative terms (at level 10) *)
let constr_initial_prec = Some ((constr_syntax_universe,(9,0,0)),Extend.L)
let tactic_initial_prec = Some ((tactic_syntax_universe,(9,0,0)),Extend.L)

let gencompr k gt =
  let uni = match k with
    | CCI | FW -> constr_syntax_universe
    | _ -> anomaly "gencompr: not a construction"
	(* WAS "<undefined>" *)
  in Esyntax.genprint (globpr k) uni constr_initial_prec gt

(* [at_top] means ids of env must be avoided in bound variables *)
let gentermpr_core at_top k env t =
  let uenv = unitize_env env in
  try gencompr k (Termast.bdize at_top uenv t)
  with s -> wrap_exception s

let gentermpr k = gentermpr_core false k
let gentermpr_at_top k = gentermpr_core true k

let prterm_env_at_top a = gentermpr_core true CCI a
let prterm_env a = gentermpr CCI a
let prterm = prterm_env (gLOB nil_sign)

let fprterm_env a = gentermpr FW a
let fprterm = fprterm_env (gLOB nil_sign)

let prtype_env env typ = prterm_env env (incast_type typ)
let prtype = prtype_env (gLOB nil_sign)

let fprtype_env env typ = fprterm_env env (incast_type typ)
let fprtype = fprtype_env (gLOB nil_sign)

let pr_constant cst = gencompr CCI (ast_of_constant cst)
let pr_existential ev = gencompr CCI (ast_of_existential ev)
let pr_inductive ind = gencompr CCI (ast_of_inductive ind)
let pr_constructor cstr = gencompr CCI (ast_of_constructor cstr)

open Rawterm
let pr_ref_label = function (* On triche sur le contexte *)
  | ConstNode sp -> pr_constant (sp,[||])
  | IndNode sp -> pr_inductive (sp,[||])
  | CstrNode sp -> pr_constructor (sp,[||])
  | VarNode id -> print_id id

(* For compatibility *)
let term0 = prterm_env
let fterm0 = fprterm_env

let genpatternpr k t =
  try gencompr k (Termast.ast_of_pattern t)
  with s -> wrap_exception s

let prpattern = genpatternpr CCI

let genrawtermpr k env t =
  try gencompr k (Termast.ast_of_rawconstr t)
  with s -> wrap_exception s

let prrawterm = genrawtermpr CCI (gLOB nil_sign)

let rec gentacpr gt =
  Esyntax.genprint default_tacpr tactic_syntax_universe tactic_initial_prec gt

and default_tacpr = function
    | Nvar(_,s) -> [< 'sTR s >]
    | Node(_,s,[]) -> [< 'sTR s >]
    | Node(_,s,ta) ->
	[< 'sTR s; 'bRK(1,2); hOV 0 (prlist_with_sep pr_spc gentacpr ta) >]
    | gt -> dfltpr gt

let print_decl k sign (s,typ) =
  let ptyp = gentermpr k (gLOB sign) (body_of_type typ) in
  [< print_id s ; 'sTR" : "; ptyp >]

let print_binding k env (na,typ) =
  let ptyp = gentermpr k env (body_of_type typ) in
  match na with
    | Anonymous -> [< 'sTR"<>" ; 'sTR" : " ; ptyp >]
    | Name id -> [< print_id id ; 'sTR" : "; ptyp >]


(* Prints out an "env" in a nice format.  We print out the
 * signature,then a horizontal bar, then the debruijn environment.
 * It's printed out from outermost to innermost, so it's readable. *)

let sign_it_with f sign e =
  snd (sign_it (fun id t (sign,e) -> (add_sign (id,t) sign, f id t sign e))
         sign (nil_sign,e))

let sign_it_with_i f sign e =
  let (_,_,e') = 
    (sign_it (fun id t (i,sign,e) -> (i+1,add_sign (id,t) sign,
				      f i id t sign e))
       sign (0,nil_sign,e))
  in 
  e'

let dbenv_it_with f env e =
  snd (dbenv_it (fun na t (env,e) -> (add_rel (na,t) env, f na t env e))
         env (gLOB(get_globals env),e))

(* Prints a signature, all declarations on the same line if possible *)
let pr_sign sign =
  hV 0 [< (sign_it_with (fun id t sign pps ->
                           [< pps; 'wS 2; print_decl CCI sign (id,t) >])
             sign) [< >] >]

(* Prints an env (variables and de Bruijn). Separator: newline *)
let pr_env k env =
  let sign_env =
    sign_it_with
      (fun id t sign pps ->
         let pidt =  print_decl k sign (id,t) in [< pps; 'fNL; pidt >])
      (get_globals env) [< >] 
  in
  let db_env =
    dbenv_it_with 
      (fun na t env pps ->
         let pnat = print_binding k env (na,t) in [< pps; 'fNL; pnat >])
      env [< >]
  in 
  [< sign_env; db_env >]

let pr_ne_env header k = function
  | ENVIRON (sign,_) as env when isnull_sign sign & isnull_rel_env env -> [< >]
  | env -> let penv = pr_env k env in [< header; penv >]

let pr_env_limit n env =
  let sign = get_globals env in
  let lgsign = sign_length sign in
  if n >= lgsign then 
    pr_env CCI env
  else
    let k = lgsign-n in
    let sign_env =
      sign_it_with_i
        (fun i id t sign pps -> 
           if i < k then 
	     [< pps ;'sTR "." >] 
	   else
             let pidt = print_decl CCI sign (id,t) in
	     [< pps ; 'fNL ;
		'sTR (emacs_str (String.make 1 (Char.chr 253)));
		pidt >])
        (get_globals env) [< >] 
    in
    let db_env =
      dbenv_it_with
        (fun na t env pps ->
           let pnat = print_binding CCI env (na,t) in
	   [< pps; 'fNL;
	      'sTR (emacs_str (String.make 1 (Char.chr 253)));
	      pnat >])
        env [< >]
    in 
    [< sign_env; db_env >]

let pr_env_opt env = match Options.print_hyps_limit () with 
  | None -> hV 0 (pr_env CCI env)
  | Some n -> hV 0 (pr_env_limit n env)
