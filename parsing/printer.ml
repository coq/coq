
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

let section_path sl s =
  let sl = List.rev sl in
  make_path (List.tl sl) (id_of_string (List.hd sl)) (kind_of_string s)

(*
let pr_global k oper =
  let id = id_of_global oper in
  [< 'sTR (string_of_id id) >]
*)

let pr_qualified_path sp id =
  if Nametab.sp_of_id (kind_of_path sp) id = sp then [<'sTR(string_of_id id)>]
  else [<'sTR(string_of_path (make_path (dirpath sp) id (kind_of_path sp)))>]

let globpr gt = match gt with
  | Nvar(_,s) -> [< 'sTR s >]
  | Node(_,"EVAR", [Num (_,ev)]) -> [< 'sTR ("?" ^ (string_of_int ev)) >]
  | Node(_,"CONST",[Path(_,sl,s)]) ->
      let sp = section_path sl s in
      pr_qualified_path sp (basename (section_path sl s))
  | Node(_,"MUTIND",[Path(_,sl,s); Num(_,tyi)]) ->
      let sp = section_path sl s in
      pr_qualified_path sp (Global.id_of_global (IndRef (sp,tyi)))
  | Node(_,"MUTCONSTRUCT",[Path(_,sl,s); Num(_,tyi); Num(_,i)]) ->
      let sp = section_path sl s in
      pr_qualified_path sp (Global.id_of_global (ConstructRef ((sp,tyi),i)))
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

let prtype_env env typ = prterm_env env (incast_type typ)
let prtype = prtype_env empty_env

let prjudge_env env j =
  (prterm_env env j.uj_val, prterm_env env (incast_type j.uj_type))
let prjudge = prjudge_env empty_env

(* Plus de "k"...
let gentermpr k = gentermpr_core false
let gentermpr_at_top k = gentermpr_core true

let fprterm_env a = gentermpr FW a
let fprterm = fprterm_env empty_env

let fprtype_env env typ = fprterm_env env (incast_type typ)
let fprtype = fprtype_env empty_env
*)

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
  | ConstNode sp -> pr_constant (Global.env()) (sp,[||])
  | IndNode sp -> pr_inductive (Global.env()) (sp,[||])
  | CstrNode sp -> pr_constructor (Global.env()) (sp,[||])
  | VarNode id -> print_id id

let pr_cases_pattern t = gentermpr (Termast.ast_of_cases_pattern t)
let pr_rawterm t = gentermpr (Termast.ast_of_rawconstr t)
let pr_pattern_env env t = gentermpr (Termast.ast_of_pattern env t)
let pr_pattern t = pr_pattern_env empty_names_context t

let rec gentacpr gt =
  Esyntax.genprint default_tacpr tactic_syntax_universe tactic_initial_prec gt

and default_tacpr = function
    | Nvar(_,s) -> [< 'sTR s >]

    (* constr's may occur inside tac expressions ! *)
    | Node(_,"EVAR", [Num (_,ev)]) -> [< 'sTR ("?" ^ (string_of_int ev)) >]
    | Node(_,"CONST",[Path(_,sl,s)]) ->
	let sp = section_path sl s in
	pr_qualified_path sp (basename (section_path sl s))
    | Node(_,"MUTIND",[Path(_,sl,s); Num(_,tyi)]) ->
	let sp = section_path sl s in
	pr_qualified_path sp (Global.id_of_global (IndRef (sp,tyi)))
    | Node(_,"MUTCONSTRUCT",[Path(_,sl,s); Num(_,tyi); Num(_,i)]) ->
	let sp = section_path sl s in
	pr_qualified_path sp (Global.id_of_global (ConstructRef ((sp,tyi),i)))

    (* This should be tactics *)
    | Node(_,s,[]) -> [< 'sTR s >]
    | Node(_,s,ta) ->
	[< 'sTR s; 'bRK(1,2); hOV 0 (prlist_with_sep pr_spc gentacpr ta) >]
    | gt -> dfltpr gt 

let pr_var_decl env (id,c,typ) =
  let pbody = match c with
    | None ->  [<  >]
    | Some c ->  [< 'sTR" := "; prterm_env env c >] in
  let ptyp = [< 'sTR" : "; prtype_env env typ >] in
  [< print_id id ; hOV 0 [< pbody; ptyp >] >]

let pr_rel_decl env (na,c,typ) =
  let pbody = match c with
    | None ->  [<  >]
    | Some c ->  [< 'sTR" :="; 'sPC; prterm_env env c >] in
  let ptyp = prtype_env env typ in
  match na with
    | Anonymous -> [< 'sTR"<>" ; 'sPC; pbody; 'sTR" :"; 'sPC; ptyp >]
    | Name id -> [< print_id id ; 'sPC; pbody; 'sTR" :"; 'sPC; ptyp >]


(* Prints out an "env" in a nice format.  We print out the
 * signature,then a horizontal bar, then the debruijn environment.
 * It's printed out from outermost to innermost, so it's readable. *)

(* Prints a signature, all declarations on the same line if possible *)
let pr_var_context_of env =
  hV 0 [< (fold_var_context
	     (fun env d pps -> [< pps; 'wS 2; pr_var_decl env d >])
             env) [< >] >]

let pr_rel_context env rel_context =
  let rec prec env = function
    | [] -> [<>] 
    | [b] -> pr_rel_decl env b
    | b::rest ->
        let pb = pr_rel_decl env b in
        let penvtl = prec (push_rel b env) rest in
        [< pb; 'sTR";"; 'sPC; penvtl >]
  in 
  prec env (List.rev rel_context)

(* Prints an env (variables and de Bruijn). Separator: newline *)
let pr_context_unlimited env =
  let sign_env =
    fold_var_context
      (fun env d pps ->
         let pidt =  pr_var_decl env d in [< pps; 'fNL; pidt >])
      env [< >] 
  in
  let db_env =
    fold_rel_context
      (fun env d pps ->
         let pnat = pr_rel_decl env d in [< pps; 'fNL; pnat >])
      env [< >]
  in 
  [< sign_env; db_env >]

let pr_ne_context_of header k env =
  if Environ.context env = empty_context then [< >]
  else let penv = pr_context_unlimited env in [< header; penv >]

let pr_context_limit n env =
  let var_context = Environ.var_context env in
  let lgsign = List.length var_context in
  if n >= lgsign then 
    pr_context_unlimited env
  else
    let k = lgsign-n in
    let _,sign_env =
      fold_var_context
        (fun env d (i,pps) ->
           if i < k then 
	     (i+1, [< pps ;'sTR "." >])
	   else
             let pidt = pr_var_decl env d in
	     (i+1, [< pps ; 'fNL ;
		      'sTR (emacs_str (String.make 1 (Char.chr 253)));
		      pidt >]))
        env (0,[< >]) 
    in
    let db_env =
      fold_rel_context
        (fun env d pps ->
           let pnat = pr_rel_decl env d in
	   [< pps; 'fNL;
	      'sTR (emacs_str (String.make 1 (Char.chr 253)));
	      pnat >])
        env [< >]
    in 
    [< sign_env; db_env >]

let pr_context_of env = match Options.print_hyps_limit () with 
  | None -> hV 0 (pr_context_unlimited env)
  | Some n -> hV 0 (pr_context_limit n env)
