
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

let print_arguments = ref false
let print_casts = ref false
let print_emacs = ref false

let emacs_str s =
  if !print_emacs then s else "" 

let section_path sl s =
  let sl = List.rev sl in
  make_path (List.tl sl) (id_of_string (List.hd sl)) (kind_of_string s)

let with_implicits f x =
  let oimpl = !Termast.print_implicits in
  Termast.print_implicits := true; 
  try
    let r = f x in
    Termast.print_implicits := oimpl;
    r
  with e -> 
    Termast.print_implicits := oimpl; raise e

let pr_qualified sp id = 
  if Nametab.sp_of_id (kind_of_path sp) id = sp then 
    [< 'sTR(string_of_id id) >]
  else 
    [< 'sTR(string_of_path sp) >]

let pr_constant sp = pr_qualified sp (basename sp)

let pr_existential ev = [< 'sTR ("?" ^ string_of_int ev) >]

let pr_inductive (sp,tyi as ind_sp) =
  let id = id_of_global (MutInd ind_sp) in
  pr_qualified sp id

let pr_constructor ((sp,tyi),i as cstr_sp) =
  let id = id_of_global (MutConstruct cstr_sp) in
  pr_qualified sp id

(*
let pr_global k oper =
  let id = id_of_global oper in
  [< 'sTR (string_of_id id) >]
*)

let dfltpr ast = [< 'sTR"#GENTERM " ; Ast.print_ast ast >]

let globpr k gt = match gt with
  | Nvar(_,s) -> [< 'sTR s >]
  | Node(_,"EVAR", (Num (_,ev))::_) ->
      if !print_arguments then dfltpr gt
      else pr_existential ev
  | Node(_,"CONST",(Path(_,sl,s))::_) ->
      if !print_arguments then dfltpr gt
      else pr_constant (section_path sl s)
  | Node(_,"MUTIND",(Path(_,sl,s))::(Num(_,tyi))::_) ->
      if !print_arguments then (dfltpr gt)
      else pr_inductive (section_path sl s,tyi)
  | Node(_,"MUTCONSTRUCT",(Path(_,sl,s))::(Num(_,tyi))::(Num(_,i))::_) ->
      if !print_arguments then (dfltpr gt)
      else pr_constructor ((section_path sl s,tyi),i)
  | gt -> dfltpr gt

let apply_prec = Some (("Term",(9,0,0)),Extend.L)
let apply_tacprec = Some (("Tactic",(9,0,0)),Extend.L)

let rec gencompr k gt =
  let uni = match k with
    | CCI | FW -> "constr"
    | _ -> "<undefined>" 
  in
  let rec gpr gt =
    Esyntax.genprint uni
      (function
         | Node(_,"PPUNI$COMMAND",[Str(_,"CCI");c]) -> gencompr CCI c
         | Node(_,"PPUNI$COMMAND",[c]) -> gencompr CCI c
         | Node(_,"PPUNI$COMMAND",[Str(_,"FW");c]) -> gencompr FW c
         | gt -> globpr k gt)
      apply_prec
      gt
  in 
  gpr gt

let print_if_exception = function
    Anomaly (s1,s2) ->
      warning ("Anomaly ("^s1^")");pP s2;
      [< 'sTR"<PP error: non-printable term>" >]
  | Failure _ | UserError _ | Not_found ->
      [< 'sTR"<PP error: non-printable term>" >]
  | s -> raise s

(* [at_top] means ids of env must be avoided in bound variables *)
let gentermpr_core at_top k env t =
  let uenv = unitize_env env in
  try 
    let ogt = 
      if !print_casts then 
	Termast.bdize at_top uenv t
      else 
	Termast.bdize_no_casts at_top uenv t
    in 
    gencompr k ogt
  with s -> print_if_exception s

let term0_at_top a = gentermpr_core true CCI a
let gentermpr a = gentermpr_core false a

let term0 a = gentermpr CCI a
let prterm = term0 (gLOB nil_sign)
let fterm0 a = gentermpr FW a
let fprterm = fterm0 (gLOB nil_sign)

let prtype_env env typ =
  if !print_casts then 
    term0 env (mkCast typ.body (mkSort typ.typ))
  else 
    prterm typ.body

let prtype = prtype_env (gLOB nil_sign)

let fprtype_env env typ =
  if !print_casts then 
    fterm0 env (mkCast typ.body (mkSort typ.typ))
  else 
    fterm0 env typ.body

let fprtype = fprtype_env (gLOB nil_sign)

let genpatternpr k t =
  try 
    gencompr k (Termast.ast_of_pattern t)
  with s -> print_if_exception s

let prpattern = genpatternpr CCI

let genrawtermpr k env t =
  try 
    gencompr k (Termast.ast_of_rawconstr t)
  with s -> print_if_exception s

let prrawterm = genrawtermpr CCI (gLOB nil_sign)

let gentacpr gt =
  let rec gpr gt =
    Esyntax.genprint "tactic"
      (function 
         | Nvar(_,s) -> [< 'sTR s >]
         | Node(_,"PPUNI$COMMAND",[Str(_,"CCI");c]) -> gencompr CCI c
         | Node(_,"PPUNI$COMMAND",[c]) -> gencompr CCI c
         | Node(_,"PPUNI$COMMAND",[Str(_,"FW");c]) -> gencompr FW c
         | gt -> default_tacpr gt)
      apply_tacprec
      gt
  and default_tacpr = function
    | Node(_,s,[]) -> [< 'sTR s >]
    | Node(_,s,ta) ->
	[< 'sTR s; 'bRK(1,2); hOV 0 (prlist_with_sep pr_spc gpr ta) >]
    | gt -> dfltpr gt
  in 
  gpr gt

let print_decl k sign (s,typ) =
  let ptyp = gentermpr k (gLOB sign) typ.body in
  [< print_id s ; 'sTR" : "; ptyp >]

let print_binding k env (na,typ) =
  let ptyp = gentermpr k env typ.body in
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
  | ENVIRON (([],[]),[]) -> [< >]
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

let emacs_str s = if !Options.print_emacs then s else "" 
