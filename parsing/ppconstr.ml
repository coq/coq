(****************************************************************************)
(*                                                                          *)
(*                          The Coq Proof Assistant                         *)
(*                                                                          *)
(*                                 Projet Coq                               *)
(*                                                                          *)
(*                     INRIA        LRI-CNRS        ENS-CNRS                *)
(*              Rocquencourt         Orsay          Lyon                    *)
(*                                                                          *)
(****************************************************************************)

(* $:Id$ *)

open Ast
open Pp
open Nametab
open Names
open Nameops
open Libnames
open Coqast
open Extend
open Util

let dfltpr ast = (str"#GENTERM " ++ print_ast ast);;

let pr_global ref = pr_global_env None ref

let global_const_name kn =
  try pr_global (ConstRef kn)
  with Not_found -> (* May happen in debug *)
    (str ("CONST("^(string_of_kn kn)^")"))

let global_var_name id =
  try pr_global (VarRef id)
  with Not_found -> (* May happen in debug *)
    (str ("SECVAR("^(string_of_id id)^")"))

let global_ind_name (kn,tyi) =
  try pr_global (IndRef (kn,tyi))
  with Not_found -> (* May happen in debug *)
    (str ("IND("^(string_of_kn kn)^","^(string_of_int tyi)^")"))

let global_constr_name ((kn,tyi),i) =
  try pr_global (ConstructRef ((kn,tyi),i))
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

let constr_syntax_universe = "constr"
(* This is starting precedence for printing constructions or tactics *)
(* Level 9 means no parentheses except for applicative terms (at level 10) *)
let constr_initial_prec = Some ((constr_syntax_universe,(9,0,0)),Extend.L)

let gentermpr_fail gt =
  Esyntax.genprint globpr constr_syntax_universe constr_initial_prec gt

let gentermpr gt =
  try gentermpr_fail gt
  with s -> wrap_exception s

(* [at_top] means ids of env must be avoided in bound variables *)
let gentermpr_core at_top env t =
  gentermpr (Termast.ast_of_constr at_top env t)

let pr_constr = gentermpr

let pr_pattern = gentermpr

let pr_qualid qid = str (string_of_qualid qid)

open Rawterm

let pr_arg pr x = spc () ++ pr x

let pr_red_flag pr r =
  (if r.rBeta then pr_arg str "Beta" else mt ()) ++
  (if r.rIota then pr_arg str "Iota" else mt ()) ++
  (if r.rZeta then pr_arg str "Zeta" else mt ()) ++
  (if r.rConst = [] then
     if r.rDelta then pr_arg str "Delta"
     else mt ()
   else
     pr_arg str "Delta" ++ (if r.rDelta then str "-" else mt ()) ++
     hov 0 (str "[" ++ prlist_with_sep spc pr r.rConst ++ str "]"))

open Genarg

let pr_metanum pr = function
  | AN (_,x) -> pr x
  | MetaNum (_,n) -> str "?" ++ int n

let pr_red_expr (pr_constr,pr_ref) = function
  | Red false -> str "Red"
  | Hnf -> str "Hnf"
  | Simpl -> str "Simpl"
  | Cbv f ->
      if f = {rBeta=true;rIota=true;rZeta=true;rDelta=true;rConst=[]} then
	str "Compute"
      else
	hov 1 (str "Cbv" ++ spc () ++ pr_red_flag pr_ref f)
  | Lazy f -> 
      hov 1 (str "Lazy" ++ spc () ++ pr_red_flag pr_ref f)
  | Unfold l ->
      hov 1 (str "Unfold" ++
        prlist (fun (nl,qid) ->
	  prlist (pr_arg int) nl ++ spc () ++ pr_ref qid) l)
  | Fold l -> hov 1 (str "Fold" ++ prlist (pr_arg pr_constr) l)
  | Pattern l ->
      hov 1 (str "Pattern" ++ 
        prlist(fun (nl,c) -> prlist (pr_arg int) nl ++ (pr_arg pr_constr) c) l)
  | Red true -> error "Shouldn't be accessible from user"
  | ExtraRedExpr (s,c) ->
      hov 1 (str s ++ pr_arg pr_constr c)

let rec pr_may_eval pr = function
  | ConstrEval (r,c) ->
      hov 0
        (str "Eval" ++ brk (1,1) ++ pr_red_expr (pr,pr_metanum pr_qualid) r ++
	 spc () ++ str "in" ++ brk (1,1) ++ pr c)
  | ConstrContext ((_,id),c) ->
      hov 0
	(str "Inst " ++ brk (1,1) ++ pr_id id ++ spc () ++
	 str "[" ++ pr c ++ str "]")
  | ConstrTypeOf c -> hov 0 (str "Check " ++ brk (1,1) ++ pr c)
  | ConstrTerm c -> pr c
