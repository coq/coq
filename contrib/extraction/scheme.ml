(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(*s Production of Scheme syntax. *)

open Pp
open Util
open Names
open Nameops
open Term
open Miniml
open Table
open Mlutil
open Options
open Nametab
open Ocaml

(*s Scheme renaming issues. *)

let keywords =     
  List.fold_right (fun s -> Idset.add (id_of_string s))
    [ "define"; "let"; "lambda"; "lambdas"; "match-case"; 
      "apply"; "car"; "cdr"; 
      "error"; "delay"; "force"; "_"; "__"] 
    Idset.empty
    

let preamble _ _ print_dummy = 
  (if print_dummy then 
     str "(define __ (lambda (_) __))" 
     ++ fnl () ++ fnl()
   else mt ())

let paren st = str "(" ++ st ++ str ")"

let pp_abst st = function 
  | [] -> assert false
  | [id] -> paren (str "lambda " ++ paren (pr_id id) ++ spc () ++ st)
  | l -> paren 
	(str "lambdas " ++ paren (prlist_with_sep spc pr_id l) ++ spc () ++ st)

(*s The pretty-printing functor. *)

module Make = functor(P : Mlpp_param) -> struct

let pp_global r env = P.pp_global r false (Some (snd env))
let pp_global' r = P.pp_global r false None

let rename_global r = P.rename_global r false 

let empty_env () = [], P.globals()

let rec apply st = function 
  | [] -> st 
  | a :: args -> apply (paren (st ++ spc () ++ a)) args 

(*s Pretty-printing of expressions.  *)

let rec pp_expr env args = 
  let apply st = apply st args in 
  function
    | MLrel n -> 
	let id = get_db_name n env in apply (pr_id id)
    | MLapp (f,args') ->
	let stl = List.map (pp_expr env []) args' in
        pp_expr env (stl @ args) f
    | MLlam _ as a -> 
      	let fl,a' = collect_lams a in
	let fl,env' = push_vars fl env in
	pp_abst (pp_expr env' [] a') (List.rev fl)
    | MLletin (id,a1,a2) ->
	let i,env' = push_vars [id] env in
	apply 
	  (hv 0 
	     (hov 2 
		(paren 
		   (str "let " ++ 
		    paren 
		      (paren 
			 (pr_id (List.hd i) ++ spc () ++ pp_expr env [] a1)) 
		    ++ spc () ++ hov 0 (pp_expr env' [] a2)))))
    | MLglob r -> 
	apply (pp_global r env)
    | MLcons (r,args') ->
	assert (args=[]);
	let st = 
	  str "`" ++ 
	  paren (pp_global r env ++ 
		 (if args' = [] then mt () else (spc () ++ str ",")) ++
		 prlist_with_sep 
		   (fun () -> spc () ++ str ",") 
		   (pp_expr env []) args')
	in 
	if Refset.mem r !cons_cofix then 
	  paren (str "delay " ++ st)
        else st 
    | MLcase (t, pv) ->
	let r,_,_ = pv.(0) in 
	let e = if Refset.mem r !cons_cofix then 
	  paren (str "force" ++ spc () ++ pp_expr env [] t)
	else 
	  pp_expr env [] t 	
	in apply (v 3 (paren 
			 (str "match-case " ++ e ++ fnl () ++ pp_pat env pv)))
    | MLfix (i,ids,defs) ->
	let ids',env' = push_vars (List.rev (Array.to_list ids)) env in
      	pp_fix env' i (Array.of_list (List.rev ids'),defs) args
    | MLexn s -> 
	(* An [MLexn] may be applied, but I don't really care. *)
	paren (str "absurd")
    | MLdummy ->
	str "`_" (* An [MLdummy] may be applied, but I don't really care. *)
    | MLdummy' -> 
	str "__" (* idem *)
    | MLcast (a,t) ->
	pp_expr env args a
    | MLmagic a ->
	pp_expr env args a


and pp_one_pat env (r,ids,t) = 
  let pp_arg id = str "?" ++ pr_id id in 
  let ids,env' = push_vars (List.rev ids) env in
  let args = 
    if ids = [] then mt () 
    else (str " " ++ prlist_with_sep spc pp_arg (List.rev ids))
  in 
  (pp_global r env ++ args), (pp_expr env' [] t)
  
and pp_pat env pv = 
  prvect_with_sep fnl  
    (fun x -> let s1,s2 = pp_one_pat env x in 
     hov 2 (str "((" ++ s1 ++ str ")" ++ spc () ++ s2 ++ str ")")) pv

(*s names of the functions ([ids]) are already pushed in [env],
    and passed here just for convenience. *)

and pp_fix env j (ids,bl) args =
    paren 
      (str "letrec " ++
       (v 0 (paren 
	       (prvect_with_sep fnl
		  (fun (fi,ti) -> paren ((pr_id fi) ++ (pp_expr env [] ti)))
		  (array_map2 (fun id b -> (id,b)) ids bl)) ++
	     fnl () ++
      	     hov 2 (apply (pr_id (ids.(j))) args))))

(*s Pretty-printing of a declaration. *)

let pp_decl = function
  | Dind _ -> mt ()
  | DdummyType _ -> mt () 
  | Dtype _ -> mt () 
  | DcustomType _ -> mt ()
  | Dfix (rv, defs) ->
      let ids = Array.map rename_global rv in 
      let env = List.rev (Array.to_list ids), P.globals() in
      prvect_with_sep 
	fnl 
	(fun (fi,ti) -> 
	   hov 2 
	     (paren (str "define " ++ pr_id fi ++ spc () ++ 
		     (pp_expr env [] ti)) 
	      ++ fnl ()))
	(array_map2 (fun id b -> (id,b)) ids defs)
  | Dterm (r, a) ->
      hov 2 (paren (str "define " ++ (pp_global' r) ++ spc () ++
		    pp_expr (empty_env ()) [] a)) ++ fnl ()  
  | DcustomTerm (r,s) -> 
      hov 2 (paren (str "define " ++ pp_global' r ++ spc () ++ str s) ++ fnl ())

end

