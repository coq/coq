(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(*s Production of Scheme syntax. *)

open Pp
open Util
open Names
open Nameops
open Libnames
open Miniml
open Mlutil
open Table
open Common

(*s Scheme renaming issues. *)

let keywords =
  List.fold_right (fun s -> Idset.add (id_of_string s))
    [ "define"; "let"; "lambda"; "lambdas"; "match";
      "apply"; "car"; "cdr";
      "error"; "delay"; "force"; "_"; "__"]
    Idset.empty

let preamble _ _ usf =
  str ";; This extracted scheme code relies on some additional macros\n" ++
  str ";; available at http://www.pps.jussieu.fr/~letouzey/scheme\n" ++
  str "(load \"macros_extr.scm\")\n\n" ++
  (if usf.mldummy then str "(define __ (lambda (_) __))\n\n" else mt ())

let pr_id id =
  let s = string_of_id id in
  for i = 0 to String.length s - 1 do
    if s.[i] = '\'' then s.[i] <- '~'
  done;
  str s

let paren = pp_par true

let pp_abst st = function
  | [] -> assert false
  | [id] -> paren (str "lambda " ++ paren (pr_id id) ++ spc () ++ st)
  | l -> paren
	(str "lambdas " ++ paren (prlist_with_sep spc pr_id l) ++ spc () ++ st)

let pp_apply st _ = function
  | [] -> st
  | [a] -> hov 2 (paren (st ++ spc () ++ a))
  | args -> hov 2 (paren (str "@ " ++ st ++
			  (prlist_strict (fun x -> spc () ++ x) args)))

(*s The pretty-printer for Scheme syntax *)

let pp_global k r = str (Common.pp_global k r)

(*s Pretty-printing of expressions.  *)

let rec pp_expr env args =
  let apply st = pp_apply st true args in
  function
    | MLrel n ->
	let id = get_db_name n env in apply (pr_id id)
    | MLapp (f,args') ->
	let stl = List.map (pp_expr env []) args' in
        pp_expr env (stl @ args) f
    | MLlam _ as a ->
      	let fl,a' = collect_lams a in
	let fl,env' = push_vars (List.map id_of_mlid fl) env in
	apply (pp_abst (pp_expr env' [] a') (List.rev fl))
    | MLletin (id,a1,a2) ->
	let i,env' = push_vars [id_of_mlid id] env in
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
	apply (pp_global Term r)
    | MLcons (i,r,args') ->
	assert (args=[]);
	let st =
	  str "`" ++
	  paren (pp_global Cons r ++
		 (if args' = [] then mt () else spc ()) ++
		 prlist_with_sep spc (pp_cons_args env) args')
	in
	if i = Coinductive then paren (str "delay " ++ st) else st
    | MLcase (_,t,pv) when is_custom_match pv ->
	let mkfun (_,ids,e) =
	  if ids <> [] then named_lams (List.rev ids) e
	  else dummy_lams (ast_lift 1 e) 1
	in
	hov 2 (str (find_custom_match pv) ++ fnl () ++
		 prvect (fun tr -> pp_expr env [] (mkfun tr) ++ fnl ()) pv
	       ++ pp_expr env [] t)
     | MLcase ((i,_),t, pv) ->
	let e =
	  if i <> Coinductive then pp_expr env [] t
	  else paren (str "force" ++ spc () ++ pp_expr env [] t)
	in
	apply (v 3 (paren (str "match " ++ e ++ fnl () ++ pp_pat env pv)))
    | MLfix (i,ids,defs) ->
	let ids',env' = push_vars (List.rev (Array.to_list ids)) env in
      	pp_fix env' i (Array.of_list (List.rev ids'),defs) args
    | MLexn s ->
	(* An [MLexn] may be applied, but I don't really care. *)
	paren (str "error" ++ spc () ++ qs s)
    | MLdummy ->
	str "__" (* An [MLdummy] may be applied, but I don't really care. *)
    | MLmagic a ->
	pp_expr env args a
    | MLaxiom -> paren (str "error \"AXIOM TO BE REALIZED\"")

and pp_cons_args env = function
  | MLcons (i,r,args) when i<>Coinductive ->
      paren (pp_global Cons r ++
	     (if args = [] then mt () else spc ()) ++
	     prlist_with_sep spc (pp_cons_args env) args)
  | e -> str "," ++ pp_expr env [] e


and pp_one_pat env (r,ids,t) =
  let ids,env' = push_vars (List.rev_map id_of_mlid ids) env in
  let args =
    if ids = [] then mt ()
    else (str " " ++ prlist_with_sep spc pr_id (List.rev ids))
  in
  (pp_global Cons r ++ args), (pp_expr env' [] t)

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
		  (fun (fi,ti) ->
		     paren ((pr_id fi) ++ spc () ++ (pp_expr env [] ti)))
		  (array_map2 (fun id b -> (id,b)) ids bl)) ++
	     fnl () ++
      	     hov 2 (pp_apply (pr_id (ids.(j))) true args))))

(*s Pretty-printing of a declaration. *)

let pp_decl = function
  | Dind _ -> mt ()
  | Dtype _ -> mt ()
  | Dfix (rv, defs,_) ->
      let ppv = Array.map (pp_global Term) rv in
      prvect_with_sep fnl
	(fun (pi,ti) ->
	   hov 2
	     (paren (str "define " ++ pi ++ spc () ++
		     (pp_expr (empty_env ()) [] ti))
	      ++ fnl ()))
	(array_map2 (fun p b -> (p,b)) ppv defs) ++
      fnl ()
  | Dterm (r, a, _) ->
      if is_inline_custom r then mt ()
      else
	if is_custom r then
	  hov 2 (paren (str "define " ++ pp_global Term r ++ spc () ++
			  str (find_custom r))) ++ fnl () ++ fnl ()
	else
	  hov 2 (paren (str "define " ++ pp_global Term r ++ spc () ++
			  pp_expr (empty_env ()) [] a)) ++ fnl () ++ fnl ()

let rec pp_structure_elem = function
  | (l,SEdecl d) -> pp_decl d
  | (l,SEmodule m) -> pp_module_expr m.ml_mod_expr
  | (l,SEmodtype m) -> mt ()
      (* for the moment we simply discard module type *)

and pp_module_expr = function
  | MEstruct (mp,sel) -> prlist_strict pp_structure_elem sel
  | MEfunctor _ -> mt ()
      (* for the moment we simply discard unapplied functors *)
  | MEident _ | MEapply _ -> assert false
      (* should be expansed in extract_env *)

let pp_struct =
  let pp_sel (mp,sel) =
    push_visible mp [];
    let p = prlist_strict pp_structure_elem sel in
    pop_visible (); p
  in
  prlist_strict pp_sel

let scheme_descr = {
  keywords = keywords;
  file_suffix = ".scm";
  capital_file = false;
  preamble = preamble;
  pp_struct = pp_struct;
  sig_suffix = None;
  sig_preamble = (fun _ _ _ -> mt ());
  pp_sig = (fun _ -> mt ());
  pp_decl = pp_decl;
}
