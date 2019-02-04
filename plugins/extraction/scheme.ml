(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(*s Production of Scheme syntax. *)

open Pp
open CErrors
open Util
open Names
open Miniml
open Mlutil
open Table
open Common

(*s Scheme renaming issues. *)

let keywords =
  List.fold_right (fun s -> Id.Set.add (Id.of_string s))
    [ "define"; "let"; "lambda"; "lambdas"; "match";
      "apply"; "car"; "cdr";
      "error"; "delay"; "force"; "_"; "__"]
    Id.Set.empty

let pp_comment s = str";; "++h 0 s++fnl ()

let pp_header_comment = function
  | None -> mt ()
  | Some com -> pp_comment com ++ fnl () ++ fnl ()

let preamble _ comment _ usf =
  pp_header_comment comment ++
  str ";; This extracted scheme code relies on some additional macros\n" ++
  str ";; available at http://www.pps.univ-paris-diderot.fr/~letouzey/scheme\n" ++
  str "(load \"macros_extr.scm\")\n\n" ++
  (if usf.mldummy then str "(define __ (lambda (_) __))\n\n" else mt ())

let pr_id id =
  str @@ String.map (fun c -> if c == '\'' then '~' else c) (Id.to_string id)

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
    | MLcons (_,r,args') ->
	assert (List.is_empty args);
	let st =
	  str "`" ++
	  paren (pp_global Cons r ++
		 (if List.is_empty args' then mt () else spc ()) ++
		 prlist_with_sep spc (pp_cons_args env) args')
	in
	if is_coinductive r then paren (str "delay " ++ st) else st
    | MLtuple _ -> user_err Pp.(str "Cannot handle tuples in Scheme yet.")
    | MLcase (_,_,pv) when not (is_regular_match pv) ->
	user_err Pp.(str "Cannot handle general patterns in Scheme yet.")
    | MLcase (_,t,pv) when is_custom_match pv ->
	let mkfun (ids,_,e) =
	  if not (List.is_empty ids) then named_lams (List.rev ids) e
	  else dummy_lams (ast_lift 1 e) 1
	in
	apply
	  (paren
	     (hov 2
		(str (find_custom_match pv) ++ fnl () ++
		 prvect (fun tr -> pp_expr env [] (mkfun tr) ++ fnl ()) pv
		 ++ pp_expr env [] t)))
    | MLcase (typ,t, pv) ->
        let e =
	  if not (is_coinductive_type typ) then pp_expr env [] t
	  else paren (str "force" ++ spc () ++ pp_expr env [] t)
	in
	apply (v 3 (paren (str "match " ++ e ++ fnl () ++ pp_pat env pv)))
    | MLfix (i,ids,defs) ->
	let ids',env' = push_vars (List.rev (Array.to_list ids)) env in
      	pp_fix env' i (Array.of_list (List.rev ids'),defs) args
    | MLexn s ->
	(* An [MLexn] may be applied, but I don't really care. *)
	paren (str "error" ++ spc () ++ qs s)
    | MLdummy _ ->
	str "__" (* An [MLdummy] may be applied, but I don't really care. *)
    | MLmagic a ->
	pp_expr env args a
    | MLaxiom -> paren (str "error \"AXIOM TO BE REALIZED\"")
    | MLuint _ ->
      paren (str "Prelude.error \"EXTRACTION OF UINT NOT IMPLEMENTED\"")

and pp_cons_args env = function
  | MLcons (_,r,args) when is_coinductive r ->
      paren (pp_global Cons r ++
	     (if List.is_empty args then mt () else spc ()) ++
	     prlist_with_sep spc (pp_cons_args env) args)
  | e -> str "," ++ pp_expr env [] e

and pp_one_pat env (ids,p,t) =
  let r = match p with
    | Pusual r -> r
    | Pcons (r,l) -> r (* cf. the check [is_regular_match] above *)
    | _ -> assert false
  in
  let ids,env' = push_vars (List.rev_map id_of_mlid ids) env in
  let args =
    if List.is_empty ids then mt ()
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
		  (Array.map2 (fun id b -> (id,b)) ids bl)) ++
	     fnl () ++
      	     hov 2 (pp_apply (pr_id (ids.(j))) true args))))

(*s Pretty-printing of a declaration. *)

let pp_decl = function
  | Dind _ -> mt ()
  | Dtype _ -> mt ()
  | Dfix (rv, defs,_) ->
      let names = Array.map
	(fun r -> if is_inline_custom r then mt () else pp_global Term r) rv
      in
      prvecti
	(fun i r ->
	  let void = is_inline_custom r ||
	    (not (is_custom r) &&
             match defs.(i) with MLexn "UNUSED" -> true | _ -> false)
	  in
	  if void then mt ()
	  else
	    hov 2
	      (paren (str "define " ++ names.(i) ++ spc () ++
			(if is_custom r then str (find_custom r)
			 else pp_expr (empty_env ()) [] defs.(i)))
	       ++ fnl ()) ++ fnl ())
	rv
  | Dterm (r, a, _) ->
      if is_inline_custom r then mt ()
      else
	hov 2 (paren (str "define " ++ pp_global Term r ++ spc () ++
			(if is_custom r then str (find_custom r)
			 else pp_expr (empty_env ()) [] a)))
	++ fnl2 ()

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
      (* should be expanded in extract_env *)

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
  file_naming = file_of_modfile;
  preamble = preamble;
  pp_struct = pp_struct;
  sig_suffix = None;
  sig_preamble = (fun _ _ _ _ -> mt ());
  pp_sig = (fun _ -> mt ());
  pp_decl = pp_decl;
}
