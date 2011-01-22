(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(*s Production of Haskell syntax. *)

open Pp
open Util
open Names
open Nameops
open Libnames
open Table
open Miniml
open Mlutil
open Common

(*s Haskell renaming issues. *)

let pr_lower_id id = str (String.uncapitalize (string_of_id id))
let pr_upper_id id = str (String.capitalize (string_of_id id))

let keywords =
  List.fold_right (fun s -> Idset.add (id_of_string s))
  [ "case"; "class"; "data"; "default"; "deriving"; "do"; "else";
    "if"; "import"; "in"; "infix"; "infixl"; "infixr"; "instance";
    "let"; "module"; "newtype"; "of"; "then"; "type"; "where"; "_"; "__";
    "as"; "qualified"; "hiding" ; "unit" ; "unsafeCoerce" ]
  Idset.empty

let preamble mod_name used_modules usf =
  let pp_import mp = str ("import qualified "^ string_of_modfile mp ^"\n")
  in
  (if not usf.magic then mt ()
   else
     str "{-# OPTIONS_GHC -cpp -fglasgow-exts #-}\n" ++
     str "{- For Hugs, use the option -F\"cpp -P -traditional\" -}\n\n")
  ++
  str "module " ++ pr_upper_id mod_name ++ str " where" ++ fnl2 () ++
  str "import qualified Prelude" ++ fnl () ++
  prlist pp_import used_modules ++ fnl () ++
  (if used_modules = [] then mt () else fnl ()) ++
  (if not usf.magic then mt ()
   else str "\
#ifdef __GLASGOW_HASKELL__
import qualified GHC.Base
unsafeCoerce = GHC.Base.unsafeCoerce#
#else
-- HUGS
import qualified IOExts
unsafeCoerce = IOExts.unsafeCoerce
#endif" ++ fnl2 ())
  ++
  (if not usf.mldummy then mt ()
   else str "__ = Prelude.error \"Logical or arity value used\"" ++ fnl2 ())

let pp_abst = function
  | [] -> (mt ())
  | l  -> (str "\\" ++
             prlist_with_sep (fun () -> (str " ")) pr_id l ++
             str " ->" ++ spc ())

(*s The pretty-printer for haskell syntax *)

let pp_global k r =
  if is_inline_custom r then str (find_custom r)
  else str (Common.pp_global k r)

(*s Pretty-printing of types. [par] is a boolean indicating whether parentheses
    are needed or not. *)

let kn_sig =
  let specif = MPfile (dirpath_of_string "Coq.Init.Specif") in
  make_kn specif empty_dirpath (mk_label "sig")

let rec pp_type par vl t =
  let rec pp_rec par = function
    | Tmeta _ | Tvar' _ -> assert false
    | Tvar i -> (try pr_id (List.nth vl (pred i)) with _ -> (str "a" ++ int i))
    | Tglob (r,[]) -> pp_global Type r
    | Tglob (r,l) ->
	if r = IndRef (mind_of_kn kn_sig,0) then
	  pp_type true vl (List.hd l)
	else
	  pp_par par
	    (pp_global Type r ++ spc () ++
	     prlist_with_sep spc (pp_type true vl) l)
    | Tarr (t1,t2) ->
	pp_par par
	  (pp_rec true t1 ++ spc () ++ str "->" ++ spc () ++ pp_rec false t2)
    | Tdummy _ -> str "()"
    | Tunknown -> str "()"
    | Taxiom -> str "() -- AXIOM TO BE REALIZED\n"
 in
  hov 0 (pp_rec par t)

(*s Pretty-printing of expressions. [par] indicates whether
    parentheses are needed or not. [env] is the list of names for the
    de Bruijn variables. [args] is the list of collected arguments
    (already pretty-printed). *)

let expr_needs_par = function
  | MLlam _  -> true
  | MLcase _ -> true
  | _        -> false


let rec pp_expr par env args =
  let par' = args <> [] || par
  and apply st = pp_apply st par args in
  function
    | MLrel n ->
	let id = get_db_name n env in apply (pr_id id)
    | MLapp (f,args') ->
	let stl = List.map (pp_expr true env []) args' in
        pp_expr par env (stl @ args) f
    | MLlam _ as a ->
      	let fl,a' = collect_lams a in
	let fl,env' = push_vars (List.map id_of_mlid fl) env in
	let st = (pp_abst (List.rev fl) ++ pp_expr false env' [] a') in
	apply (pp_par par' st)
    | MLletin (id,a1,a2) ->
	let i,env' = push_vars [id_of_mlid id] env in
	let pp_id = pr_id (List.hd i)
	and pp_a1 = pp_expr false env [] a1
	and pp_a2 = pp_expr (not par && expr_needs_par a2) env' [] a2 in
	hv 0
	  (apply
	     (pp_par par'
		(hv 0
		   (hov 5
		      (str "let" ++ spc () ++ pp_id ++ str " = " ++ pp_a1) ++
		    spc () ++ str "in") ++
		 spc () ++ hov 0 pp_a2)))
    | MLglob r ->
	apply (pp_global Term r)
    | MLcons (_,r,[]) ->
	assert (args=[]); pp_global Cons r
    | MLcons (_,r,[a]) ->
	assert (args=[]);
	pp_par par (pp_global Cons r ++ spc () ++ pp_expr true env [] a)
    | MLcons (_,r,args') ->
	assert (args=[]);
	pp_par par (pp_global Cons r ++ spc () ++
		    prlist_with_sep spc (pp_expr true env []) args')
    | MLcase (_,t, pv) when is_custom_match pv ->
	let mkfun (_,ids,e) =
	  if ids <> [] then named_lams (List.rev ids) e
	  else dummy_lams (ast_lift 1 e) 1
	in
	hov 2 (str (find_custom_match pv) ++ fnl () ++
		 prvect (fun tr -> pp_expr true env [] (mkfun tr) ++ fnl ()) pv
	       ++ pp_expr true env [] t)
    | MLcase (info,t, pv) ->
      	apply (pp_par par'
		 (v 0 (str "case " ++ pp_expr false env [] t ++ str " of" ++
		       fnl () ++ str "  " ++ pp_pat env info pv)))
    | MLfix (i,ids,defs) ->
	let ids',env' = push_vars (List.rev (Array.to_list ids)) env in
      	pp_fix par env' i (Array.of_list (List.rev ids'),defs) args
    | MLexn s ->
	(* An [MLexn] may be applied, but I don't really care. *)
	pp_par par (str "Prelude.error" ++ spc () ++ qs s)
    | MLdummy ->
	str "__" (* An [MLdummy] may be applied, but I don't really care. *)
    | MLmagic a ->
	pp_apply (str "unsafeCoerce") par (pp_expr true env [] a :: args)
    | MLaxiom -> pp_par par (str "Prelude.error \"AXIOM TO BE REALIZED\"")

and pp_pat env info pv =
  let pp_one_pat (name,ids,t) =
    let ids,env' = push_vars (List.rev_map id_of_mlid ids) env in
    let par = expr_needs_par t in
    hov 2 (pp_global Cons name ++
	   (match ids with
	      | [] -> mt ()
	      | _  -> (str " " ++
		       prlist_with_sep
			 (fun () -> (spc ())) pr_id (List.rev ids))) ++
	   str " ->" ++ spc () ++ pp_expr par env' [] t)
  in
  let factor_br, factor_set = try match info.m_same with
    | BranchFun ints ->
        let i = Intset.choose ints in
	branch_as_fun info.m_typs pv.(i), ints
    | BranchCst ints ->
        let i = Intset.choose ints in
        ast_pop (branch_as_cst pv.(i)), ints
    | BranchNone -> MLdummy, Intset.empty
  with _ -> MLdummy, Intset.empty
  in
  let last = Array.length pv - 1 in
  prvecti
    (fun i x -> if Intset.mem i factor_set then mt () else
       (pp_one_pat pv.(i) ++
       if i = last && Intset.is_empty factor_set then mt () else
       fnl () ++ str "  ")) pv
  ++
  if Intset.is_empty factor_set then mt () else
  let par = expr_needs_par factor_br in
  match info.m_same with
    | BranchFun _ ->
        let ids, env' = push_vars [anonymous_name] env in
        pr_id (List.hd ids) ++ str " ->" ++ spc () ++
	  pp_expr par env' [] factor_br
    | BranchCst _ ->
        str "_ ->" ++ spc () ++ pp_expr par env [] factor_br
    | BranchNone -> mt ()

(*s names of the functions ([ids]) are already pushed in [env],
    and passed here just for convenience. *)

and pp_fix par env i (ids,bl) args =
  pp_par par
    (v 0
       (v 2 (str "let" ++ fnl () ++
	     prvect_with_sep fnl
	       (fun (fi,ti) -> pp_function env (pr_id fi) ti)
	       (array_map2 (fun a b -> a,b) ids bl)) ++
	fnl () ++
	hov 2 (str "in " ++ pp_apply (pr_id ids.(i)) false args)))

and pp_function env f t =
  let bl,t' = collect_lams t in
  let bl,env' = push_vars (List.map id_of_mlid bl) env in
  (f ++ pr_binding (List.rev bl) ++
     str " =" ++ fnl () ++ str "  " ++
     hov 2 (pp_expr false env' [] t'))

(*s Pretty-printing of inductive types declaration. *)

let pp_comment s = str "-- " ++ s ++ fnl ()

let pp_logical_ind packet =
  pp_comment (pr_id packet.ip_typename ++ str " : logical inductive") ++
  pp_comment (str "with constructors : " ++
	      prvect_with_sep spc pr_id packet.ip_consnames)

let pp_singleton kn packet =
  let l = rename_tvars keywords packet.ip_vars in
  let l' = List.rev l in
  hov 2 (str "type " ++ pp_global Type (IndRef (kn,0)) ++ spc () ++
	 prlist_with_sep spc pr_id l ++
	 (if l <> [] then str " " else mt ()) ++ str "=" ++ spc () ++
	 pp_type false l' (List.hd packet.ip_types.(0)) ++ fnl () ++
	 pp_comment (str "singleton inductive, whose constructor was " ++
		     pr_id packet.ip_consnames.(0)))

let pp_one_ind ip pl cv =
  let pl = rename_tvars keywords pl in
  let pp_constructor (r,l) =
    (pp_global Cons r ++
     match l with
       | [] -> (mt ())
       | _  -> (str " " ++
      	       	prlist_with_sep
		  (fun () -> (str " ")) (pp_type true pl) l))
  in
  str (if Array.length cv = 0 then "type " else "data ") ++
  pp_global Type (IndRef ip) ++ str " " ++
  prlist_with_sep (fun () -> str " ") pr_lower_id pl ++
  (if pl = [] then mt () else str " ") ++
  if Array.length cv = 0 then str "= () -- empty inductive"
  else
    (v 0 (str "= " ++
	  prvect_with_sep (fun () -> fnl () ++ str "| ") pp_constructor
	    (Array.mapi (fun i c -> ConstructRef (ip,i+1),c) cv)))

let rec pp_ind first kn i ind =
  if i >= Array.length ind.ind_packets then
    if first then mt () else fnl ()
  else
    let ip = (kn,i) in
    let p = ind.ind_packets.(i) in
    if is_custom (IndRef (kn,i)) then pp_ind first kn (i+1) ind
    else
      if p.ip_logical then
	pp_logical_ind p ++ pp_ind first kn (i+1) ind
      else
	pp_one_ind ip p.ip_vars p.ip_types ++ fnl () ++
	pp_ind false kn (i+1) ind


(*s Pretty-printing of a declaration. *)

let pp_string_parameters ids = prlist (fun id -> str id ++ str " ")

let pp_decl = function
  | Dind (kn,i) when i.ind_kind = Singleton ->
      pp_singleton (mind_of_kn kn) i.ind_packets.(0) ++ fnl ()
  | Dind (kn,i) -> hov 0 (pp_ind true (mind_of_kn kn) 0 i)
  | Dtype (r, l, t) ->
      if is_inline_custom r then mt ()
      else
	let l = rename_tvars keywords l in
	let st =
	  try
	    let ids,s = find_type_custom r in
	    prlist (fun id -> str (id^" ")) ids ++ str "=" ++ spc () ++ str s
	  with Not_found ->
	    prlist (fun id -> pr_id id ++ str " ") l ++
	    if t = Taxiom then str "= () -- AXIOM TO BE REALIZED\n"
	    else str "=" ++ spc () ++ pp_type false l t
	in
	hov 2 (str "type " ++ pp_global Type r ++ spc () ++ st) ++ fnl2 ()
  | Dfix (rv, defs, typs) ->
      let names = Array.map
	(fun r -> if is_inline_custom r then mt () else pp_global Term r) rv
      in
      prvecti
	(fun i r ->
	  if is_inline_custom r then mt ()
	  else
	    names.(i) ++ str " :: " ++ pp_type false [] typs.(i) ++ fnl ()
	    ++ pp_function (empty_env ()) names.(i) defs.(i) ++ fnl2 ())
	rv
  | Dterm (r, a, t) ->
      if is_inline_custom r then mt ()
      else
	let e = pp_global Term r in
	e ++ str " :: " ++ pp_type false [] t ++ fnl () ++
	  if is_custom r then
	    hov 0 (e ++ str " = " ++ str (find_custom r) ++ fnl2 ())
	  else
	    hov 0 (pp_function (empty_env ()) e a ++ fnl2 ())

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


let haskell_descr = {
  keywords = keywords;
  file_suffix = ".hs";
  preamble = preamble;
  pp_struct = pp_struct;
  sig_suffix = None;
  sig_preamble = (fun _ _ _ -> mt ());
  pp_sig = (fun _ -> mt ());
  pp_decl = pp_decl;
}
