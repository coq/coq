(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(*s Production of Haskell syntax. *)

open Pp
open Util
open Names
open Term
open Miniml
open Mlutil
open Options
open Ocaml

(*s Haskell renaming issues. *)

let keywords =     
  List.fold_right (fun s -> Idset.add (id_of_string s))
  [ "case"; "class"; "data"; "default"; "deriving"; "do"; "else";
    "if"; "import"; "in"; "infix"; "infixl"; "infixr"; "instance"; 
    "let"; "module"; "newtype"; "of"; "then"; "type"; "where"; "_";
    "as"; "qualified"; "hiding" ; "prop" ; "arity" ]
  Idset.empty

let preamble prm =
  let m = match prm.mod_name with 
    | None -> "Main" 
    | Some m -> String.capitalize (string_of_id m) 
  in 
  [< 'sTR "module "; 'sTR m; 'sTR " where"; 'fNL; 'fNL;
     'sTR "type Prop = ()"; 'fNL;
     'sTR "prop = ()"; 'fNL; 'fNL;
     'sTR "type Arity = ()"; 'fNL;
     'sTR "arity = ()"; 'fNL; 'fNL >]

(*s The pretty-printing functor. *)

module Make = functor(P : Mlpp_param) -> struct

let pp_type_global = P.pp_type_global
let pp_global = P.pp_global
let rename_global = P.rename_global

let pr_lower_id id = pr_id (lowercase_id id)

let empty_env () = [], P.globals()

(*s Pretty-printing of types. [par] is a boolean indicating whether parentheses
    are needed or not. *)

let rec pp_type par t =
  let rec pp_rec par = function
    | Tvar id -> pr_lower_id id (* TODO: possible clash with Haskell kw *)
    | Tapp l ->
	(match collapse_type_app l with
	   | [] -> assert false
	   | [t] -> pp_rec par t
	   | t::l -> 
	       [< open_par par;
		  pp_rec false t; 'sPC;
		  prlist_with_sep (fun () -> [< 'sPC >]) (pp_type true) l; 
		  close_par par >])
    | Tarr (t1,t2) ->
	[< open_par par; pp_rec true t1; 'sPC; 'sTR "->"; 'sPC; 
	   pp_rec false t2; close_par par >]
    | Tglob r -> 
	pp_type_global r
    | Tprop ->
	string "Prop"
    | Tarity ->
	string "Arity"
  in 
  hOV 0 (pp_rec par t)

(*s Pretty-printing of expressions. [par] indicates whether
    parentheses are needed or not. [env] is the list of names for the
    de Bruijn variables. [args] is the list of collected arguments
    (already pretty-printed). *)

let expr_needs_par = function
  | MLlam _  -> true
  | MLcase _ -> true
  | _        -> false 

let rec pp_expr par env args = 
  let apply st = match args with
    | [] -> st
    | _  -> hOV 2 [< open_par par; st; 'sPC;
                     prlist_with_sep (fun () -> [< 'sPC >]) (fun s -> s) args;
                     close_par par >] 
  in
  function
    | MLrel n -> 
	apply (pr_id (get_db_name n env))
    | MLapp (f,args') ->
	let stl = List.map (pp_expr true env []) args' in
        pp_expr par env (stl @ args) f
    | MLlam _ as a -> 
      	let fl,a' = collect_lams a in
	let fl,env' = push_vars fl env in
	let st = [< pp_abst (List.rev fl); pp_expr false env' [] a' >] in
	if args = [] then
          [< open_par par; st; close_par par >]
        else
          apply [< 'sTR "("; st; 'sTR ")" >]
    | MLletin (id,a1,a2) ->
	let id',env' = push_vars [id] env in
	let par' = par || args <> [] in
	let par2 = not par' && expr_needs_par a2 in
	apply 
	  (hOV 0 [< open_par par';
		    hOV 2 [< 'sTR "let "; pr_id (List.hd id'); 'sTR " ="; 'sPC;
			     pp_expr false env [] a1; 'sPC; 'sTR "in" >];
		    'sPC;
		    pp_expr par2 env' [] a2;
		    close_par par' >])
    | MLglob r -> 
	apply (pp_global r)
    | MLcons (r,[]) ->
	pp_global r
    | MLcons (r,[a]) ->
	[< open_par par; pp_global r; 'sPC;
	   pp_expr true env [] a; close_par par >]
    | MLcons (r,args') ->
	[< open_par par; pp_global r; 'sPC;
	   prlist_with_sep (fun () -> [< 'sPC >]) (pp_expr true env []) args';
	   close_par par >]
    | MLcase (t, pv) ->
      	apply
      	  [< if args <> [] then [< 'sTR "(" >]  else open_par par;
      	     v 0 [< 'sTR "case "; pp_expr false env [] t; 'sTR " of";
		    'fNL; 'sTR "  "; pp_pat env pv >];
	     if args <> [] then [< 'sTR ")" >] else close_par par >]
    | MLfix (i,ids,defs) ->
	let ids',env' = push_vars (List.rev (Array.to_list ids)) env in
      	pp_fix par env' (Some i) (Array.of_list (List.rev ids'),defs) args
    | MLexn str -> 
	[< open_par par; 'sTR "error"; 'sPC; 'qS str; close_par par >]
    | MLprop ->
	string "prop"
    | MLarity ->
	string "arity"
    | MLcast (a,t) ->
	[< open_par true; pp_expr false env args a; 'sPC; 'sTR "::"; 'sPC; 
	   pp_type false t; close_par true >]
    | MLmagic a ->
	[< open_par true; 'sTR "Obj.magic"; 'sPC; 
	   pp_expr false env args a; close_par true >]

and pp_pat env pv = 
  let pp_one_pat (name,ids,t) =
    let ids,env' = push_vars (List.rev ids) env in
    let par = expr_needs_par t in
    hOV 2 [< pp_global name;
	     begin match ids with 
	       | [] -> [< >]
	       | _  -> [< 'sTR " "; 
			  prlist_with_sep 
			    (fun () -> [< 'sPC >]) pr_id (List.rev ids) >]
	     end;
	     'sTR " ->"; 'sPC; pp_expr par env' [] t >]
  in 
  [< prvect_with_sep (fun () -> [< 'fNL; 'sTR "  " >]) pp_one_pat pv >]

(*s names of the functions ([ids]) are already pushed in [env],
    and passed here just for convenience. *)

and pp_fix par env in_p (ids,bl) args =
  [< open_par par; 
     v 0 [< 'sTR "let { " ;
	    prvect_with_sep
      	      (fun () -> [< 'sTR "; "; 'fNL >])
	      (fun (fi,ti) -> pp_function env (pr_id fi) ti)
	      (array_map2 (fun id b -> (id,b)) ids bl);
	    'sTR " }";'fNL;
	    match in_p with
	      | Some j -> 
      		  hOV 2 [< 'sTR "in "; pr_id ids.(j);
			   if args <> [] then
			     [< 'sTR " "; 
				prlist_with_sep (fun () -> [<'sTR " ">])
				  (fun s -> s) args >]
			   else
			     [< >] >]
	      | None -> 
		  [< >] >];
     close_par par >]

and pp_function env f t =
  let bl,t' = collect_lams t in
  let bl,env' = push_vars bl env in
  [< f; pr_binding (List.rev bl);
     'sTR " ="; 'fNL; 'sTR "  ";
     hOV 2 (pp_expr false env' [] t') >]
	
let pp_ast a = hOV 0 (pp_expr false (empty_env ()) [] a)

(*s Pretty-printing of inductive types declaration. *)

let pp_one_inductive (pl,name,cl) =
  let pp_constructor (id,l) =
    [< pp_global id;
       match l with
         | [] -> [< >] 
	 | _  -> [< 'sTR " " ;
      	       	    prlist_with_sep 
		      (fun () -> [< 'sTR " " >]) (pp_type true) l >] >]
  in
  [< 'sTR (if cl = [] then "type " else "data "); 
     pp_type_global name; 'sTR " ";
     prlist_with_sep (fun () -> [< 'sTR " " >]) pr_lower_id pl;
     if pl = [] then [< >] else [< 'sTR " " >];
     if cl = [] then
       [< 'sTR "= () -- empty inductive" >]
     else
       [< v 0 [< 'sTR "= ";
		 prlist_with_sep (fun () -> [< 'fNL; 'sTR "  | " >])
                   pp_constructor cl >] >] >]

let pp_inductive il =
  [< prlist_with_sep (fun () -> [< 'fNL >]) pp_one_inductive il; 'fNL >]

(*s Pretty-printing of a declaration. *)

let pp_decl = function
  | Dtype ([], _) -> 
      [< >]
  | Dtype (i, _) -> 
      hOV 0 (pp_inductive i)
  | Dabbrev (r, l, t) ->
      hOV 0 [< 'sTR "type "; pp_type_global r; 'sPC; 
	       prlist_with_sep (fun () -> [< 'sTR " " >]) pr_lower_id l;
	       if l <> [] then [< 'sTR " " >] else [< >]; 'sTR "="; 'sPC;
	       pp_type false t; 'fNL >]
  | Dglob (r, MLfix (i,ids,defs)) ->
      let env = empty_env () in
      let ids',env' = push_vars (List.rev (Array.to_list ids)) env in
      [< prlist_with_sep (fun () -> [< 'fNL >])
	   (fun (fi,ti) -> pp_function env' (pr_id fi) ti)
	   (List.combine (List.rev ids') (Array.to_list defs));
	 'fNL;
	 let id = rename_global r in
	 let idi = List.nth (List.rev ids') i in
	 if id <> idi then
	   [< 'fNL; pr_id id; 'sTR " = "; pr_id idi; 'fNL >]
	 else
	   [< >] >]
  | Dglob (r, a) ->
      hOV 0 [< pp_function (empty_env ()) (pp_global r) a; 'fNL >]
  | Dcustom (r,s) -> 
      hOV 0  [< pp_global r; 'sTR " ="; 
		'sPC; 'sTR s; 'fNL  >]

let pp_type = pp_type false

end

