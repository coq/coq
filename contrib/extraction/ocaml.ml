(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(*s Production of Ocaml syntax. *)

open Pp
open Util
open Names
open Term
open Miniml

(*s Some utility functions. *)

let string s = [< 'sTR s >]

let open_par = function true -> string "(" | false -> [<>]

let close_par = function true -> string ")" | false -> [<>]

let rec collapse_type_app = function
  | (Tapp l1) :: l2 -> collapse_type_app (l1@l2)
  | l -> l

let pp_tuple f = function
  | [] -> [< >]
  | [x] -> f x
  | l -> [< 'sTR "(";
      	    prlist_with_sep (fun () -> [< 'sTR ","; 'sPC >]) f l;
	    'sTR ")" >]

let pp_boxed_tuple f = function
  | [] -> [< >]
  | [x] -> f x
  | l -> [< 'sTR "(";
      	    hOV 0 [< prlist_with_sep (fun () -> [< 'sTR ","; 'sPC >]) f l;
		     'sTR ")" >] >]

let space_if = function true -> [< 'sPC >] | false -> [<>]

(* collect_lambda MLlam(id1,...MLlam(idn,t)...) = [id1;...;idn],t *)

let collect_lambda = 
  let rec collect acc = function
    | MLlam(id,t) -> collect (id::acc) t
    | x           -> acc,x
  in 
  collect []

let rec rename_bvars avoid = function
  | [] -> []
  | id :: idl ->
      let v = next_ident_away id avoid in 
      v :: (rename_bvars (v::avoid) idl)

let abst = function
  | [] -> [< >]
  | l  -> [< 'sTR "fun " ;
             prlist_with_sep (fun  ()-> [< 'sTR " " >]) pr_id l;
             'sTR " ->" ; 'sPC >]

let pr_binding = function
  | [] -> [< >]
  | l  -> [< 'sTR " "; prlist_with_sep (fun () -> [< 'sTR " " >]) pr_id l >]

(*s The pretty-printing functor. *)

module Make = functor(P : Mlpp_param) -> struct

(*s Pretty-printing of types. [par] is a boolean indicating whether parentheses
    are needed or not. *)

let pp_type t =
  let rec pp_rec par = function
    | Tvar id -> 
	string ("'" ^ string_of_id id)
    | Tapp l ->
	(match collapse_type_app l with
	   | [] -> assert false
	   | [t] -> pp_rec par t
	   | t::l -> [< open_par par; pp_tuple (pp_rec false) l; 
			space_if (l <>[]); pp_rec false t; close_par par >])
    | Tarr (t1,t2) ->
	[< open_par par; pp_rec true t1; 'sPC; 'sTR"->"; 'sPC; 
	   pp_rec false t2; close_par par >]
    | Tglob r -> 
	P.pp_global r
    | Tprop ->
	string "prop"
    | Tarity ->
	string "arity"
  in 
  hOV 0 (pp_rec false t)

(*s Pretty-printing of expressions. [par] indicates whether
    parentheses are needed or not. [env] is the list of names for the
    de Bruijn variables. [args] is the list of collected arguments
    (already pretty-printed). *)

let rec pp_expr par env args = 
  let apply st = match args with
    | [] -> st
    | _  -> hOV 2 [< open_par par; st; 'sPC;
                     prlist_with_sep (fun () -> [<'sPC>]) (fun s -> s) args;
                     close_par par >] 
  in
  function
    | MLrel n -> 
	apply (pr_id (List.nth env (pred n)))
    | MLapp (f,args') ->
	let stl = List.map (pp_expr true env []) args' in
        pp_expr par env (stl @ args) f
    | MLlam _ as a -> 
      	let fl,a' = collect_lambda a in
	let fl = rename_bvars env fl in
	let st = [< abst (List.rev fl); pp_expr false (fl@env) [] a' >] in
	if args = [] then
          [< open_par par; st; close_par par >]
        else
          apply [< 'sTR "("; st; 'sTR ")" >]
    | MLletin (id,a1,a2) ->
	let id' = rename_bvars env [id] in
	hOV 0 [< hOV 2 [< 'sTR "let "; pr_id (List.hd id'); 'sTR " ="; 'sPC;
			  pp_expr false env [] a1; 'sPC; 'sTR "in" >];
		 'sPC;
		 pp_expr false (id'@env) [] a2 >] 
    | MLglob r -> 
	apply (P.pp_global r)
    | MLcons (_,id,[]) ->
	pr_id id
    | MLcons (_,id,[a]) ->
	[< open_par par; pr_id id; 'sPC; pp_expr true env [] a;
	   pp_expr true env [] a ; close_par par >]
    | MLcons (_,id,args') ->
	[< open_par par; pr_id id; 'sPC;
	   pp_tuple (pp_expr true env []) args'; close_par par >]
    | MLcase (t, pv) ->
      	apply
      	  [< if args<>[] then [< 'sTR"(" >]  else open_par par;
      	     v 0 [< 'sTR "match "; pp_expr false env [] t; 'sTR " with";
		    'fNL; 'sTR "  "; pp_pat env pv >] ;
	     if args<>[] then [< 'sTR")" >] else close_par par >]
    | MLfix (i,b,idl,al) ->
      	pp_fix par env (i,b,idl,al) args
    | MLexn id -> 
	[< open_par par; 'sTR "failwith"; 'sPC; 
	   'qS (string_of_id id); close_par par >]
    | MLprop ->
	string "Prop"
    | MLarity ->
	string "Arity"
    | MLcast (a,t) ->
	[< open_par true; pp_expr false env args a; 'sPC; 'sTR ":"; 'sPC; 
	   pp_type t; close_par true >]
    | MLmagic a ->
	[< open_par true; 'sTR "Obj.magic"; 'sPC; 
	   pp_expr false env args a; close_par true >]

and pp_pat env pv = 
  let pp_one_pat (name,ids,t) =
    let ids = rename_bvars env ids in
    let par = match t with
      | MLlam _  -> true
      | MLcase _ -> true
      | _        -> false 
    in
    hOV 2 [< 'sTR(string_of_id name) ;
	     begin match ids with 
		 [] -> [< >]
	       | _  -> 
      		   [< 'sTR " ";
		      pp_boxed_tuple
			(fun id -> [< 'sTR(string_of_id id) >]) 
			(List.rev ids) >]
	     end ;
	     'sTR" ->" ; 'sPC ; pp_expr par (ids@env) [] t
          >]
  in 
  [< prvect_with_sep (fun () -> [< 'fNL ; 'sTR"| " >]) pp_one_pat pv >]

and pp_fix par env (j,in_p,fid,bl) args =
  let env' = (List.rev fid) @ env in
  [< open_par par; 
     v 0 [< 'sTR"let rec " ;
	    prlist_with_sep
      	      (fun () -> [< 'fNL; 'sTR "and " >])
	      (fun (fi,ti) -> pp_function env' fi ti)
	      (List.combine fid bl) ;
	    'fNL ;
	    if in_p then 
      	      hOV 2 [< 'sTR "in "; pr_id (List.nth fid j);
                       if args <> [] then
			 [< 'sTR " "; prlist_with_sep (fun () -> [<'sTR " ">])
                              (fun s -> s) args >]
                       else [< >]
      		    >]
	    else 
	      [< >] >];
     close_par par >]

and pp_function env f t =
  let bl,t' = collect_lambda t in
  let bl = rename_bvars env bl in
  let is_function pv =
    let ktl = array_map_to_list (fun (_,l,t0) -> (List.length l,t0)) pv in
    not (List.exists (fun (k,t0) -> Mlutil.occurs (k+1) t0) ktl)
  in
  match t' with 
    | MLcase(MLrel 1,pv) ->
	if is_function pv then
	  [< 'sTR(string_of_id f) ; pr_binding (List.rev (List.tl bl)) ;
       	     'sTR" = function" ; 'fNL ;
	     v 0 [< 'sTR"  " ; pp_pat (bl@env) pv >] >]
	else
          [< 'sTR(string_of_id f) ; pr_binding (List.rev bl) ; 
             'sTR" = match " ;
	     'sTR(string_of_id (List.hd bl)) ; 'sTR" with" ; 'fNL ;
	     v 0 [< 'sTR"  " ; pp_pat (bl@env) pv >] >]
	  
    | _ -> [< 'sTR(string_of_id f) ; pr_binding (List.rev bl) ;
	      'sTR" =" ; 'fNL ; 'sTR"  " ;
	      hOV 2 (pp_expr false (bl@env) [] t') >]
	
let pp_ast a = hOV 0 (pp_expr false [] [] a)

(*s Pretty-printing of inductive types declaration. *)

let pp_parameters l = 
  [< pp_tuple (fun id -> string ("'" ^ string_of_id id)) l; space_if (l<>[]) >]

let pp_one_inductive (pl,name,cl) =
  let pp_constructor (id,l) =
    [< pr_id id;
       match l with
         | [] -> [< >] 
	 | _  -> [< 'sTR " of " ;
      	       	    prlist_with_sep 
		      (fun () -> [< 'sPC ; 'sTR "* " >]) pp_type l >] >] 
  in
  [< pp_parameters pl; pr_id name; 'sTR " ="; 'fNL; 
     v 0 [< 'sTR "    " ;
	    prlist_with_sep (fun () -> [< 'fNL ; 'sTR "  | ">])
                            (fun c -> hOV 2 (pp_constructor c)) cl >] >]

let pp_inductive il =
  [< 'sTR "type " ;
     prlist_with_sep 
       (fun () -> [< 'fNL ; 'sTR "and " >])
       (fun i -> pp_one_inductive i)
       il;
     'fNL >]

let pp_decl = function
  | Dtype i -> 
      hOV 0 (pp_inductive i)
  | Dabbrev (id, l, t) ->
      hOV 0 [< 'sTR "type"; 'sPC; pp_parameters l; 
	       pr_id id; 'sPC; 'sTR "="; 'sPC; pp_type t >]
  | Dglob (id, a) ->
      hOV 0 [< 'sTR "let"; 'sPC; pr_id id; 'sPC; 'sTR "="; 'sPC; pp_ast a >]

end
