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
open Nameops
open Term
open Miniml
open Mlutil
open Options
open Ocaml
open Nametab

(*s Haskell renaming issues. *)

let keywords =     
  List.fold_right (fun s -> Idset.add (id_of_string s))
  [ "case"; "class"; "data"; "default"; "deriving"; "do"; "else";
    "if"; "import"; "in"; "infix"; "infixl"; "infixr"; "instance"; 
    "let"; "module"; "newtype"; "of"; "then"; "type"; "where"; "_"; "__";
    "as"; "qualified"; "hiding" ; "unit" ]
  Idset.empty

let preamble prm used_modules print_dummy =
  let m = String.capitalize (string_of_id prm.mod_name)   in 
  str "module " ++ str m ++ str " where" ++ fnl () ++ fnl() ++ 
  str "import qualified Prelude" ++ fnl() ++
  Idset.fold 
    (fun m s -> 
       s ++ str "import qualified " ++ pr_id (uppercase_id m) ++ fnl())
    used_modules (mt ()) ++ fnl()
  ++
  (if print_dummy then 
     str "__ = Prelude.error \"Logical or arity value used\"" 
     ++ fnl () ++ fnl()
   else mt())

let pp_abst = function
  | [] -> (mt ())
  | l  -> (str "\\" ++
             prlist_with_sep (fun () -> (str " ")) pr_id l ++
             str " ->" ++ spc ())

(*s The pretty-printing functor. *)

module Make = functor(P : Mlpp_param) -> struct

let pp_type_global r = P.pp_global r true None
let pp_global r = P.pp_global r false None

let rename_global r = P.rename_global r false

let pr_lower_id id = pr_id (lowercase_id id)

let empty_env () = [], P.globals()

(*s Pretty-printing of types. [par] is a boolean indicating whether parentheses
    are needed or not. *)

let rec pp_type par vl t =
  let rec pp_rec par = function
    | Tvar i -> (try pr_id (List.nth vl (pred i)) with _ -> (str "a" ++ int i))
    | Tapp l ->
	(match collapse_type_app l with
	   | [] -> assert false
	   | [t] -> pp_rec par t
	   | t::l -> 
	       (open_par par ++
		  pp_rec false t ++ spc () ++
		  prlist_with_sep (fun () -> (spc ())) (pp_type true vl) l ++ 
		  close_par par))
    | Tarr (t1,t2) ->
	(open_par par ++ pp_rec true t1 ++ spc () ++ str "->" ++ spc () ++ 
	   pp_rec false t2 ++ close_par par)
    | Tglob r -> pp_type_global r
    | Tdummy -> str "()"
    | Tunknown -> str "()"
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
  let apply st = match args with
    | [] -> st
    | _  -> hov 2 (open_par par ++ st ++ spc () ++
                     prlist_with_sep (fun () -> (spc ())) (fun s -> s) args ++
                     close_par par) 
  in
  function
    | MLrel n -> 
	let id = get_db_name n env in apply (pr_id id)
    | MLapp (f,args') ->
	let stl = List.map (pp_expr true env []) args' in
        pp_expr par env (stl @ args) f
    | MLlam _ as a -> 
      	let fl,a' = collect_lams a in
	let fl,env' = push_vars fl env in
	let st = (pp_abst (List.rev fl) ++ pp_expr false env' [] a') in
	if args = [] then
          (open_par par ++ st ++ close_par par)
        else
          apply (str "(" ++ st ++ str ")")
    | MLletin (id,a1,a2) ->
	let i,env' = push_vars [id] env in
	let par' = par || args <> [] in
	let par2 = not par' && expr_needs_par a2 in
	apply 
	  (hv 0 
	     (hv 0 (open_par par' ++
		    hov 2 (str "let" ++ spc () ++ pr_id (List.hd i) ++ 
			   str " = " ++ pp_expr false env [] a1) ++ 
		    spc () ++ str "in") ++
	      spc () ++ hov 0 (pp_expr par2 env' [] a2) ++ close_par par'))
    | MLglob r -> 
	apply (pp_global r)
    | MLcons (r,[]) ->
	assert (args=[]); pp_global r
    | MLcons (r,[a]) ->
	assert (args=[]);
	(open_par par ++ pp_global r ++ spc () ++
	   pp_expr true env [] a ++ close_par par)
    | MLcons (r,args') ->
	assert (args=[]);
	(open_par par ++ pp_global r ++ spc () ++
	   prlist_with_sep (fun () -> (spc ())) (pp_expr true env []) args' ++
	   close_par par)
    | MLcase (t, pv) ->
      	apply
      	  (if args <> [] then (str "(")  else open_par par ++
      	     v 0 (str "case " ++ pp_expr false env [] t ++ str " of" ++
		    fnl () ++ str "  " ++ pp_pat env pv) ++
	     if args <> [] then (str ")") else close_par par)
    | MLfix (i,ids,defs) ->
	let ids',env' = push_vars (List.rev (Array.to_list ids)) env in
      	pp_fix par env' (Some i) (Array.of_list (List.rev ids'),defs) args
    | MLexn s -> 
	(* An [MLexn] may be applied, but I don't really care. *)
	(open_par par ++ str "Prelude.error" ++ spc () ++ 
	 qs s ++ close_par par)
    | MLdummy | MLdummy' ->
	str "__" (* An [MLdummy] may be applied, but I don't really care. *)
    | MLcast (a,t) -> pp_expr par env args a
    | MLmagic a ->  pp_expr par env args a

and pp_pat env pv = 
  let pp_one_pat (name,ids,t) =
    let ids,env' = push_vars (List.rev ids) env in
    let par = expr_needs_par t in
    hov 2 (pp_global name ++
	     begin match ids with 
	       | [] -> (mt ())
	       | _  -> (str " " ++ 
			  prlist_with_sep 
			    (fun () -> (spc ())) pr_id (List.rev ids))
	     end ++
	     str " ->" ++ spc () ++ pp_expr par env' [] t)
  in 
  (prvect_with_sep (fun () -> (fnl () ++ str "  ")) pp_one_pat pv)

(*s names of the functions ([ids]) are already pushed in [env],
    and passed here just for convenience. *)

and pp_fix par env in_p (ids,bl) args =
  (open_par par ++ 
   v 0  
     (v 2 (str "let" ++ fnl () ++
	   prvect_with_sep fnl 
	  (fun (fi,ti) -> pp_function env (pr_id fi) ti) 
	     (array_map2 (fun a b -> a,b) ids bl)) ++ 
      fnl () ++ 
      (match in_p with
	 | Some j -> 
      	     hov 2 (str "in " ++ pr_id ids.(j) ++
		    if args <> [] then
		      (str " " ++ 
		       prlist_with_sep (fun () -> (str " "))
		      (fun s -> s) args)
		    else
		      (mt ()))
	 | None -> 
	     (mt ()))) ++
   close_par par)

and pp_function env f t =
  let bl,t' = collect_lams t in
  let bl,env' = push_vars bl env in
  (f ++ pr_binding (List.rev bl) ++
     str " =" ++ fnl () ++ str "  " ++
     hov 2 (pp_expr false env' [] t'))
	
let pp_ast a = hov 0 (pp_expr false (empty_env ()) [] a)

(*s Pretty-printing of inductive types declaration. *)

let pp_one_inductive (pl,name,cl) =
  let pl = rename_tvars keywords pl in
  let pp_constructor (id,l) =
    (pp_global id ++
     match l with
       | [] -> (mt ()) 
       | _  -> (str " " ++
      	       	prlist_with_sep 
		  (fun () -> (str " ")) (pp_type true (List.rev pl)) l))
  in
  (str (if cl = [] then "type " else "data ") ++ 
   pp_type_global name ++ str " " ++
   prlist_with_sep (fun () -> (str " ")) pr_lower_id pl ++
   (if pl = [] then (mt ()) else (str " ")) ++
   if cl = [] then str "= () -- empty inductive"
   else 
      (v 0 (str "= " ++
	    prlist_with_sep (fun () -> (fnl () ++ str "  | "))
              pp_constructor cl)))
  
let pp_inductive il =
  (prlist_with_sep (fun () -> (fnl ())) pp_one_inductive il ++ fnl ())

(*s Pretty-printing of a declaration. *)

let pp_decl = function
  | Dtype ([], _) -> mt ()
  | Dtype (i, _) -> 
      hov 0 (pp_inductive i)
  | Dabbrev (r, l, t) ->
      let l = rename_tvars keywords l in
      let l' = List.rev l in 
      hov 0 (str "type " ++ pp_type_global r ++ spc () ++ 
	       prlist_with_sep (fun () -> (str " ")) pr_id l ++
	       (if l <> [] then (str " ") else (mt ())) ++ str "=" ++ spc () ++
	       pp_type false l' t ++ fnl ())
  | Dfix (rv, defs) ->
      let ids = List.map rename_global (Array.to_list rv) in 
      let env = List.rev ids, P.globals() in
      (prlist_with_sep (fun () -> fnl () ++ fnl ()) 
	   (fun (fi,ti) -> pp_function env (pr_id fi) ti)
	   (List.combine ids (Array.to_list defs)) ++ fnl ())
  | Dglob (r, a) ->
      hov 0 (pp_function (empty_env ()) (pp_global r) a ++ fnl ())
  | Dcustom (r,s) -> 
      hov 0  (pp_global r ++ str " =" ++ spc () ++ str s ++ fnl ())

let pp_type = pp_type false []

end

