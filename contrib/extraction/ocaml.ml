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
open Nameops
open Term
open Miniml
open Table
open Mlutil
open Options
open Nametab

let current_module = ref None

let cons_cofix = ref Refset.empty

(*s Some utility functions. *)

let rec collapse_type_app = function
  | (Tapp l1) :: l2 -> collapse_type_app (l1 @ l2)
  | l -> l

let open_par = function true -> str "(" | false -> (mt ())

let close_par = function true -> str ")" | false -> (mt ())

let pp_tvar id = 
  let s = string_of_id id in 
  if String.length s < 2 || s.[1]<>'\'' 
  then str ("'"^s)
  else str ("' "^s)

let pp_tuple f = function
  | [] -> (mt ())
  | [x] -> f x
  | l -> (str "(" ++
      	    prlist_with_sep (fun () -> (str "," ++ spc ())) f l ++
	    str ")")

let pp_boxed_tuple f = function
  | [] -> (mt ())
  | [x] -> f x
  | l -> (str "(" ++
      	    hov 0 (prlist_with_sep (fun () -> (str "," ++ spc ())) f l ++
		     str ")"))

let pp_abst = function
  | [] -> (mt ())
  | l  -> (str "fun " ++
             prlist_with_sep (fun () -> (str " ")) pr_id l ++
             str " ->" ++ spc ())

let pr_binding = function
  | [] -> (mt ())
  | l  -> (str " " ++ prlist_with_sep (fun () -> (str " ")) pr_id l)

let space_if = function true -> (str " ") | false -> (mt ())

let sec_space_if = function true -> (spc ()) | false -> (mt ())

(*s Generic renaming issues. *)

let rec rename_id id avoid = 
  if Idset.mem id avoid then rename_id (lift_ident id) avoid else id

let lowercase_id id = id_of_string (String.uncapitalize (string_of_id id))
let uppercase_id id = id_of_string (String.capitalize (string_of_id id))

(*s de Bruijn environments for programs *)

type env = identifier list * Idset.t

let rec rename_vars avoid = function
  | [] -> 
      [], avoid
  | id :: idl when id == dummy_name ->
      (* we don't rename dummy binders *)
      let (idl', avoid') = rename_vars avoid idl in
      (id :: idl', avoid')
  | id :: idl ->
      let (idl, avoid) = rename_vars avoid idl in
      let id = rename_id (lowercase_id id) avoid in
      (id :: idl, Idset.add id avoid)

let rename_tvars avoid l = 
  let rec rename avoid = function 
    | [] -> [],avoid 
    | id :: idl -> 
	let id = rename_id (lowercase_id id) avoid in 
	let idl, avoid = rename (Idset.add id avoid) idl in 
	(id :: idl, avoid) in
  fst (rename avoid l)

let push_vars ids (db,avoid) =
  let ids',avoid' = rename_vars avoid ids in
  ids', (ids' @ db, avoid')

let get_db_name n (db,_) = List.nth db (pred n)

(*s Ocaml renaming issues. *)

let keywords =     
  List.fold_right (fun s -> Idset.add (id_of_string s))
  [ "and"; "as"; "assert"; "begin"; "class"; "constraint"; "do";
    "done"; "downto"; "else"; "end"; "exception"; "external"; "false";
    "for"; "fun"; "function"; "functor"; "if"; "in"; "include";
    "inherit"; "initializer"; "lazy"; "let"; "match"; "method";
    "module"; "mutable"; "new"; "object"; "of"; "open"; "or";
    "parser"; "private"; "rec"; "sig"; "struct"; "then"; "to"; "true";
    "try"; "type"; "val"; "virtual"; "when"; "while"; "with"; "mod";
    "land"; "lor"; "lxor"; "lsl"; "lsr"; "asr" ; "unit" ; "_" ; "__" ] 
  Idset.empty

let preamble _ used_modules print_dummy = 
  Idset.fold (fun m s -> s ++ str "open " ++ pr_id (uppercase_id m) ++ fnl())
    used_modules (mt ())
  ++ 
  (if Idset.is_empty used_modules  then mt () else fnl ())
  ++
  (if print_dummy then 
     str "let (__:unit) = let rec f _ = Obj.magic f in Obj.magic f" 
     ++ fnl () ++ fnl()
   else mt ())

(*s The pretty-printing functor. *)

module Make = functor(P : Mlpp_param) -> struct

let pp_type_global r = P.pp_global r false (Some (P.globals()))
let pp_global r env = P.pp_global r false (Some (snd env))
let pp_global' r = P.pp_global r false None
let rename_global r = P.rename_global r false 

let empty_env () = [], P.globals()

(*s Pretty-printing of types. [par] is a boolean indicating whether parentheses
    are needed or not. *)

let rec pp_type par vl t =
  let rec pp_rec par = function
    | Tvar i -> (try pp_tvar (List.nth vl (pred i)) 
		 with _ -> (str "'a" ++ int i))
    | Tapp l ->
	(match collapse_type_app l with
	   | [] -> assert false
	   | [t] -> pp_rec par t
	   | [t;u] -> pp_rec true u ++ spc () ++ pp_rec false t 
	   | t::l -> (pp_tuple (pp_rec false) l ++ spc () ++  
		      pp_rec false t))
    | Tarr (t1,t2) ->
	(open_par par ++ pp_rec true t1 ++ spc () ++ str "->" ++ spc () ++ 
	   pp_rec false t2 ++ close_par par)
    | Tglob r -> pp_type_global r
    | Tdummy -> str "unit"
    | Tunknown -> str "Obj.t"
  in 
  hov 0 (pp_rec par t)

(*s Pretty-printing of expressions. [par] indicates whether
    parentheses are needed or not. [env] is the list of names for the
    de Bruijn variables. [args] is the list of collected arguments
    (already pretty-printed). *)

let expr_needs_par = function
  | MLlam _  -> true
  | MLcase (_,[|_|]) -> false 
  | MLcase _ -> true
  | _        -> false 

let rec pp_expr par env args = 
  let par' = args <> [] || par in 
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
	apply (open_par par' ++ st ++ close_par par')
    | MLletin (id,a1,a2) ->
	let i,env' = push_vars [id] env in
	let par2 = not par' && expr_needs_par a2 in
	apply 
	  (hv 0 
	     (hv 0 (open_par par' ++
		    hov 2 
		      (str "let " ++ pr_id (List.hd i) ++ str " =" ++ spc ()
			++ pp_expr false env [] a1) ++ 
		    spc () ++ str "in") ++ 
	      spc () ++ hov 0 (pp_expr par2 env' [] a2) ++ close_par par'))
    | MLglob r -> 
	apply (pp_global r env )
    | MLcons (r,[]) ->
	assert (args=[]);
	if Refset.mem r !cons_cofix then 
	  (open_par par ++ str "lazy " ++ pp_global r env ++ close_par par)
	else pp_global r env
    | MLcons (r,[a]) ->
	assert (args=[]);
	if Refset.mem r !cons_cofix then 
	  (open_par par ++ str "lazy (" ++
	   pp_global r env ++ spc () ++
	   pp_expr true env [] a ++ str ")" ++ close_par par)
	else
	  (open_par par ++ pp_global r env ++ spc () ++
	   pp_expr true env [] a ++ close_par par)
    | MLcons (r,args') ->
	assert (args=[]);
	if Refset.mem r !cons_cofix then 
	  (open_par par ++ str "lazy (" ++ pp_global r env ++ spc () ++
	   pp_tuple (pp_expr true env []) args' ++ str ")" ++ close_par par)
	else
	  (open_par par ++ pp_global r env ++ spc () ++
	   pp_tuple (pp_expr true env []) args' ++ close_par par)
    | MLcase (t,[|(r,_,_) as x|])->
	let expr = if Refset.mem r !cons_cofix then 
	  (str "Lazy.force" ++ spc () ++ pp_expr true env [] t)
	else 
	  (pp_expr false env [] t) 
	in 
	let s1,s2 = pp_one_pat env x in 
	apply 
	  (hv 0 
	     (hv 0 (open_par par' ++ 
		    hov 2 (str "let " ++ s1 ++ str " =" ++ spc () ++ expr) ++ 
		    spc () ++ str "in") ++ 
	      spc () ++ hov 0 s2 ++ close_par par'))
    | MLcase (t, pv) ->
	let r,_,_ = pv.(0) in 
	let expr = if Refset.mem r !cons_cofix then 
	  (str "Lazy.force" ++ spc () ++ pp_expr true env [] t)
	else 
	  (pp_expr false env [] t) 	
	in apply
      	     (open_par par' ++
      	      v 0 (str "match " ++ expr ++ str " with" ++
		   fnl () ++ str "  | " ++ pp_pat env pv) ++
	      close_par par')
    | MLfix (i,ids,defs) ->
	let ids',env' = push_vars (List.rev (Array.to_list ids)) env in
      	pp_fix par env' (Some i) (Array.of_list (List.rev ids'),defs) args
    | MLexn s -> 
	(* An [MLexn] may be applied, but I don't really care. *)
	(open_par par ++ str "assert false" ++ spc () ++ 
	 str ("(* "^s^" *)") ++ close_par par)
    | MLdummy ->
	str "()" (* An [MLdummy] may be applied, but I don't really care. *)
    | MLdummy' -> 
	str "__" (* idem *)
    | MLcast (a,t) ->
	(open_par true ++ pp_expr false env args a ++ spc () ++ str ":" ++ 
	 spc () ++ pp_type false [] t ++ close_par true)
    | MLmagic a ->
	(open_par true ++ str "Obj.magic" ++ spc () ++ 
	 pp_expr false env args a ++ close_par true)

and pp_one_pat env (r,ids,t) = 
  let ids,env' = push_vars (List.rev ids) env in
  let par = expr_needs_par t in
  let args = 
    if ids = [] then (mt ()) 
    else str " " ++ pp_boxed_tuple pr_id (List.rev ids) in 
  (pp_global r env ++ args), (pp_expr par env' [] t)
  
and pp_pat env pv = 
  prvect_with_sep (fun () -> (fnl () ++ str "  | ")) 
    (fun x -> let s1,s2 = pp_one_pat env x in 
     hov 2 (s1 ++ str " ->" ++ spc () ++ s2)) pv

(*s names of the functions ([ids]) are already pushed in [env],
    and passed here just for convenience. *)

and pp_fix par env in_p (ids,bl) args =
  (open_par par ++ 
     v 0 (str "let rec " ++
	    prvect_with_sep
      	      (fun () -> (fnl () ++ str "and "))
	      (fun (fi,ti) -> pp_function env (pr_id fi) ti)
	      (array_map2 (fun id b -> (id,b)) ids bl) ++
	    fnl () ++
	    match in_p with
	      | Some j -> 
      		  hov 2 (str "in " ++ pr_id (ids.(j)) ++
			   if args <> [] then
			     (str " " ++ 
				prlist_with_sep (fun () -> (str " "))
				  (fun s -> s) args)
			   else
			     (mt ()))
	      | None -> 
		  (mt ())) ++
     close_par par)

and pp_function env f t =
  let bl,t' = collect_lams t in
  let bl,env' = push_vars bl env in
  let is_function pv =
    let ktl = array_map_to_list (fun (_,l,t0) -> (List.length l,t0)) pv in
    not (List.exists (fun (k,t0) -> Mlutil.occurs (k+1) t0) ktl)
  in
  let is_not_cofix pv = let (r,_,_) = pv.(0) in not (Refset.mem r !cons_cofix) 
  in					  
  match t' with 
    | MLcase(MLrel 1,pv) when is_not_cofix pv ->
	if is_function pv then
	  (f ++ pr_binding (List.rev (List.tl bl)) ++
       	     str " = function" ++ fnl () ++
	     v 0 (str "  | " ++ pp_pat env' pv))
	else
          (f ++ pr_binding (List.rev bl) ++ 
             str " = match " ++
	     pr_id (List.hd bl) ++ str " with" ++ fnl () ++
	     v 0 (str "  | " ++ pp_pat env' pv))
	  
    | _ -> (f ++ pr_binding (List.rev bl) ++
	      str " =" ++ fnl () ++ str "  " ++
	      hov 2 (pp_expr false env' [] t'))
	
(*s Pretty-printing of inductive types declaration. *)

let pp_parameters l = 
  (pp_boxed_tuple pp_tvar l ++ space_if (l<>[]))

let pp_one_ind prefix (pl,name,cl) =
  let pl = rename_tvars keywords pl in
  let pp_constructor (id,l) =
    (pp_global' id ++
     match l with
       | [] -> (mt ()) 
       | _  -> (str " of " ++
      		prlist_with_sep 
		  (fun () -> (spc () ++ str "* ")) 
		  (pp_type true (List.rev pl)) l))
  in
  (pp_parameters pl ++ str prefix ++ pp_type_global name ++ str " =" ++ 
   if cl = [] then str " unit (* empty inductive *)" 
   else (fnl () ++
	 v 0 (str "  | " ++
	      prlist_with_sep (fun () -> (fnl () ++ str "  | "))
                (fun c -> hov 2 (pp_constructor c)) cl)))

let pp_ind il =
  (str "type " ++
   prlist_with_sep (fun () -> (fnl () ++ str "and ")) (pp_one_ind "") il
   ++ fnl ())

let pp_coind_preamble (pl,name,_) = 
  let pl = rename_tvars keywords pl in
  (pp_parameters pl ++ pp_type_global name ++ str " = " ++ 
    pp_parameters pl ++ str "__" ++ pp_type_global name ++ str " Lazy.t")

let pp_coind il = 
  (str "type " ++ 
   prlist_with_sep (fun () -> (fnl () ++ str "and ")) pp_coind_preamble il ++
   fnl () ++ str "and " ++ 
   prlist_with_sep (fun () -> (fnl () ++ str "and ")) (pp_one_ind "__") il ++
   fnl ())

(*s Pretty-printing of a declaration. *)

let pp_decl = function
  | Dind ([], _) -> mt ()
  | Dind (i, cofix) -> 
      if cofix then begin
	List.iter   
	  (fun (_,_,l) -> 
	     List.iter (fun (r,_) -> 
			  cons_cofix := Refset.add r !cons_cofix)  l) i; 
	hov 0 (pp_coind i)
      end else 
	hov 0 (pp_ind i)
  | DdummyType r -> 
      hov 0 (str "type " ++ pp_type_global r ++ str " = unit" ++ fnl ())
  | Dtype (r, l, t) ->
      let l = rename_tvars keywords l in 
      hov 0 (str "type" ++ spc () ++ pp_parameters l ++ 
	       pp_type_global r ++ spc () ++ str "=" ++ spc () ++ 
	       pp_type false (List.rev l) t ++ fnl ())
  | Dfix (rv, defs) ->
      let ids = Array.map rename_global rv in 
      let env = List.rev (Array.to_list ids), P.globals() in
      (hov 2 (pp_fix false env None (ids,defs) []))
  | Dterm (r, a) ->
      hov 0 (str "let " ++ 
	       pp_function (empty_env ()) (pp_global' r) a ++ fnl ())
  | DcustomTerm (r,s) -> 
      hov 0 (str "let " ++ pp_global' r ++ 
	       str " =" ++ spc () ++ str s ++ fnl ())
  | DcustomType (r,s) -> 
      hov 0 (str "type " ++ pp_type_global r ++ str " = " ++ str s ++ fnl ())

end

