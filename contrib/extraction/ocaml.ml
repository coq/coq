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
open Libnames
open Table
open Miniml
open Mlutil

let cons_cofix = ref Refset.empty

(*s Some utility functions. *)

let pp_par par st = if par then str "(" ++ st ++ str ")" else st

let pp_tvar id = 
  let s = string_of_id id in 
  if String.length s < 2 || s.[1]<>'\'' 
  then str ("'"^s)
  else str ("' "^s)

let pp_tuple_light f = function
  | [] -> mt ()
  | [x] -> f true x
  | l -> 
      pp_par true (prlist_with_sep (fun () -> str "," ++ spc ()) (f false) l)

let pp_tuple f = function
  | [] -> mt ()
  | [x] -> f x
  | l -> pp_par true (prlist_with_sep (fun () -> str "," ++ spc ()) f l)

let pp_boxed_tuple f = function
  | [] -> mt ()
  | [x] -> f x
  | l -> pp_par true (hov 0 (prlist_with_sep (fun () -> str "," ++ spc ()) f l))

let pp_abst = function
  | [] -> mt ()
  | l  -> 
      str "fun " ++ prlist_with_sep (fun () -> str " ") pr_id l ++ 
      str " ->" ++ spc ()

let pp_apply st par args = match args with
  | [] -> st
  | _  -> hov 2 (pp_par par (st ++ spc () ++ prlist_with_sep spc identity args))

let pr_binding = function
  | [] -> mt ()
  | l  -> str " " ++ prlist_with_sep (fun () -> str " ") pr_id l

let space_if = function true -> str " " | false -> mt ()

let sec_space_if = function true -> spc () | false -> mt ()

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

let preamble _ used_modules (mldummy,tdummy,tunknown) = 
  Idset.fold (fun m s -> str "open " ++ pr_id (uppercase_id m) ++ fnl() ++ s)
    used_modules (mt ())
  ++ 
  (if Idset.is_empty used_modules then mt () else fnl ())
  ++
  (if tdummy || tunknown then str "type __ = Obj.t" ++ fnl() else mt()) 
  ++
  (if mldummy then 
     str "let __ = let rec f _ = Obj.repr f in Obj.repr f" 
     ++ fnl ()
   else mt ()) 
  ++ 
  (if tdummy || tunknown || mldummy then fnl () else mt ())


(*s The pretty-printing functor. *)

module Make = functor(P : Mlpp_param) -> struct

let pp_global r = P.pp_global r
let empty_env () = [], P.globals()

(*s Pretty-printing of types. [par] is a boolean indicating whether parentheses
    are needed or not. *)

let rec pp_type par vl t =
  let rec pp_rec par = function
    | Tmeta _ | Tvar' _ -> assert false
    | Tvar i -> (try pp_tvar (List.nth vl (pred i)) 
		 with _ -> (str "'a" ++ int i))
    | Tglob (r,[]) -> pp_global r
    | Tglob (r,l) -> pp_tuple_light pp_rec l ++ spc () ++ pp_global r
    | Tarr (t1,t2) ->
	pp_par par 
	  (pp_rec true t1 ++ spc () ++ str "->" ++ spc () ++ pp_rec false t2)
    | Tdummy -> str "__"
    | Tunknown -> str "__"
    | Tcustom s -> str s
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
	let fl,env' = push_vars fl env in
	let st = (pp_abst (List.rev fl) ++ pp_expr false env' [] a') in
	apply (pp_par par' st)
    | MLletin (id,a1,a2) ->
	assert (args=[]); 
	let i,env' = push_vars [id] env in
	let pp_id = pr_id (List.hd i)
	and pp_a1 = pp_expr false env [] a1
	and pp_a2 = pp_expr (not par && expr_needs_par a2) env' [] a2 in 
	hv 0 
	  (pp_par par 
	     (hv 0 
		(hov 2 (str "let " ++ pp_id ++ str " =" ++ spc () ++ pp_a1) ++ 
		 spc () ++ str "in") ++ 
	      spc () ++ hov 0 pp_a2))
    | MLglob r when is_projection r && args <> [] ->
	let record = List.hd args in 
	pp_apply (record ++ str "." ++ pp_global r) par (List.tl args)
    | MLglob r -> 
	apply (pp_global r)
    | MLcons (r,[]) ->
	assert (args=[]);
	if Refset.mem r !cons_cofix then 
	  pp_par par (str "lazy " ++ pp_global r)
	else pp_global r
    | MLcons (r,args') -> 
	(try 
	   let projs = find_projections (kn_of_r r) in 
	   pp_record_pat (projs, List.map (pp_expr true env []) args')
	 with Not_found ->
	   assert (args=[]);
	   let tuple = pp_tuple (pp_expr true env []) args' in 
	   if Refset.mem r !cons_cofix then 
	     pp_par par (str "lazy (" ++ pp_global r ++ spc() ++ tuple ++str ")")
	   else pp_par par (pp_global r ++ spc () ++ tuple))
    | MLcase (t, pv) ->
	let r,_,_ = pv.(0) in 
	let expr = if Refset.mem r !cons_cofix then 
	  (str "Lazy.force" ++ spc () ++ pp_expr true env [] t)
	else 
	  (pp_expr false env [] t) 
	in 
	let record = 
	  try ignore (find_projections (kn_of_r r)); true with Not_found -> false
	in 
	if Array.length pv = 1 && not record then 
	  let s1,s2 = pp_one_pat env pv.(0) in 
	  apply 
	    (hv 0 
	       (pp_par par' 
		  (hv 0 
		     (hov 2 (str "let " ++ s1 ++ str " =" ++ spc () ++ expr) 
		      ++ spc () ++ str "in") ++ 
		   spc () ++ hov 0 s2)))
	else
	  apply
      	    (pp_par par' 
      	       (v 0 (str "match " ++ expr ++ str " with" ++
		     fnl () ++ str "  | " ++ pp_pat env pv)))
    | MLfix (i,ids,defs) ->
	let ids',env' = push_vars (List.rev (Array.to_list ids)) env in
      	pp_fix par env' i (Array.of_list (List.rev ids'),defs) args
    | MLexn s -> 
	(* An [MLexn] may be applied, but I don't really care. *)
	pp_par par (str "assert false" ++ spc () ++ str ("(* "^s^" *)"))
    | MLdummy ->
	str "__" (* An [MLdummy] may be applied, but I don't really care. *)
    | MLcast (a,t) ->
	apply (pp_par true 
		 (pp_expr true env [] a ++ spc () ++ str ":" ++ 
		  spc () ++ pp_type true [] t))
    | MLmagic a ->
	pp_apply (str "Obj.magic") par (pp_expr true env [] a :: args)
    | MLcustom s -> str s
	  
and pp_record_pat (projs, args) =
   str "{ " ++
   prlist_with_sep (fun () -> str ";" ++ spc ()) 
     (fun (r,a) -> pp_global r ++ str " =" ++ spc () ++ a)
     (List.combine projs args) ++
   str " }"

and pp_one_pat env (r,ids,t) = 
  let ids,env' = push_vars (List.rev ids) env in
  let expr = pp_expr (expr_needs_par t) env' [] t in 
  try 
    let projs = find_projections (kn_of_r r) in 
    pp_record_pat (projs, List.rev_map pr_id ids), expr
  with Not_found -> 
    let args = 
      if ids = [] then (mt ()) 
      else str " " ++ pp_boxed_tuple pr_id (List.rev ids) in 
    pp_global r ++ args, expr
  
and pp_pat env pv = 
  prvect_with_sep (fun () -> (fnl () ++ str "  | ")) 
    (fun x -> let s1,s2 = pp_one_pat env x in 
     hov 2 (s1 ++ str " ->" ++ spc () ++ s2)) pv

and pp_function env f t =
  let bl,t' = collect_lams t in
  let bl,env' = push_vars bl env in
  let is_function pv =
    let ktl = array_map_to_list (fun (_,l,t0) -> (List.length l,t0)) pv in
    not (List.exists (fun (k,t0) -> ast_occurs (k+1) t0) ktl)
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

(*s names of the functions ([ids]) are already pushed in [env],
    and passed here just for convenience. *)

and pp_fix par env i (ids,bl) args =
  pp_par par 
    (v 0 (str "let rec " ++
	  prvect_with_sep
      	    (fun () -> fnl () ++ str "and ")
	    (fun (fi,ti) -> pp_function env (pr_id fi) ti)
	    (array_map2 (fun id b -> (id,b)) ids bl) ++
	  fnl () ++
	  hov 2 (str "in " ++ pp_apply (pr_id ids.(i)) false args)))

let pp_val e typ = 
  str "(** val " ++ e ++ str " : " ++ pp_type false [] typ ++ 
  str " **)"  ++ fnl () ++ fnl ()

(*s Pretty-printing of [Dfix] *)

let pp_Dfix env (p,c,t) = 
  let init = 
    pp_val p.(0) t.(0) ++ str "let rec " ++ pp_function env p.(0) c.(0) ++ fnl ()
  in
  iterate_for 1 (Array.length p - 1) 
    (fun i acc -> acc ++ fnl () ++ 
       pp_val p.(i) t.(i) ++ str "and " ++ pp_function env p.(i) c.(i) ++ fnl ())
    init 
	
(*s Pretty-printing of inductive types declaration. *)

let pp_parameters l = 
  (pp_boxed_tuple pp_tvar l ++ space_if (l<>[]))

let pp_one_ind prefix ip pl cv =
  let pl = rename_tvars keywords pl in
  let pp_constructor (r,l) =
    hov 2 (str "  | " ++ pp_global r ++
	   match l with
	     | [] -> mt () 
	     | _  -> (str " of " ++ 
		      prlist_with_sep 
			(fun () -> spc () ++ str "* ") (pp_type true pl) l))
  in
  pp_parameters pl ++ str prefix ++ pp_global (IndRef ip) ++ str " =" ++ 
  if cv = [||] then str " unit (* empty inductive *)" 
  else fnl () ++ v 0 (prvect_with_sep fnl pp_constructor
			(Array.mapi (fun i c -> ConstructRef (ip,i+1), c) cv))

let pp_comment s = str "(* " ++ s ++ str " *)" ++ fnl ()

let pp_logical_ind ip packet = 
  pp_comment (Printer.pr_global (IndRef ip) ++ str " : logical inductive") ++
  pp_comment (str "with constructors : " ++ 
	      prvect_with_sep spc Printer.pr_global 
		(Array.mapi (fun i _ -> ConstructRef (ip,i+1)) packet.ip_types)) 
    
let pp_singleton kn packet = 
  let l = rename_tvars keywords packet.ip_vars in 
  hov 0 (str "type " ++ spc () ++ pp_parameters l ++
	 pp_global (IndRef (kn,0)) ++ spc () ++ str "=" ++ spc () ++
	 pp_type false l (List.hd packet.ip_types.(0)) ++ fnl () ++
	 pp_comment (str "singleton inductive, whose constructor was " ++ 
		     Printer.pr_global (ConstructRef ((kn,0),1))))

let pp_record kn packet = 
  let l = List.combine (find_projections kn) packet.ip_types.(0) in 
  let projs = find_projections kn in
  let pl = rename_tvars keywords packet.ip_vars in 
  str "type " ++ pp_parameters pl ++ pp_global (IndRef (kn,0)) ++ str " = { "++
  hov 0 (prlist_with_sep (fun () -> str ";" ++ spc ()) 
	   (fun (r,t) -> pp_global r ++ str " : " ++ pp_type true pl t) l) 
  ++ str " }" ++ fnl () 

let pp_coind ip pl = 
  let r = IndRef ip in 
  let pl = rename_tvars keywords pl in
  pp_parameters pl ++ pp_global r ++ str " = " ++ 
  pp_parameters pl ++ str "__" ++ pp_global r ++ str " Lazy.t"

let rec pp_ind co first kn i ind =
  if i >= Array.length ind.ind_packets then mt () 
  else 
    let ip = (kn,i) in 
    let p = ind.ind_packets.(i) in 
    if p.ip_logical then  
      pp_logical_ind ip p ++ pp_ind co first kn (i+1) ind
    else 
      str (if first then "type " else "and ") ++
      (if co then pp_coind ip p.ip_vars ++ fnl () ++ str "and " else mt ()) ++ 
      pp_one_ind (if co then "__" else "") ip p.ip_vars p.ip_types ++
      fnl () ++ pp_ind co false kn (i+1) ind

(*s Pretty-printing of a declaration. *)

let pp_decl = function
  | Dind (kn,i) as d -> 
      (match i.ind_info with 
	 | Singleton -> pp_singleton kn i.ind_packets.(0) 
	 | Record -> pp_record kn i.ind_packets.(0)
	 | Coinductive -> 
	     let nop _ = () 
	     and add r = cons_cofix := Refset.add r !cons_cofix in 
	     decl_iter_references nop add nop d; 
	     hov 0 (pp_ind true true kn 0 i)
	 | Standard -> 
	     hov 0 (pp_ind false true kn 0 i))
  | Dtype (r, l, t) ->
      let l = rename_tvars keywords l in 
      hov 0 (str "type" ++ spc () ++ pp_parameters l ++ 
	       pp_global r ++ spc () ++ str "=" ++ spc () ++ 
	       pp_type false l t ++ fnl ())
  | Dfix (rv, defs, typs) ->
      (* We compute renamings of [rv] before asking [empty_env ()]... *)
      let ppv = Array.map pp_global rv in 
      hov 0 (pp_Dfix (empty_env ()) (ppv,defs,typs))
  | Dterm (r, a, t) when is_projection r -> 
      let e = pp_global r in 
      (pp_val e t ++ 
       hov 0 (str "let " ++ e ++ str " x = x." ++ e ++ fnl())) 
  | Dterm (r, a, t) ->
      let e = pp_global r in 
      (pp_val e t ++ 
       hov 0 (str "let " ++ pp_function (empty_env ()) e a ++ fnl ()))
  | DcustomTerm (r,s) -> 
      hov 0 (str "let " ++ pp_global r ++ 
	     str " =" ++ spc () ++ str s ++ fnl ())
  | DcustomType (r,s) -> 
      hov 0 (str "type " ++ pp_global r ++ str " = " ++ str s ++ fnl ())

end

