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

let rec collapse_type_app = function
  | (Tapp l1) :: l2 -> collapse_type_app (l1 @ l2)
  | l -> l

let space_if = function true -> [< 'sTR " " >] | false -> [< >]

let sec_space_if = function true -> [< 'sPC >] | false -> [< >]

(*s Haskell renaming issues. *)

let haskell_keywords =     
  List.fold_right (fun s -> Idset.add (id_of_string s))
  [ "case"; "class"; "data"; "default"; "deriving"; "do"; "else";
    "if"; "import"; "in"; "infix"; "infixl"; "infixr"; "instance"; 
    "let"; "module"; "newtype"; "of"; "then"; "type"; "where"; "_";
    "as"; "qualified"; "hiding" ]
  Idset.empty

let current_ids = ref haskell_keywords

let rec rename_id id avoid = 
  if Idset.mem id avoid then rename_id (lift_ident id) avoid else id

let rename_global id = 
  let id' = rename_id id !current_ids in
  current_ids := Idset.add id' !current_ids; 
  id'

let lowercase_id id = id_of_string (String.uncapitalize (string_of_id id))
let uppercase_id id = id_of_string (String.capitalize (string_of_id id))

let rename_lower_global id = rename_global (lowercase_id id)
let rename_upper_global id = rename_global (uppercase_id id)

let pr_lower_id id = pr_id (lowercase_id id)

(*s de Bruijn environments for programs *)

type env = identifier list * Idset.t

let rec rename_vars avoid = function
  | [] -> 
      [], avoid
  | id :: idl when id == prop_name ->
      (* we don't rename propositions binders *)
      let (idl', avoid') = rename_vars avoid idl in
      (id :: idl', avoid')
  | id :: idl ->
      let id' = rename_id (lowercase_id id) avoid in
      let (idl', avoid') = rename_vars (Idset.add id' avoid) idl in
      (id' :: idl', avoid')

let push_vars ids (db,avoid) =
  let ids',avoid' = rename_vars avoid ids in
  ids', (ids' @ db, avoid')

let empty_env () = ([], !current_ids)

let get_db_name n (db,_) = List.nth db (pred n)

(*s [collect_lambda MLlam(id1,...MLlam(idn,t)...)] returns
    the list [id1;...;idn] and the term [t]. *)

let collect_lambda = 
  let rec collect acc = function
    | MLlam(id,t) -> collect (id::acc) t
    | x           -> acc,x
  in 
  collect []

let abst = function
  | [] -> [< >]
  | l  -> [< 'sTR "\\ ";
             prlist_with_sep (fun  ()-> [< 'sTR " " >]) pr_id l;
             'sTR " ->"; 'sPC >]

let pr_binding = function
  | [] -> [< >]
  | l  -> [< 'sTR " "; prlist_with_sep (fun () -> [< 'sTR " " >]) pr_id l >]

(*s The pretty-printing functor. *)

module Make = functor(P : Mlpp_param) -> struct

let pp_reference f r = 
  try let s = find_ml_extraction r in [< 'sTR s >]
  with Not_found -> f r
 
let pp_type_global = pp_reference P.pp_type_global
let pp_global = pp_reference P.pp_global

(*s Pretty-printing of types. [par] is a boolean indicating whether parentheses
    are needed or not. *)

let rec pp_type par t =
  let rec pp_rec par = function
    | Tvar id -> 
	pr_id (lowercase_id id) (* TODO: possible clash with Haskell kw *)
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
      	let fl,a' = collect_lambda a in
	let fl,env' = push_vars fl env in
	let st = [< abst (List.rev fl); pp_expr false env' [] a' >] in
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
    | MLexn id -> 
	[< open_par par; 'sTR "error"; 'sPC; 
	   'qS (string_of_id id); close_par par >]
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
  if pv = [||] then
    [< 'sTR "_ -> error \"shouldn't happen\" -- empty inductive" >]
  else
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
  let bl,t' = collect_lambda t in
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
	 let id = P.rename_global r in
	 let idi = List.nth (List.rev ids') i in
	 if id <> idi then
	   [< 'fNL; pr_id id; 'sTR " = "; pr_id idi; 'fNL >]
	 else
	   [< >] >]
  | Dglob (r, a) ->
      hOV 0 [< pp_function (empty_env ()) (pp_global r) a; 'fNL >]

let pp_type = pp_type false

end

(*s Renaming issues for a monolithic extraction. *)

module MonoParams = struct

let renamings = Hashtbl.create 97

let cache r f = 
  try Hashtbl.find renamings r 
  with Not_found -> let id = f r in Hashtbl.add renamings r id; id

let rename_type_global r =  
  cache r
    (fun r -> 
       let id = Environ.id_of_global (Global.env()) r in
       rename_upper_global id)

let pp_type_global r = pr_id (rename_type_global r)

let rename_global r = 
  cache r
    (fun r -> 
       let id = Environ.id_of_global (Global.env()) r in
       match r with
	 | ConstructRef _ -> rename_upper_global id
	 | _ -> rename_lower_global id)

let pp_global r = pr_id (rename_global r)

let cofix_warning = true

end

module MonoPp = Make(MonoParams)

(*s Renaming issues in a modular extraction. *)

module ModularParams = struct

  let avoid = 
    Idset.add (id_of_string "prop")
      (Idset.add (id_of_string "arity") haskell_keywords)

  let rename_lower id = 
    if Idset.mem id avoid || id <> lowercase_id id then 
      "coq_" ^ string_of_id id 
    else 
      string_of_id id

  let rename_upper id = 
    if Idset.mem id avoid || id <> uppercase_id id then 
      "Coq_" ^ string_of_id id 
    else 
      string_of_id id

  let id_of_global r s =
    let sp = match r with
      | ConstRef sp -> sp
      | IndRef (sp,_) -> sp
      | ConstructRef ((sp,_),_) -> sp
      | _ -> assert false
    in
    let m = list_last (dirpath sp) in
    id_of_string 
      (if Some m = !current_module then s
      else (String.capitalize (string_of_id m)) ^ "." ^ s)

  let rename_type_global r = 
    let id = Environ.id_of_global (Global.env()) r in 
    id_of_global r (rename_upper id)

  let rename_global r = 
    let id = Environ.id_of_global (Global.env()) r in 
    match r with
      | ConstructRef _ -> id_of_global r (rename_upper id)
      | _ -> id_of_global r (rename_lower id)

  let pp_type_global r = pr_id (rename_type_global r)
  let pp_global r = pr_id (rename_global r)

  let cofix_warning = true
end

module ModularPp = Make(ModularParams)

(*s Extraction to a file. *)

let haskell_preamble prm =
  let m = if prm.modular then String.capitalize prm.module_name else "Main" in
  [< 'sTR "module "; 'sTR m; 'sTR " where"; 'fNL; 'fNL;
     'sTR "type Prop = ()"; 'fNL;
     'sTR "prop = ()"; 'fNL; 'fNL;
     'sTR "type Arity = ()"; 'fNL;
     'sTR "arity = ()"; 'fNL; 'fNL >]

let extract_to_file f prm decls =
  let pp_decl = if prm.modular then ModularPp.pp_decl else MonoPp.pp_decl in
  let cout = open_out f in
  let ft = Pp_control.with_output_to cout in
  pP_with ft (hV 0 (haskell_preamble prm));
  begin 
    try
      List.iter (fun d -> mSGNL_with ft (pp_decl d)) decls
    with e ->
      pp_flush_with ft (); close_out cout; raise e
  end;
  pp_flush_with ft ();
  close_out cout
