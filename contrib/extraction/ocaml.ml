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
open Mlutil
open Options

let current_module = ref None

(*s Some utility functions. *)

let string s = [< 'sTR s >]

let open_par = function true -> string "(" | false -> [< >]

let close_par = function true -> string ")" | false -> [< >]

let rec collapse_type_app = function
  | (Tapp l1) :: l2 -> collapse_type_app (l1 @ l2)
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

let space_if = function true -> [< 'sTR " " >] | false -> [< >]

let sec_space_if = function true -> [< 'sPC >] | false -> [< >]

(*s Ocaml renaming issues. *)

let ocaml_keywords =     
  List.fold_right (fun s -> Idset.add (id_of_string s))
  [ "and"; "as"; "assert"; "begin"; "class"; "constraint"; "do";
    "done"; "downto"; "else"; "end"; "exception"; "external"; "false";
    "for"; "fun"; "function"; "functor"; "if"; "in"; "include";
    "inherit"; "initializer"; "lazy"; "let"; "match"; "method";
    "module"; "mutable"; "new"; "object"; "of"; "open"; "or";
    "parser"; "private"; "rec"; "sig"; "struct"; "then"; "to"; "true";
    "try"; "type"; "val"; "virtual"; "when"; "while"; "with"; "mod";
    "land"; "lor"; "lxor"; "lsl"; "lsr"; "asr" ] 
  Idset.empty

let current_ids = ref ocaml_keywords

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

(*s Modules considerations *)

let module_of_r r = snd (split_dirpath (dirpath (sp_of_r r)))

let string_of_r r = string_of_id (basename (sp_of_r r))

let module_option r = 
  let m = module_of_r r in
  if Some m = !current_module then ""
  else (String.capitalize (string_of_id m)) ^ "."

let check_ml r d = 
  try find_ml_extraction r
  with Not_found -> d

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
  | l  -> [< 'sTR "fun ";
             prlist_with_sep (fun () -> [< 'sTR " " >]) pr_id l;
             'sTR " ->"; 'sPC >]

let pr_binding = function
  | [] -> [< >]
  | l  -> [< 'sTR " "; prlist_with_sep (fun () -> [< 'sTR " " >]) pr_id l >]

(*s The pretty-printing functor. *)

module Make = functor(P : Mlpp_param) -> struct

let pp_type_global = P.pp_type_global
let pp_global = P.pp_global

(*s Pretty-printing of types. [par] is a boolean indicating whether parentheses
    are needed or not. *)

let rec pp_type par t =
  let rec pp_rec par = function
    | Tvar id -> 
	string ("'" ^ string_of_id id)
    | Tapp l ->
	(match collapse_type_app l with
	   | [] -> assert false
	   | [t] -> pp_rec par t
	   | t::l -> [< pp_tuple (pp_rec false) l; 
			sec_space_if (l <>[]); 
			pp_rec false t >])
    | Tarr (t1,t2) ->
	[< open_par par; pp_rec true t1; 'sPC; 'sTR "->"; 'sPC; 
	   pp_rec false t2; close_par par >]
    | Tglob r -> 
	pp_type_global r
    | Tprop ->
	string "prop"
    | Tarity ->
	string "arity"
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
	   pp_tuple (pp_expr true env []) args'; close_par par >]
    | MLcase (t, pv) ->
      	apply
      	  [< if args <> [] then [< 'sTR "(" >]  else open_par par;
      	     v 0 [< 'sTR "match "; pp_expr false env [] t; 'sTR " with";
		    'fNL; 'sTR "  "; pp_pat env pv >];
	     if args <> [] then [< 'sTR ")" >] else close_par par >]
    | MLfix (i,ids,defs) ->
	let ids',env' = push_vars (List.rev (Array.to_list ids)) env in
      	pp_fix par env' (Some i) (Array.of_list (List.rev ids'),defs) args
    | MLexn id -> 
	[< open_par par; 'sTR "failwith"; 'sPC; 
	   'qS (string_of_id id); close_par par >]
    | MLprop ->
	string "prop"
    | MLarity ->
	string "arity"
    | MLcast (a,t) ->
	[< open_par true; pp_expr false env args a; 'sPC; 'sTR ":"; 'sPC; 
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
	       | _  -> [< 'sTR " "; pp_boxed_tuple pr_id (List.rev ids) >]
	     end;
	     'sTR " ->"; 'sPC; pp_expr par env' [] t >]
  in 
  if pv = [||] then
    [< 'sTR "_ -> assert false (* empty inductive *)" >]
  else
    [< prvect_with_sep (fun () -> [< 'fNL; 'sTR "| " >]) pp_one_pat pv >]

(*s names of the functions ([ids]) are already pushed in [env],
    and passed here just for convenience. *)

and pp_fix par env in_p (ids,bl) args =
  [< open_par par; 
     v 0 [< 'sTR "let rec " ;
	    prvect_with_sep
      	      (fun () -> [< 'fNL; 'sTR "and " >])
	      (fun (fi,ti) -> pp_function env (pr_id fi) ti)
	      (array_map2 (fun id b -> (id,b)) ids bl);
	    'fNL;
	    match in_p with
	      | Some j -> 
      		  hOV 2 [< 'sTR "in "; pr_id (ids.(j));
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
  let is_function pv =
    let ktl = array_map_to_list (fun (_,l,t0) -> (List.length l,t0)) pv in
    not (List.exists (fun (k,t0) -> Mlutil.occurs (k+1) t0) ktl)
  in
  match t' with 
    | MLcase(MLrel 1,pv) ->
	if is_function pv then
	  [< f; pr_binding (List.rev (List.tl bl)) ;
       	     'sTR " = function"; 'fNL;
	     v 0 [< 'sTR "  "; pp_pat env' pv >] >]
	else
          [< f; pr_binding (List.rev bl); 
             'sTR " = match ";
	     pr_id (List.hd bl); 'sTR " with"; 'fNL;
	     v 0 [< 'sTR "  "; pp_pat env' pv >] >]
	  
    | _ -> [< f; pr_binding (List.rev bl);
	      'sTR " ="; 'fNL; 'sTR "  ";
	      hOV 2 (pp_expr false env' [] t') >]
	
let pp_ast a = hOV 0 (pp_expr false (empty_env ()) [] a)

(*s Pretty-printing of inductive types declaration. *)

let pp_parameters l = 
  [< pp_tuple (fun id -> string ("'" ^ string_of_id id)) l; space_if (l<>[]) >]

let pp_one_inductive (pl,name,cl) =
  let pp_constructor (id,l) =
    [< pp_global id;
       match l with
         | [] -> [< >] 
	 | _  -> [< 'sTR " of " ;
      	       	    prlist_with_sep 
		      (fun () -> [< 'sPC ; 'sTR "* " >]) (pp_type true) l >] >]
  in
  [< pp_parameters pl; pp_type_global name; 'sTR " ="; 
     if cl = [] then
       [< 'sTR " unit (* empty inductive *)" >]
     else
       [< 'fNL;
	  v 0 [< 'sTR "    ";
		 prlist_with_sep (fun () -> [< 'fNL; 'sTR "  | " >])
                   (fun c -> hOV 2 (pp_constructor c)) cl >] >] >]

let pp_inductive il =
  [< 'sTR "type ";
     prlist_with_sep (fun () -> [< 'fNL; 'sTR "and " >]) pp_one_inductive il;
     'fNL >]

(*s Pretty-printing of a declaration. *)

let warning_coinductive r = 
  wARN (hOV 0 
	  [< 'sTR "You are trying to extract the CoInductive definition"; 'sPC;
	     Printer.pr_global r; 'sPC; 'sTR "in Ocaml."; 'sPC; 
	     'sTR "This is in general NOT a good idea,"; 'sPC; 
	     'sTR "since Ocaml is not lazy."; 'sPC;
	     'sTR "You should consider using Haskell instead." >])

let pp_decl = function
  | Dtype ([], _) -> 
      [< >]
  | Dtype ((_,r,_)::_ as i, cofix) -> 
      if cofix && P.cofix_warning then if_verbose warning_coinductive r; 
      hOV 0 (pp_inductive i)
  | Dabbrev (r, l, t) ->
      hOV 0 [< 'sTR "type"; 'sPC; pp_parameters l; 
	       pp_type_global r; 'sPC; 'sTR "="; 'sPC; 
	       pp_type false  t; 'fNL >]
  | Dglob (r, MLfix (_,[|_|],[|def|])) ->
      let id = P.rename_global r in
      let env' = ([id], !current_ids) in
      [<  hOV 2 (pp_fix false env' None ([|id|],[|def|]) []) >]
  | Dglob (r, a) ->
      hOV 0 [< 'sTR "let "; 
	       pp_function (empty_env ()) (pp_global r) a; 'fNL >]

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
       rename_lower_global id)

let rename_global r = 
  cache r
    (fun r -> 
       let id = Environ.id_of_global (Global.env()) r in
       match r with
	 | ConstructRef _ -> rename_upper_global id
	 | _ -> rename_lower_global id)

let pp_type_global r = 
  string (check_ml r (string_of_id (rename_type_global r)))

let pp_global r = 
  string (check_ml r (string_of_id (rename_global r)))

let cofix_warning = true

end

module MonoPp = Make(MonoParams)

(*s Renaming issues in a modular extraction. *)



module ModularParams = struct

  let avoid = 
    Idset.add (id_of_string "prop")
      (Idset.add (id_of_string "arity") ocaml_keywords)

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

  let rename_type_global r = 
    let id = Environ.id_of_global (Global.env()) r in 
    rename_lower id

  let rename_global_aux r = 
    let id = Environ.id_of_global (Global.env()) r in 
    match r with
      | ConstructRef _ -> rename_upper id
      | _ -> rename_lower id

  let rename_global r = id_of_string (rename_global_aux r)

  let pp_type_global r = 
    string (check_ml r ((module_option r)^(rename_type_global r)))

  let pp_global r = 
    string (check_ml r ((module_option r)^(rename_global_aux r)))

  let cofix_warning = true
end

module ModularPp = Make(ModularParams)

(*s Extraction to a file. *)

let ocaml_preamble () =
  [< 'sTR "type prop = unit"; 'fNL;
     'sTR "let prop = ()"; 'fNL; 'fNL;
     'sTR "type arity = unit"; 'fNL;
     'sTR "let arity = ()"; 'fNL; 'fNL >]


let ocaml_header ft b ml_decls =
  let l,l' = ml_cst_extractions () in
  List.iter2 
    (fun r s -> 
       if (not b) or (Some (module_of_r r) = !current_module)  then 
       pP_with ft (hV 0  
	 [< 'sTR "let "; 'sTR (string_of_r r); 'sTR " ="; 'sPC; 'sTR s; 'fNL ; 'fNL >]))
    ((List.rev l) @ ml_decls)
    ((List.rev l') @ (List.map find_ml_extraction ml_decls))

let extract_to_file f prm decls ml_decls =
  let pp_decl = if prm.modular then ModularPp.pp_decl else MonoPp.pp_decl in
  let cout = open_out f in
  let ft = Pp_control.with_output_to cout in
  pP_with ft (hV 0 (ocaml_preamble ()));
  ocaml_header ft prm.modular ml_decls;
  begin 
    try
      List.iter (fun d -> mSGNL_with ft (pp_decl d)) decls
    with e ->
      pp_flush_with ft (); close_out cout; raise e
  end;
  pp_flush_with ft ();
  close_out cout
