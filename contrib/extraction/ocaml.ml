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

let fnl2 () = fnl () ++ fnl () 

(*s Generic renaming issues. *)

let rec rename_id id avoid = 
  if Idset.mem id avoid then rename_id (lift_ident id) avoid else id

let lowercase_id id = id_of_string (String.uncapitalize (string_of_id id))
let uppercase_id id = id_of_string (String.capitalize (string_of_id id))

(* [pr_upper_id id] makes 2 String.copy lesser than [pr_id (uppercase_id id)] *)
let pr_upper_id id = str (String.capitalize (string_of_id id))

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
  let pp_mp = function 
    | MPfile d -> pr_upper_id (List.hd (repr_dirpath d))
    | _ -> assert false 
  in 
  prlist (fun mp -> str "open " ++ pp_mp mp ++ fnl ()) used_modules
  ++ 
  (if used_modules = [] then mt () else fnl ())
  ++
  (if tdummy || tunknown then str "type __ = Obj.t" ++ fnl() else mt()) 
  ++
  (if mldummy then 
     str "let __ = let rec f _ = Obj.repr f in Obj.repr f" ++ fnl ()
   else mt ()) 
  ++ 
  (if tdummy || tunknown || mldummy then fnl () else mt ())

let preamble_sig _ used_modules (_,tdummy,tunknown) = 
  let pp_mp = function 
    | MPfile d -> pr_upper_id (List.hd (repr_dirpath d))
    | _ -> assert false 
  in 
  prlist (fun mp -> str "open " ++ pp_mp mp ++ fnl ()) used_modules
  ++ 
  (if used_modules = [] then mt () else fnl ())
  ++
  (if tdummy || tunknown then str "type __ = Obj.t" ++ fnl() ++ fnl () 
   else mt()) 

(*s The pretty-printing functor. *)

module Make = functor(P : Mlpp_param) -> struct

let local_mp = ref initial_path

let pp_global r = 
  let r = long_r r in 
  if is_inline_custom r then str (find_custom r) 
  else P.pp_global !local_mp  r

let empty_env () = [], P.globals ()

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
    | MLglob r -> 
	(try 
	   let _,args = list_chop (projection_arity r) args in 
	   let record = List.hd args in 
	   pp_apply (record ++ str "." ++ pp_global r) par (List.tl args)
	 with _ -> apply (pp_global r))
    | MLcons (r,[]) ->
	assert (args=[]);
	if Refset.mem (long_r r) !cons_cofix then 
	  pp_par par (str "lazy " ++ pp_global r)
	else pp_global r
    | MLcons (r,args') -> 
	(try 
	   let projs = find_projections (kn_of_r r) in 
	   pp_record_pat (projs, List.map (pp_expr true env []) args')
	 with Not_found ->
	   assert (args=[]);
	   let tuple = pp_tuple (pp_expr true env []) args' in 
	   if Refset.mem (long_r r) !cons_cofix then 
	     pp_par par (str "lazy (" ++ pp_global r ++ spc() ++ tuple ++str ")")
	   else pp_par par (pp_global r ++ spc () ++ tuple))
    | MLcase (t, pv) ->
	let r,_,_ = pv.(0) in 
	let expr = if Refset.mem (long_r r) !cons_cofix then 
	  (str "Lazy.force" ++ spc () ++ pp_expr true env [] t)
	else 
	  (pp_expr false env [] t) 
	in 
	let record = 
	  try Some (find_projections (kn_of_r r)) with Not_found -> None
	in 
	(try 
	   match record with 
	     | None -> raise Not_found 
	     | Some projs -> 
		 let (_, ids, c) = pv.(0) in 
		 let n = List.length ids in 
		 match c with 
		   | MLrel i when i <= n -> 
		       apply (pp_par par' (pp_expr true env [] t ++ str "." ++ 
					   pp_global (List.nth projs (n-i)))) 
		   | MLapp (MLrel i, a) when i <= n -> 
		       if List.exists (ast_occurs_itvl 1 n) a 
		       then raise Not_found
		       else
			 let ids,env' = push_vars (List.rev ids) env in
			 (pp_apply 
			    (pp_expr true env [] t ++ str "." ++ 
			     pp_global (List.nth projs (n-i)))
			    par ((List.map (pp_expr true env' []) a) @ args))
	     | _ -> raise Not_found
	 with Not_found -> 
	   if Array.length pv = 1 && record = None then 
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
			fnl () ++ str "  | " ++ pp_pat env pv))))
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
  let is_not_cofix pv = 
    let (r,_,_) = pv.(0) in not (Refset.mem (long_r r) !cons_cofix) 
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
  str " **)"  ++ fnl2 ()

(*s Pretty-printing of [Dfix] *)

let rec pp_Dfix init i ((rv,c,t) as fix) = 
  if i >= Array.length rv then mt () 
  else 
    let r = long_r rv.(i) in 
    if is_inline_custom r then pp_Dfix init (i+1) fix
    else 
      let e = pp_global r in
      (if init then mt () else fnl2 ()) ++
      pp_val e t.(i) ++
      str (if init then "let rec " else "and ") ++
      (if is_custom r then e ++ str " = " ++ str (find_custom r)
       else pp_function (empty_env ()) e c.(i)) ++
      pp_Dfix false (i+1) fix 
	
(*s Pretty-printing of inductive types declaration. *)

let pp_parameters l = 
  (pp_boxed_tuple pp_tvar l ++ space_if (l<>[]))

let pp_string_parameters l = 
  (pp_boxed_tuple str l ++ space_if (l<>[])) 

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

let pp_comment s = str "(* " ++ s ++ str " *)"

let pp_logical_ind packet = 
  pp_comment (pr_id packet.ip_typename ++ str " : logical inductive") ++ 
  fnl () ++ pp_comment (str "with constructors : " ++ 
			prvect_with_sep spc pr_id packet.ip_consnames)

let pp_singleton kn packet = 
  let l = rename_tvars keywords packet.ip_vars in 
  hov 2 (str "type " ++ pp_parameters l ++
	 P.pp_global !local_mp (IndRef (kn,0)) ++ str " =" ++ spc () ++
	 pp_type false l (List.hd packet.ip_types.(0)) ++ fnl () ++
	 pp_comment (str "singleton inductive, whose constructor was " ++ 
		     pr_id packet.ip_consnames.(0)))

let pp_record kn packet = 
  let kn = long_kn kn in 
  let l = List.combine (find_projections kn) packet.ip_types.(0) in 
  let projs = find_projections kn in
  let pl = rename_tvars keywords packet.ip_vars in 
  str "type " ++ pp_parameters pl ++ pp_global (IndRef (kn,0)) ++ str " = { "++
  hov 0 (prlist_with_sep (fun () -> str ";" ++ spc ()) 
	   (fun (r,t) -> pp_global r ++ str " : " ++ pp_type true pl t) l) 
  ++ str " }"

let pp_coind ip pl = 
  let r = IndRef ip in 
  let pl = rename_tvars keywords pl in
  pp_parameters pl ++ pp_global r ++ str " = " ++ 
  pp_parameters pl ++ str "__" ++ pp_global r ++ str " Lazy.t"

let pp_ind co kn ind =
  let some = ref false in 
  let init= ref (str "type ") in 
  let rec pp i =  
    if i >= Array.length ind.ind_packets then mt () 
    else 
      let ip = (kn,i) in 
      let p = ind.ind_packets.(i) in 
      if is_custom (IndRef (kn,i)) then pp (i+1)
      else begin 
	some := true; 
	if p.ip_logical then pp_logical_ind p ++ pp (i+1)
	else 
	  let s = !init in 
	  begin 
	    init := (fnl () ++ str "and "); 
	    s ++
	    (if co then pp_coind ip p.ip_vars ++ fnl () ++ str "and " else mt ())
	    ++ pp_one_ind (if co then "__" else "") ip p.ip_vars p.ip_types ++
	    pp (i+1)
	  end
      end
  in 
  let st = pp 0 in if !some then st else failwith "empty phrase"
	     

(*s Pretty-printing of a declaration. *)

let pp_mind kn i = 
  let kn = long_kn kn in 
  (match i.ind_info with 
     | Singleton -> pp_singleton kn i.ind_packets.(0)
     | Coinductive -> 
	 let nop _ = () 
	 and add r = cons_cofix := Refset.add (long_r r) !cons_cofix in 
	 decl_iter_references nop add nop (Dind (kn,i)); 
	 pp_ind true kn i
     | Record -> pp_record kn i.ind_packets.(0)
     | _ -> pp_ind false kn i)

let pp_decl mp = 
  local_mp := mp; 
  function
    | Dind (kn,i) as d -> pp_mind kn i
    | Dtype (r, l, t) ->
	if is_inline_custom r then failwith "empty phrase"
	else 
	  let l = rename_tvars keywords l in 
	  let ids, def = try 
	    let ids,s = find_type_custom r in 
	    pp_string_parameters ids, str s 
	  with not_found -> pp_parameters l, pp_type false l t
	  in 
	  hov 2 (str "type" ++ spc () ++ ids ++ pp_global r ++ 
		 spc () ++ str "=" ++ spc () ++ def)
    | Dterm (r, a, t) -> 
	if is_inline_custom r then failwith "empty phrase"
	else 
	  let e = pp_global r in 
	  pp_val e t ++
	  hov 0 
	    (str "let " ++ 
	     if is_custom r then 
	       e ++ str " = " ++ str (find_custom r)
	     else if is_projection r then 
	       let s = prvecti (fun _ -> str) 
			 (Array.make (projection_arity r) " _") in 
	       e ++ s ++ str " x = x." ++ e
	     else pp_function (empty_env ()) e a)
    | Dfix (rv,defs,typs) ->
	pp_Dfix true 0 (rv,defs,typs)

let pp_spec mp = 
  local_mp := mp; 
  function 
    | Sind (kn,i) -> pp_mind kn i
    | Sval (r,t) -> 
	if is_inline_custom r then failwith "empty phrase"
	else 
	  hov 2 (str "val" ++ spc () ++ pp_global r ++ str " :" ++ spc () ++
		 pp_type false [] t)
    | Stype (r,vl,ot) -> 
	if is_inline_custom r then failwith "empty phrase"
	else 
	  let l = rename_tvars keywords vl in 
	  let ids, def = 
	    try 
	      let ids, s = find_type_custom r in 
	      pp_string_parameters ids,  str "= " ++ str s 
	    with not_found -> 
	      let ids = pp_parameters l in 
	      match ot with 
		| None -> ids, mt () 
		| Some t -> ids, str "=" ++ spc () ++ pp_type false l t 
	  in 
	  hov 2 (str "type" ++ spc () ++ ids ++ pp_global r ++ spc () ++ def)

let rec pp_structure_elem mp = function 
  | (_,SEdecl d) -> pp_decl mp d
  | (l,SEmodule m) ->
      hov 1 
	(str "module " ++ P.pp_short_module (id_of_label l) ++ 
	 (match m.ml_mod_equiv with 
	    | None -> 
		str " :" ++ fnl () ++ 
		pp_module_type mp m.ml_mod_type ++ fnl () ++
		str "= " ++ fnl () ++ 
		(match m.ml_mod_expr with 
		   | None -> assert false (* see Jacek *)
		   | Some me -> pp_module_expr mp me)
	    | Some mp' -> 
		str " = " ++ P.pp_long_module mp mp'))
  | (l,SEmodtype m) -> 
      hov 1 
	(str "module type " ++ P.pp_short_module (id_of_label l) ++
	 str " = " ++ fnl () ++ pp_module_type mp m)

and pp_module_expr mp = function 
  | MEident mp' -> P.pp_long_module mp mp'
  | MEfunctor (mbid, mt, me) -> 
      str "functor (" ++ 
      P.pp_short_module (id_of_mbid mbid) ++
      str ":" ++
      pp_module_type mp mt ++
      str ") ->" ++ fnl () ++
      pp_module_expr mp me
  | MEapply (me, me') -> 
      pp_module_expr mp me ++ str "(" ++ pp_module_expr mp me' ++ str ")"
  | MEstruct (msid, sel) -> 
      let l = map_succeed (pp_structure_elem (MPself msid)) sel in 
      str "struct " ++ fnl () ++
      v 1 (str " " ++ prlist_with_sep fnl2 identity l) ++ 
      fnl () ++ str "end" 

and pp_module_type mp = function 
  | MTident kn -> 
      let mp',_,l = repr_kn kn in P.pp_long_module mp (MPdot (mp,l)) 
  | MTfunsig (mbid, mt, mt') -> 
      str "functor (" ++ 
      P.pp_short_module (id_of_mbid mbid) ++
      str ":" ++
      pp_module_type mp mt ++
      str ") ->" ++ fnl () ++
      pp_module_type mp mt'
  | MTsig (msid, sign) -> 
      let l = map_succeed (pp_specif (MPself msid)) sign in 
      str "sig " ++ fnl () ++ 
      v 1 (str " " ++ prlist_with_sep fnl2 identity l) ++
      fnl () ++ str "end"

and pp_specif mp = function 
  | (_,Spec s) -> pp_spec mp s 
  | (l,Smodule mt) -> 
      hov 1 
	(str "module " ++ 
	 P.pp_short_module (id_of_label l) ++
	 str " : " ++ fnl () ++ pp_module_type mp mt)
  | (l,Smodtype mt) -> 
      hov 1
	(str "module type " ++
	 P.pp_short_module (id_of_label l) ++
	 str " = " ++ fnl () ++ pp_module_type mp mt)

let pp_struct s =
  let pp mp s = pp_structure_elem mp s ++ fnl2 () in 
  prlist (fun (mp,sel) -> prlist identity (map_succeed (pp mp) sel)) s

let pp_signature s = 
  let pp mp s = pp_specif mp s ++ fnl2 () in 
  prlist (fun (mp,sign) -> prlist identity (map_succeed (pp mp) sign)) s

let pp_decl mp d = 
  try pp_decl mp d with Failure "empty phrase" -> mt () 

end



