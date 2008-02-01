(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

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
open Modutil
open Common
open Declarations


(*s Some utility functions. *)

let rec  msid_of_mt = function
  | MTident mp -> begin
      match Modops.eval_struct (Global.env()) (SEBident mp) with
	| SEBstruct(msid,_) -> MPself msid
	| _ -> anomaly "Extraction:the With can'tbe applied to a funsig"
    end
  | MTwith(mt,_)-> msid_of_mt mt
  | _ -> anomaly "Extraction:the With operator isn't applied to a name"

let  make_mp_with mp idl =
  let idl_rev = List.rev idl in
  let idl' = List.rev (List.tl idl_rev) in
    (List.fold_left (fun mp id -> MPdot(mp,label_of_id id))
       mp idl')


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

let pp_parameters l = 
  (pp_boxed_tuple pp_tvar l ++ space_if (l<>[]))

let pp_string_parameters l = 
  (pp_boxed_tuple str l ++ space_if (l<>[])) 

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

let pp_open mp = str ("open "^ string_of_modfile mp ^"\n")

let preamble _ used_modules usf = 
  prlist pp_open used_modules ++
  (if used_modules = [] then mt () else fnl ()) ++
  (if usf.tdummy || usf.tunknown then str "type __ = Obj.t\n" else mt()) ++
  (if usf.mldummy then 
     str "let __ = let rec f _ = Obj.repr f in Obj.repr f\n"
   else mt ()) ++
  (if usf.tdummy || usf.tunknown || usf.mldummy then fnl () else mt ())

let sig_preamble _ used_modules usf =
  prlist pp_open used_modules ++
  (if used_modules = [] then mt () else fnl ()) ++
  (if usf.tdummy || usf.tunknown then str "type __ = Obj.t\n\n" else mt())

(*s The pretty-printer for Ocaml syntax*)

let pp_global k r = 
  if is_inline_custom r then str (find_custom r) 
  else str (Common.pp_global k r)

let pp_modname mp = str (Common.pp_module mp)

let is_infix r = 
  is_inline_custom r && 
  (let s = find_custom r in 
   let l = String.length s in 
   l >= 2 && s.[0] = '(' && s.[l-1] = ')')

let get_infix r = 
  let s = find_custom r in 
  String.sub s 1 (String.length s - 2)

exception NoRecord

let find_projections = function Record l -> l | _ -> raise NoRecord

(*s Pretty-printing of types. [par] is a boolean indicating whether parentheses
    are needed or not. *)

let kn_sig = 
  let specif = MPfile (dirpath_of_string "Coq.Init.Specif") in 
  make_kn specif empty_dirpath (mk_label "sig")

let rec pp_type par vl t =
  let rec pp_rec par = function
    | Tmeta _ | Tvar' _ | Taxiom -> assert false
    | Tvar i -> (try pp_tvar (List.nth vl (pred i)) 
		 with _ -> (str "'a" ++ int i))
    | Tglob (r,[a1;a2]) when is_infix r -> 
	pp_par par 
	  (pp_rec true a1 ++ spc () ++ str (get_infix r) ++ spc () ++ 
	   pp_rec true a2)
    | Tglob (r,[]) -> pp_global Type r
    | Tglob (r,l) -> 
	if r = IndRef (kn_sig,0) then 
	  pp_tuple_light pp_rec l
	else 
	  pp_tuple_light pp_rec l ++ spc () ++ pp_global Type r
    | Tarr (t1,t2) ->
	pp_par par 
	  (pp_rec true t1 ++ spc () ++ str "->" ++ spc () ++ pp_rec false t2)
    | Tdummy _ -> str "__"
    | Tunknown -> str "__"
  in 
  hov 0 (pp_rec par t)

(*s Pretty-printing of expressions. [par] indicates whether
    parentheses are needed or not. [env] is the list of names for the
    de Bruijn variables. [args] is the list of collected arguments
    (already pretty-printed). *)

let is_ifthenelse = function 
  | [|(r1,[],_);(r2,[],_)|] -> 
      (try (find_custom r1 = "true") && (find_custom r2 = "false") 
       with Not_found -> false)
  | _ -> false

let expr_needs_par = function
  | MLlam _  -> true
  | MLcase (_,_,[|_|]) -> false 
  | MLcase (_,_,pv) -> not (is_ifthenelse pv)
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
	let i,env' = push_vars [id] env in
	let pp_id = pr_id (List.hd i)
	and pp_a1 = pp_expr false env [] a1
	and pp_a2 = pp_expr (not par && expr_needs_par a2) env' [] a2 in 
	hv 0 
	  (apply 
	     (pp_par par' 
		(hv 0 
		   (hov 2 
		      (str "let " ++ pp_id ++ str " =" ++ spc () ++ pp_a1) ++ 
		    spc () ++ str "in") ++ 
		 spc () ++ hov 0 pp_a2)))
    | MLglob r -> 
	(try 
	   let args = list_skipn (projection_arity r) args in 
	   let record = List.hd args in 
	   pp_apply (record ++ str "." ++ pp_global Term r) par (List.tl args)
	 with _ -> apply (pp_global Term r))
    | MLcons (Coinductive,r,[]) ->
	assert (args=[]);
	pp_par par (str "lazy " ++ pp_global Cons r)
    | MLcons (Coinductive,r,args') -> 
	assert (args=[]);
	let tuple = pp_tuple (pp_expr true env []) args' in 
	pp_par par (str "lazy (" ++ pp_global Cons r ++ spc() ++ tuple ++str ")")
    | MLcons (_,r,[]) -> 
	assert (args=[]);
	pp_global Cons r
    | MLcons (Record projs, r, args') -> 
	assert (args=[]); 
	pp_record_pat (projs, List.map (pp_expr true env []) args')
    | MLcons (_,r,[arg1;arg2]) when is_infix r -> 
	assert (args=[]); 
	pp_par par
	  ((pp_expr true env [] arg1) ++ spc () ++ str (get_infix r) ++
	   spc () ++ (pp_expr true env [] arg2))
    | MLcons (_,r,args') -> 
	assert (args=[]);
	let tuple = pp_tuple (pp_expr true env []) args' in 
	pp_par par (pp_global Cons r ++ spc () ++ tuple)
    | MLcase ((i,factors), t, pv) ->
	let expr = if i = Coinductive then 
	  (str "Lazy.force" ++ spc () ++ pp_expr true env [] t)
	else 
	  (pp_expr false env [] t) 
	in 
	(try 
	   let projs = find_projections i in 
	   let (_, ids, c) = pv.(0) in 
	   let n = List.length ids in 
	   match c with 
	     | MLrel i when i <= n -> 
		 apply (pp_par par' (pp_expr true env [] t ++ str "." ++ 
				     pp_global Term (List.nth projs (n-i))))
	     | MLapp (MLrel i, a) when i <= n -> 
		 if List.exists (ast_occurs_itvl 1 n) a 
		 then raise NoRecord
		 else
		   let ids,env' = push_vars (List.rev ids) env in
		   (pp_apply 
		      (pp_expr true env [] t ++ str "." ++ 
		       pp_global Term (List.nth projs (n-i)))
		      par ((List.map (pp_expr true env' []) a) @ args))
	     | _ -> raise NoRecord
	 with NoRecord -> 
	   if Array.length pv = 1 then 
	     let s1,s2 = pp_one_pat env i pv.(0) in 
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
		  (try pp_ifthenelse par' env expr pv 
		   with Not_found -> 
		     v 0 (str "match " ++ expr ++ str " with" ++ fnl () ++
			  str "  | " ++ pp_pat env (i,factors) pv))))
    | MLfix (i,ids,defs) ->
	let ids',env' = push_vars (List.rev (Array.to_list ids)) env in
      	pp_fix par env' i (Array.of_list (List.rev ids'),defs) args
    | MLexn s -> 
	(* An [MLexn] may be applied, but I don't really care. *)
	pp_par par (str "assert false" ++ spc () ++ str ("(* "^s^" *)"))
    | MLdummy ->
	str "__" (* An [MLdummy] may be applied, but I don't really care. *)
    | MLmagic a ->
	pp_apply (str "Obj.magic") par (pp_expr true env [] a :: args)
    | MLaxiom -> 
	pp_par par (str "failwith \"AXIOM TO BE REALIZED\"")

	  
and pp_record_pat (projs, args) =
   str "{ " ++
   prlist_with_sep (fun () -> str ";" ++ spc ()) 
     (fun (r,a) -> pp_global Term r ++ str " =" ++ spc () ++ a)
     (List.combine projs args) ++
   str " }"

and pp_ifthenelse par env expr pv = match pv with 
  | [|(tru,[],the);(fal,[],els)|] when 
      (find_custom tru = "true") && (find_custom fal = "false")
      -> 
      hv 0 (hov 2 (str "if " ++ expr) ++ spc () ++ 
            hov 2 (str "then " ++
		   hov 2 (pp_expr (expr_needs_par the) env [] the)) ++ spc () ++ 
	    hov 2 (str "else " ++
	           hov 2 (pp_expr (expr_needs_par els) env [] els)))
  | _ -> raise Not_found

and pp_one_pat env i (r,ids,t) = 
  let ids,env' = push_vars (List.rev ids) env in
  let expr = pp_expr (expr_needs_par t) env' [] t in 
  try 
    let projs = find_projections i in 
    pp_record_pat (projs, List.rev_map pr_id ids), expr
  with NoRecord -> 
    (match List.rev ids with 
      | [i1;i2] when is_infix r -> 
	  pr_id i1 ++ str " " ++ str (get_infix r) ++ str " " ++ pr_id i2
      | [] -> pp_global Cons r
      | ids -> pp_global Cons r ++ str " " ++ pp_boxed_tuple pr_id ids), 
    expr
  
and pp_pat env (info,factors) pv = 
  prvecti 
    (fun i x -> if List.mem i factors then mt () else 
       let s1,s2 = pp_one_pat env info x in 
       hov 2 (s1 ++ str " ->" ++ spc () ++ s2) ++
       (if factors = [] && i = Array.length pv-1 then mt () 
	else fnl () ++ str "  | ")) pv 
  ++ 
  match factors with 
     | [] -> mt ()
     | i::_ -> 
	 let (_,ids,t) = pv.(i) in 
	 let t = ast_lift (-List.length ids) t in 
	 hov 2 (str "_ ->" ++ spc () ++ pp_expr (expr_needs_par t) env [] t)

and pp_function env t =
  let bl,t' = collect_lams t in
  let bl,env' = push_vars bl env in
  match t' with 
    | MLcase(i,MLrel 1,pv) when fst i=Standard -> 
	if not (ast_occurs 1 (MLcase(i,MLdummy,pv))) then 
	  pr_binding (List.rev (List.tl bl)) ++
       	  str " = function" ++ fnl () ++
	  v 0 (str "  | " ++ pp_pat env' i pv)
	else
          pr_binding (List.rev bl) ++ 
          str " = match " ++ pr_id (List.hd bl) ++ str " with" ++ fnl () ++
	  v 0 (str "  | " ++ pp_pat env' i pv)
    | _ -> 
          pr_binding (List.rev bl) ++
	  str " =" ++ fnl () ++ str "  " ++
	  hov 2 (pp_expr false env' [] t')

(*s names of the functions ([ids]) are already pushed in [env],
    and passed here just for convenience. *)

and pp_fix par env i (ids,bl) args =
  pp_par par 
    (v 0 (str "let rec " ++
	  prvect_with_sep
      	    (fun () -> fnl () ++ str "and ")
	    (fun (fi,ti) -> pr_id fi ++ pp_function env ti)
	    (array_map2 (fun id b -> (id,b)) ids bl) ++
	  fnl () ++
	  hov 2 (str "in " ++ pp_apply (pr_id ids.(i)) false args)))

let pp_val e typ = 
  hov 4 (str "(** val " ++ e ++ str " :" ++ spc () ++ pp_type false [] typ ++ 
  str " **)")  ++ fnl2 ()

(*s Pretty-printing of [Dfix] *)

let pp_Dfix (rv,c,t) = 
  let names = Array.map 
    (fun r -> if is_inline_custom r then mt () else pp_global Term r) rv
  in 
  let rec pp sep letand i = 
    if i >= Array.length rv then mt ()
    else if is_inline_custom rv.(i) then pp sep letand (i+1)
    else 
      let def = 
	if is_custom rv.(i) then str " = " ++ str (find_custom rv.(i))
	else pp_function (empty_env ()) c.(i)
      in 
      sep () ++ pp_val names.(i) t.(i) ++ 
      str letand ++ names.(i) ++ def ++ pp fnl2 "and " (i+1) 
  in pp mt "let rec " 0

(*s Pretty-printing of inductive types declaration. *)

let pp_equiv param_list name = function 
  | NoEquiv, _ -> mt ()
  | Equiv kn, i -> 
      str " = " ++ pp_parameters param_list ++ pp_global Type (IndRef (kn,i))
  | RenEquiv ren, _  ->
      str " = " ++ pp_parameters param_list ++ str (ren^".") ++ name

let pp_comment s = str "(* " ++ s ++ str " *)"

let pp_one_ind prefix ip_equiv pl name cnames ctyps =
  let pl = rename_tvars keywords pl in
  let pp_constructor i typs =
    (if i=0 then mt () else fnl ()) ++ 
    hov 5 (str "  | " ++ cnames.(i) ++
	   (if typs = [] then mt () else str " of ") ++
	   prlist_with_sep 
	    (fun () -> spc () ++ str "* ") (pp_type true pl) typs)
  in
  pp_parameters pl ++ str prefix ++ name ++
  pp_equiv pl name ip_equiv ++ str " =" ++
  if Array.length ctyps = 0 then str " unit (* empty inductive *)" 
  else fnl () ++ v 0 (prvecti pp_constructor ctyps)

let pp_logical_ind packet = 
  pp_comment (pr_id packet.ip_typename ++ str " : logical inductive") ++ 
  fnl () ++
  pp_comment (str "with constructors : " ++ 
	      prvect_with_sep spc pr_id packet.ip_consnames) ++
  fnl ()

let pp_singleton kn packet = 
  let name = pp_global Type (IndRef (kn,0)) in 
  let l = rename_tvars keywords packet.ip_vars in 
  hov 2 (str "type " ++ pp_parameters l ++ name ++ str " =" ++ spc () ++
	 pp_type false l (List.hd packet.ip_types.(0)) ++ fnl () ++
	 pp_comment (str "singleton inductive, whose constructor was " ++ 
		     pr_id packet.ip_consnames.(0)))

let pp_record kn projs ip_equiv packet = 
  let name = pp_global Type (IndRef (kn,0)) in
  let projnames = List.map (pp_global Term) projs in 
  let l = List.combine projnames packet.ip_types.(0) in 
  let pl = rename_tvars keywords packet.ip_vars in 
  str "type " ++ pp_parameters pl ++ name ++ 
  pp_equiv pl name ip_equiv ++ str " = { "++
  hov 0 (prlist_with_sep (fun () -> str ";" ++ spc ()) 
	   (fun (p,t) -> p ++ str " : " ++ pp_type true pl t) l) 
  ++ str " }"

let pp_coind pl name = 
  let pl = rename_tvars keywords pl in
  pp_parameters pl ++ name ++ str " = " ++ 
  pp_parameters pl ++ str "__" ++ name ++ str " Lazy.t" ++ 
  fnl() ++ str "and "

let pp_ind co kn ind =
  let prefix = if co then "__" else "" in 
  let some = ref false in 
  let init= ref (str "type ") in 
  let names = 
    Array.mapi (fun i p -> if p.ip_logical then mt () else 
		  pp_global Type (IndRef (kn,i)))
      ind.ind_packets
  in 
  let cnames = 
    Array.mapi 
      (fun i p -> if p.ip_logical then [||] else 
	 Array.mapi (fun j _ -> pp_global Cons (ConstructRef ((kn,i),j+1)))
	   p.ip_types)
      ind.ind_packets
  in 
  let rec pp i =  
    if i >= Array.length ind.ind_packets then mt () 
    else 
      let ip = (kn,i) in 
      let ip_equiv = ind.ind_equiv, 0 in 
      let p = ind.ind_packets.(i) in 
      if is_custom (IndRef ip) then pp (i+1)
      else begin 
	some := true; 
	if p.ip_logical then pp_logical_ind p ++ pp (i+1)
	else 
	  let s = !init in 
	  begin 
	    init := (fnl () ++ str "and "); 
	    s ++
	    (if co then pp_coind p.ip_vars names.(i) else mt ()) ++
	    pp_one_ind 
	      prefix ip_equiv p.ip_vars names.(i) cnames.(i) p.ip_types ++
	    pp (i+1)
	  end
      end
  in 
  let st = pp 0 in if !some then st else failwith "empty phrase"
	     

(*s Pretty-printing of a declaration. *)

let pp_mind kn i = 
  match i.ind_info with 
    | Singleton -> pp_singleton kn i.ind_packets.(0)
    | Coinductive -> pp_ind true kn i
    | Record projs -> 
	pp_record kn projs (i.ind_equiv,0) i.ind_packets.(0)
    | Standard -> pp_ind false kn i

let pp_decl = function
    | Dtype (r,_,_) when is_inline_custom r -> failwith "empty phrase"
    | Dterm (r,_,_) when is_inline_custom r -> failwith "empty phrase"
    | Dind (kn,i) -> pp_mind kn i
    | Dtype (r, l, t) -> 
        let name = pp_global Type r in 
	let l = rename_tvars keywords l in 
        let ids, def = 
	  try 
	    let ids,s = find_type_custom r in 
	    pp_string_parameters ids, str "=" ++ spc () ++ str s 
	  with Not_found -> 
	    pp_parameters l, 
	    if t = Taxiom then str "(* AXIOM TO BE REALIZED *)"
	    else str "=" ++ spc () ++ pp_type false l t
	in 
	hov 2 (str "type " ++ ids ++ name ++ spc () ++ def)
    | Dterm (r, a, t) -> 
	let def = 
	  if is_custom r then str (" = " ^ find_custom r)
	  else if is_projection r then 
	    (prvect str (Array.make (projection_arity r) " _")) ++ 
	    str " x = x."
	  else pp_function (empty_env ()) a
	in 
	let name = pp_global Term r in 
	let postdef = if is_projection r then name else mt () in 
	pp_val name t ++ hov 0 (str "let " ++ name ++ def ++ postdef)
    | Dfix (rv,defs,typs) ->
	pp_Dfix (rv,defs,typs)

let pp_alias_decl ren = function 
  | Dind (kn,i) -> pp_mind kn { i with ind_equiv = RenEquiv ren }
  | Dtype (r, l, _) -> 
      let name = pp_global Type r in 
      let l = rename_tvars keywords l in 
      let ids = pp_parameters l in 
      hov 2 (str "type " ++ ids ++ name ++ str " =" ++ spc () ++ ids ++ 
	     str (ren^".") ++ name)
  | Dterm (r, a, t) -> 
      let name = pp_global Term r in
      hov 2 (str "let " ++ name ++ str (" = "^ren^".") ++ name)
  | Dfix (rv, _, _) ->
      prvecti (fun i r -> if is_inline_custom r then mt () else 
		 let name = pp_global Term r in 
		 hov 2 (str "let " ++ name ++ str (" = "^ren^".") ++ name) ++
		 fnl ()) 
	rv

let pp_spec = function 
  | Sval (r,_) when is_inline_custom r -> failwith "empty phrase"
  | Stype (r,_,_) when is_inline_custom r -> failwith "empty phrase"
  | Sind (kn,i) -> pp_mind kn i
  | Sval (r,t) -> 
      let def = pp_type false [] t in 
      let name = pp_global Term r in 
      hov 2 (str "val " ++ name ++ str " :" ++ spc () ++ def)
  | Stype (r,vl,ot) -> 
      let name = pp_global Type r in
      let l = rename_tvars keywords vl in 
      let ids, def = 
	try 
	  let ids, s = find_type_custom r in 
	  pp_string_parameters ids,  str "= " ++ str s 
	with Not_found -> 
	  let ids = pp_parameters l in 
	  match ot with 
	    | None -> ids, mt ()
	    | Some Taxiom -> ids, str "(* AXIOM TO BE REALIZED *)" 
	    | Some t -> ids, str "=" ++ spc () ++ pp_type false l t 
      in 
      hov 2 (str "type " ++ ids ++ name ++ spc () ++ def)

let pp_alias_spec ren = function 
  | Sind (kn,i) -> pp_mind kn { i with ind_equiv = RenEquiv ren }
  | Stype (r,l,_) ->       
      let name = pp_global Type r in 
      let l = rename_tvars keywords l in 
      let ids = pp_parameters l in 
      hov 2 (str "type " ++ ids ++ name ++ str " =" ++ spc () ++ ids ++ 
	     str (ren^".") ++ name)
  | Sval _ -> assert false
	  
let rec pp_specif = function 
  | (_,Spec (Sval _ as s)) -> pp_spec s
  | (l,Spec s) -> 
      (try 
	 let ren = Common.check_duplicate (top_visible_mp ()) l in 
	 hov 1 (str ("module "^ren^" : sig ") ++ fnl () ++ pp_spec s) ++
	 fnl () ++ str "end" ++ fnl () ++
	 pp_alias_spec ren s
       with Not_found -> pp_spec s)
  | (l,Smodule mt) -> 
      let def = pp_module_type (Some l) mt in 
      let def' = pp_module_type (Some l) mt in 
      let name = pp_modname (MPdot (top_visible_mp (), l)) in 
      hov 1 (str "module " ++ name ++ str " : " ++ fnl () ++ def) ++
      (try 
	 let ren = Common.check_duplicate (top_visible_mp ()) l in
	 fnl () ++ hov 1 (str ("module "^ren^" : ") ++ fnl () ++ def')
       with Not_found -> Pp.mt ())
  | (l,Smodtype mt) -> 
      let def = pp_module_type None mt in 
      let name = pp_modname (MPdot (top_visible_mp (), l)) in
      hov 1 (str "module type " ++ name ++ str " = " ++ fnl () ++ def) ++
      (try 
	 let ren = Common.check_duplicate (top_visible_mp ()) l in 
	 fnl () ++ str ("module type "^ren^" = ") ++ name
       with Not_found -> Pp.mt ())

and pp_module_type ol = function 
  | MTident kn -> 
      pp_modname kn
  | MTfunsig (mbid, mt, mt') -> 
      let name = pp_modname (MPbound mbid) in 
      let typ = pp_module_type None mt in 
      let def = pp_module_type None mt' in 
      str "functor (" ++ name ++ str ":" ++ typ ++ str ") ->" ++ fnl () ++ def
  | MTsig (msid, sign) ->
      let tvm = top_visible_mp () in 
      Option.iter (fun l -> add_subst msid (MPdot (tvm, l))) ol; 
      let mp = MPself msid in
      push_visible mp; 
      let l = map_succeed pp_specif sign in 
      pop_visible (); 
      str "sig " ++ fnl () ++ 
      v 1 (str " " ++ prlist_with_sep fnl2 identity l) ++
	fnl () ++ str "end"
  | MTwith(mt,ML_With_type(idl,vl,typ)) ->
      let l = rename_tvars keywords vl in 
      let ids = pp_parameters l in 
      let mp_mt = msid_of_mt mt in
      let mp = make_mp_with mp_mt idl in
      let gr = ConstRef (
	(make_con mp empty_dirpath
	  (label_of_id ( 
	    List.hd (List.rev idl))))) in
	push_visible mp_mt;
	let s = pp_module_type None mt ++
	  str " with type " ++
	  pp_global Type gr ++
	  ids in
	  pop_visible();
	  s ++ str "=" ++ spc () ++
	  pp_type false  vl typ
  | MTwith(mt,ML_With_module(idl,mp)) ->
      let mp_mt=msid_of_mt mt in
	push_visible mp_mt;
	let s = 
	  pp_module_type None mt ++
	    str " with module " ++
	    (pp_modname
	       (List.fold_left (fun mp id -> MPdot(mp,label_of_id id))
		  mp_mt idl))
	  ++ str " = "  
	in
	  pop_visible ();
	  s ++ (pp_modname mp)
	    
	    
let is_short = function MEident _ | MEapply _ -> true | _ -> false
  
let rec pp_structure_elem = function 
  | (l,SEdecl d) -> 
       (try 
	 let ren = Common.check_duplicate (top_visible_mp ()) l in 
	 hov 1 (str ("module "^ren^" = struct ") ++ fnl () ++ pp_decl d) ++
	 fnl () ++ str "end" ++ fnl () ++
	 pp_alias_decl ren d 
	with Not_found -> pp_decl d)
  | (l,SEmodule m) ->
      let def = pp_module_expr (Some l) m.ml_mod_expr in 
      let name = pp_modname (MPdot (top_visible_mp (), l)) in 
      hov 1 
	(str "module " ++ name ++ str " = " ++ 
	 (if (is_short m.ml_mod_expr) then mt () else fnl ()) ++ def) ++ 
      (try 
	 let ren = Common.check_duplicate (top_visible_mp ()) l in 
	 fnl () ++ str ("module "^ren^" = ") ++ name
       with Not_found -> mt ())
  | (l,SEmodtype m) -> 
      let def = pp_module_type None m in 
      let name = pp_modname (MPdot (top_visible_mp (), l)) in 
      hov 1 (str "module type " ++ name ++ str " = " ++ fnl () ++ def) ++
      (try 
	 let ren = Common.check_duplicate (top_visible_mp ()) l in 
         fnl () ++ str ("module type "^ren^" = ") ++ name
       with Not_found -> mt ())

and pp_module_expr ol = function 
  | MEident mp' -> pp_modname mp'
  | MEfunctor (mbid, mt, me) -> 
      let name = pp_modname (MPbound mbid) in
      let typ = pp_module_type None mt in 
      let def = pp_module_expr None me in 
      str "functor (" ++ name ++ str ":" ++ typ ++ str ") ->" ++ fnl () ++ def
  | MEapply (me, me') -> 
      pp_module_expr None me ++ str "(" ++ pp_module_expr None me' ++ str ")"
  | MEstruct (msid, sel) -> 
      let tvm = top_visible_mp () in 
      let mp = match ol with None -> MPself msid | Some l -> MPdot (tvm,l) in
      push_visible mp; 
      let l = map_succeed pp_structure_elem sel in 
      pop_visible (); 
      str "struct " ++ fnl () ++
      v 1 (str " " ++ prlist_with_sep fnl2 identity l) ++ 
      fnl () ++ str "end" 

let pp_struct s =
  let pp mp s = 
    push_visible mp; 
    let p = pp_structure_elem s ++ fnl2 () in 
    pop_visible (); p
  in
  prlist_strict 
    (fun (mp,sel) -> prlist_strict identity (map_succeed (pp mp) sel)) s

let pp_signature s = 
  let pp mp s = 
    push_visible mp; 
    let p = pp_specif s ++ fnl2 () in 
    pop_visible (); p
  in 
  prlist_strict
    (fun (mp,sign) -> prlist_strict identity (map_succeed (pp mp) sign)) s

let pp_decl d = 
  try pp_decl d with Failure "empty phrase" -> mt ()

let ocaml_descr = {
  keywords = keywords;  
  file_suffix = ".ml"; 
  capital_file = false;  
  preamble = preamble; 
  pp_struct = pp_struct; 
  sig_suffix = Some ".mli";  
  sig_preamble = sig_preamble; 
  pp_sig = pp_signature;
  pp_decl = pp_decl; 
}


