(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

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

(* Beware of the side-effects of [pp_global] and [pp_modname].
   They are used to update table of content for modules. Many [let]
   below should not be altered since they force evaluation order.
*)

let str_global k r =
  if is_inline_custom r then find_custom r else Common.pp_global k r

let pp_global k r = str (str_global k r)

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

let mk_ind path s =
  make_mind (MPfile (dirpath_of_string path)) empty_dirpath (mk_label s)

let rec pp_type par vl t =
  let rec pp_rec par = function
    | Tmeta _ | Tvar' _ | Taxiom -> assert false
    | Tvar i -> (try pp_tvar (List.nth vl (pred i))
		 with _ -> (str "'a" ++ int i))
    | Tglob (r,[a1;a2]) when is_infix r ->
	pp_par par (pp_rec true a1 ++ str (get_infix r) ++ pp_rec true a2)
    | Tglob (r,[]) -> pp_global Type r
    | Tglob (IndRef(kn,0),l) when kn = mk_ind "Coq.Init.Specif" "sig" ->
	pp_tuple_light pp_rec l
    | Tglob (r,l) ->
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


(** Special hack for constants of type Ascii.ascii : if an
    [Extract Inductive ascii => char] has been declared, then
    the constants are directly turned into chars *)

let ind_ascii = mk_ind "Coq.Strings.Ascii" "ascii"

let check_extract_ascii () =
  try find_custom (IndRef (ind_ascii,0)) = "char" with Not_found -> false

let is_list_cons l =
 List.for_all (function MLcons (_,ConstructRef(_,_),[]) -> true | _ -> false) l

let pp_char l =
  let rec cumul = function
    | [] -> 0
    | MLcons(_,ConstructRef(_,j),[])::l -> (2-j) + 2 * (cumul l)
    | _ -> assert false
  in str ("'"^Char.escaped (Char.chr (cumul l))^"'")

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
	let fl = List.map id_of_mlid fl in
	let fl,env' = push_vars fl env in
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
    | MLcons(_,ConstructRef ((kn,0),1),l)
        when kn = ind_ascii && check_extract_ascii () & is_list_cons l ->
	assert (args=[]);
	pp_char l
    | MLcons ({c_kind = Coinductive},r,[]) ->
	assert (args=[]);
	pp_par par (str "lazy " ++ pp_global Cons r)
    | MLcons ({c_kind = Coinductive},r,args') ->
	assert (args=[]);
	let tuple = pp_tuple (pp_expr true env []) args' in
	pp_par par (str "lazy (" ++ pp_global Cons r ++ spc() ++ tuple ++str ")")
    | MLcons (_,r,[]) ->
	assert (args=[]);
	pp_global Cons r
    | MLcons ({c_kind = Record projs}, r, args') ->
	assert (args=[]);
	pp_record_pat (projs, List.map (pp_expr true env []) args')
    | MLcons (_,r,[arg1;arg2]) when is_infix r ->
	assert (args=[]);
	pp_par par
	  ((pp_expr true env [] arg1) ++ str (get_infix r) ++
	   (pp_expr true env [] arg2))
    | MLcons (_,r,args') ->
	assert (args=[]);
	let tuple = pp_tuple (pp_expr true env []) args' in
	if str_global Cons r = "" (* hack Extract Inductive prod *)
	then tuple
	else pp_par par (pp_global Cons r ++ spc () ++ tuple)
    | MLcase (_, t, pv) when is_custom_match pv ->
	let mkfun (_,ids,e) =
	  if ids <> [] then named_lams (List.rev ids) e
	  else dummy_lams (ast_lift 1 e) 1
	in
	apply
	  (pp_par par'
	     (hov 2
		(str (find_custom_match pv) ++ fnl () ++
		 prvect (fun tr -> pp_expr true env [] (mkfun tr) ++ fnl ()) pv
		 ++ pp_expr true env [] t)))
    | MLcase (info, t, pv) ->
	let expr = if info.m_kind = Coinductive then
	  (str "Lazy.force" ++ spc () ++ pp_expr true env [] t)
	else
	  (pp_expr false env [] t)
	in
	(try
	   let projs = find_projections info.m_kind in
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
		   let ids,env' = push_vars (List.rev_map id_of_mlid ids) env
		   in
		   (pp_apply
		      (pp_expr true env [] t ++ str "." ++
		       pp_global Term (List.nth projs (n-i)))
		      par ((List.map (pp_expr true env' []) a) @ args))
	     | _ -> raise NoRecord
	 with NoRecord ->
	   if Array.length pv = 1 then
	     let s1,s2 = pp_one_pat env info pv.(0) in
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
			  str "  | " ++ pp_pat env info pv))))
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

and pp_one_pat env info (r,ids,t) =
  let ids,env' = push_vars (List.rev_map id_of_mlid ids) env in
  let expr = pp_expr (expr_needs_par t) env' [] t in
  try
    let projs = find_projections info.m_kind in
    pp_record_pat (projs, List.rev_map pr_id ids), expr
  with NoRecord ->
    (match List.rev ids with
      | [i1;i2] when is_infix r -> pr_id i1 ++ str (get_infix r) ++ pr_id i2
      | [] -> pp_global Cons r
      | ids ->
	  (* hack Extract Inductive prod *)
	  (if str_global Cons r = "" then mt () else pp_global Cons r ++ spc ())
	   ++ pp_boxed_tuple pr_id ids),
    expr

and pp_pat env info pv =
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
       let s1,s2 = pp_one_pat env info x in
       hov 2 (s1 ++ str " ->" ++ spc () ++ s2) ++
       if i = last && Intset.is_empty factor_set then mt () else
       fnl () ++ str "  | ") pv
  ++
  if Intset.is_empty factor_set then mt () else
  let par = expr_needs_par factor_br in
  match info.m_same with
    | BranchFun _ ->
        let ids, env' = push_vars [anonymous_name] env in
        hov 2 (pr_id (List.hd ids) ++ str " ->" ++ spc () ++
		 pp_expr par env' [] factor_br)
    | BranchCst _ ->
        hov 2 (str "_ ->" ++ spc () ++ pp_expr par env [] factor_br)
    | BranchNone -> mt ()

and pp_function env t =
  let bl,t' = collect_lams t in
  let bl,env' = push_vars (List.map id_of_mlid bl) env in
  match t' with
    | MLcase(i,MLrel 1,pv) when
	i.m_kind = Standard && not (is_custom_match pv) ->
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
      str " = " ++ pp_parameters param_list ++ pp_global Type (IndRef (mind_of_kn kn,i))
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
  let name = pp_global Type (IndRef (mind_of_kn kn,0)) in
  let l = rename_tvars keywords packet.ip_vars in
  hov 2 (str "type " ++ pp_parameters l ++ name ++ str " =" ++ spc () ++
	 pp_type false l (List.hd packet.ip_types.(0)) ++ fnl () ++
	 pp_comment (str "singleton inductive, whose constructor was " ++
		     pr_id packet.ip_consnames.(0)))

let pp_record kn projs ip_equiv packet =
  let name = pp_global Type (IndRef (mind_of_kn kn,0)) in
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
		  pp_global Type (IndRef (mind_of_kn kn,i)))
      ind.ind_packets
  in
  let cnames =
    Array.mapi
      (fun i p -> if p.ip_logical then [||] else
	 Array.mapi (fun j _ -> pp_global Cons (ConstructRef ((mind_of_kn kn,i),j+1)))
	   p.ip_types)
      ind.ind_packets
  in
  let rec pp i =
    if i >= Array.length ind.ind_packets then mt ()
    else
      let ip = (mind_of_kn kn,i) in
      let ip_equiv = ind.ind_equiv, i in
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
  match i.ind_kind with
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
      let def = pp_module_type [] mt in
      let def' = pp_module_type [] mt in
      let name = pp_modname (MPdot (top_visible_mp (), l)) in
      hov 1 (str "module " ++ name ++ str " : " ++ fnl () ++ def) ++
      (try
	 let ren = Common.check_duplicate (top_visible_mp ()) l in
	 fnl () ++ hov 1 (str ("module "^ren^" : ") ++ fnl () ++ def')
       with Not_found -> Pp.mt ())
  | (l,Smodtype mt) ->
      let def = pp_module_type [] mt in
      let name = pp_modname (MPdot (top_visible_mp (), l)) in
      hov 1 (str "module type " ++ name ++ str " = " ++ fnl () ++ def) ++
      (try
	 let ren = Common.check_duplicate (top_visible_mp ()) l in
	 fnl () ++ str ("module type "^ren^" = ") ++ name
       with Not_found -> Pp.mt ())

and pp_module_type params = function
  | MTident kn ->
      pp_modname kn
  | MTfunsig (mbid, mt, mt') ->
      let typ = pp_module_type [] mt in
      let name = pp_modname (MPbound mbid) in
      let def = pp_module_type (MPbound mbid :: params) mt' in
      str "functor (" ++ name ++ str ":" ++ typ ++ str ") ->" ++ fnl () ++ def
  | MTsig (mp, sign) ->
      push_visible mp params;
      let l = map_succeed pp_specif sign in
      pop_visible ();
      str "sig " ++ fnl () ++
      v 1 (str " " ++ prlist_with_sep fnl2 identity l) ++
	fnl () ++ str "end"
  | MTwith(mt,ML_With_type(idl,vl,typ)) ->
      let ids = pp_parameters (rename_tvars keywords vl) in
      let mp_mt = msid_of_mt mt in
      let l,idl' = list_sep_last idl in
      let mp_w =
	List.fold_left (fun mp l -> MPdot(mp,label_of_id l)) mp_mt idl'
      in
      let r = ConstRef (make_con mp_w empty_dirpath (label_of_id l)) in
      push_visible mp_mt [];
      let pp_w = str " with type " ++ ids ++ pp_global Type r in
      pop_visible();
      pp_module_type [] mt ++ pp_w ++ str " = " ++ pp_type false vl typ
  | MTwith(mt,ML_With_module(idl,mp)) ->
      let mp_mt = msid_of_mt mt in
      let mp_w =
	List.fold_left (fun mp id -> MPdot(mp,label_of_id id)) mp_mt idl
      in
      push_visible mp_mt [];
      let pp_w = str " with module " ++ pp_modname mp_w in
      pop_visible ();
      pp_module_type [] mt ++ pp_w ++ str " = " ++ pp_modname mp

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
      let typ =
        (* virtual printing of the type, in order to have a correct mli later*)
	if Common.get_phase () = Pre then
	  str ": " ++ pp_module_type [] m.ml_mod_type
	else mt ()
      in
      let def = pp_module_expr [] m.ml_mod_expr in
      let name = pp_modname (MPdot (top_visible_mp (), l)) in
      hov 1
	(str "module " ++ name ++ typ ++ str " = " ++
	 (if (is_short m.ml_mod_expr) then mt () else fnl ()) ++ def) ++
      (try
	 let ren = Common.check_duplicate (top_visible_mp ()) l in
	 fnl () ++ str ("module "^ren^" = ") ++ name
       with Not_found -> mt ())
  | (l,SEmodtype m) ->
      let def = pp_module_type [] m in
      let name = pp_modname (MPdot (top_visible_mp (), l)) in
      hov 1 (str "module type " ++ name ++ str " = " ++ fnl () ++ def) ++
      (try
	 let ren = Common.check_duplicate (top_visible_mp ()) l in
         fnl () ++ str ("module type "^ren^" = ") ++ name
       with Not_found -> mt ())

and pp_module_expr params = function
  | MEident mp -> pp_modname mp
  | MEapply (me, me') ->
      pp_module_expr [] me ++ str "(" ++ pp_module_expr [] me' ++ str ")"
  | MEfunctor (mbid, mt, me) ->
      let name = pp_modname (MPbound mbid) in
      let typ = pp_module_type [] mt in
      let def = pp_module_expr (MPbound mbid :: params) me in
      str "functor (" ++ name ++ str ":" ++ typ ++ str ") ->" ++ fnl () ++ def
  | MEstruct (mp, sel) ->
      push_visible mp params;
      let l = map_succeed pp_structure_elem sel in
      pop_visible ();
      str "struct " ++ fnl () ++
      v 1 (str " " ++ prlist_with_sep fnl2 identity l) ++
      fnl () ++ str "end"

let do_struct f s =
  let pp s = try f s ++ fnl2 () with Failure "empty phrase" -> mt ()
  in
  let ppl (mp,sel) =
    push_visible mp [];
    let p = prlist_strict pp sel in
    (* for monolithic extraction, we try to simulate the unavailability
       of [MPfile] in names by artificially nesting these [MPfile] *)
    (if modular () then pop_visible ()); p
  in
  let p = prlist_strict ppl s in
  (if not (modular ()) then repeat (List.length s) pop_visible ());
  p

let pp_struct s = do_struct pp_structure_elem s

let pp_signature s = do_struct pp_specif s

let pp_decl d = try pp_decl d with Failure "empty phrase" -> mt ()

let ocaml_descr = {
  keywords = keywords;
  file_suffix = ".ml";
  preamble = preamble;
  pp_struct = pp_struct;
  sig_suffix = Some ".mli";
  sig_preamble = sig_preamble;
  pp_sig = pp_signature;
  pp_decl = pp_decl;
}


