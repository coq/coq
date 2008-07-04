(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(*i*)
open Names
open Decl_kinds
open Term
open Sign
open Evd
open Environ
open Nametab
open Mod_subst
open Util
open Rawterm
open Topconstr
open Libnames
open Typeclasses
open Typeclasses_errors
open Pp
(*i*)

let ids_of_list l = 
  List.fold_right Idset.add l Idset.empty

let locate_reference qid =
  match Nametab.extended_locate qid with
    | TrueGlobal ref -> true
    | SyntacticDef kn -> true

let is_global id =
  try 
    locate_reference (make_short_qualid id)
  with Not_found -> 
    false

let is_freevar ids env x =
  try
    if Idset.mem x ids then false
    else
      try ignore(Environ.lookup_named x env) ; false
      with _ -> not (is_global x)
  with _ -> true

(* Auxilliary functions for the inference of implicitly quantified variables. *)    

let free_vars_of_constr_expr c ?(bound=Idset.empty) l = 
  let found id bdvars l = 
    if List.mem id l then l 
    else if not (is_freevar bdvars (Global.env ()) id)
    then l else id :: l 
  in
  let rec aux bdvars l c = match c with
    | CRef (Ident (_,id)) -> found id bdvars l
    | CNotation (_, "{ _ : _ | _ }", (CRef (Ident (_, id))) :: _) when not (Idset.mem id bdvars) ->
	fold_constr_expr_with_binders (fun a l -> Idset.add a l) aux (Idset.add id bdvars) l c
    | c -> fold_constr_expr_with_binders (fun a l -> Idset.add a l) aux bdvars l c
  in aux bound l c

let ids_of_names l = 
  List.fold_left (fun acc x -> match snd x with Name na -> na :: acc | Anonymous -> acc) [] l

let free_vars_of_binders ?(bound=Idset.empty) l (binders : local_binder list) = 
  let rec aux bdvars l c = match c with
      ((LocalRawAssum (n, _, c)) :: tl) ->
	let bound = ids_of_names n in
	let l' = free_vars_of_constr_expr c ~bound:bdvars l in
	  aux (Idset.union (ids_of_list bound) bdvars) l' tl

    | ((LocalRawDef (n, c)) :: tl) -> 
	let bound = match snd n with Anonymous -> [] | Name n -> [n] in
	let l' = free_vars_of_constr_expr c ~bound:bdvars l in
	  aux (Idset.union (ids_of_list bound) bdvars) l' tl
	
    | [] -> bdvars, l
  in aux bound l binders

let rec make_fresh ids env x =
  if is_freevar ids env x then x else make_fresh ids env (Nameops.lift_ident x)

let freevars_of_ids env ids = 
  List.filter (is_freevar env (Global.env())) ids

let binder_list_of_ids ids =
  List.map (fun id -> LocalRawAssum ([dummy_loc, Name id], Default Implicit, CHole (dummy_loc, None))) ids
      
let next_ident_away_from id avoid = make_fresh avoid (Global.env ()) id
    
let combine_params avoid fn applied needed =
  let named, applied = 
    List.partition 
      (function
	  (t, Some (loc, ExplByName id)) -> 
	    if not (List.exists (fun (_, (id', _, _)) -> Name id = id') needed) then
	      user_err_loc (loc,"",str "Wrong argument name: " ++ Nameops.pr_id id);
	    true
	| _ -> false) applied
  in
  let named = List.map
    (fun x -> match x with (t, Some (loc, ExplByName id)) -> id, t | _ -> assert false)
    named
  in
  let rec aux ids avoid app need =
    match app, need with
	[], [] -> List.rev ids, avoid

      | app, (_, (Name id, _, _)) :: need when List.mem_assoc id named ->
	  aux (List.assoc id named :: ids) avoid app need
	    
      | (x, None) :: app, (None, (Name id, _, _)) :: need ->
	  aux (x :: ids) avoid app need
	    
      | _, (Some cl, (Name id, _, _) as d) :: need -> 
	  let t', avoid' = fn avoid d in
	    aux (t' :: ids) avoid' app need

      | x :: app, (None, _) :: need -> aux (fst x :: ids) avoid app need

      | [], (None, _ as decl) :: need -> 
	  let t', avoid' = fn avoid decl in
	    aux (t' :: ids) avoid' app need

      | _ :: _, [] -> failwith "combine_params: overly applied typeclass"

      | _, _ -> raise (Invalid_argument "combine_params")
  in aux [] avoid applied needed

let combine_params_freevar avoid applied needed =
  combine_params avoid
    (fun avoid (_, (id, _, _)) -> 
      let id' = next_ident_away_from (Nameops.out_name id) avoid in
	(CRef (Ident (dummy_loc, id')), Idset.add id' avoid))
    applied needed

let compute_context_vars env l =
  List.fold_left (fun avoid (iid, _, c) -> 
    (match snd iid with Name i -> [i] | Anonymous -> []) @ (free_vars_of_constr_expr c ~bound:env avoid))
    [] l

let destClassApp cl =
  match cl with
    | CApp (loc, (None,CRef ref), l) -> loc, ref, List.map fst l
    | CRef ref -> loc_of_reference ref, ref, []
    | _ -> raise Not_found
      
let destClassAppExpl cl =
  match cl with
    | CApp (loc, (None,CRef ref), l) -> loc, ref, l
    | CRef ref -> loc_of_reference ref, ref, []
    | _ -> raise Not_found

let full_class_binders env l = 
  let avoid = Idset.union env (ids_of_list (compute_context_vars env l)) in
  let l', avoid =
    List.fold_left (fun (l', avoid) (iid, bk, cl as x) -> 
      match bk with
	  Implicit -> 
	    let (loc, id, l) = 
	      try destClassAppExpl cl 
	      with Not_found -> 
		user_err_loc (constr_loc cl, "class_binders", str"Not an applied type class")
	    in
	    let gr = Nametab.global id in
	      (try
		  let c = class_info gr in
		  let args, avoid = combine_params_freevar avoid l (List.rev c.cl_context) in
		    (iid, bk, CAppExpl (loc, (None, id), args)) :: l', avoid
		with Not_found -> not_a_class (Global.env ()) (constr_of_global gr))
	| Explicit -> (x :: l', avoid))
      ([], avoid) l
  in List.rev l'

let compute_context_freevars env ctx =
  let bound, ids = 
    List.fold_left 
      (fun (bound, acc) (oid, id, x) -> 
	let bound = match snd oid with Name n -> Idset.add n bound | Anonymous -> bound in
	  bound, free_vars_of_constr_expr x ~bound acc)
      (env,[]) ctx
  in freevars_of_ids env (List.rev ids)

let resolve_class_binders env l = 
  let ctx = full_class_binders env l in
  let fv_ctx = 
    let elts = compute_context_freevars env ctx in
      List.map (fun id -> (dummy_loc, id), CHole (dummy_loc, None)) elts
  in
    fv_ctx, ctx

let full_class_binder env (iid, (bk, bk'), cl as c) = 
  let avoid = Idset.union env (ids_of_list (compute_context_vars env [c])) in
  let c, avoid =
    match bk' with
    | Implicit -> 
	let (loc, id, l) = 
	  try destClassAppExpl cl 
	  with Not_found -> 
	    user_err_loc (constr_loc cl, "class_binders", str"Not an applied type class")
	in
	let gr = Nametab.global id in
	  (try
	      let c = class_info gr in
	      let args, avoid = combine_params_freevar avoid l (List.rev c.cl_context) in
		(iid, bk, CAppExpl (loc, (None, id), args)), avoid
	    with Not_found -> not_a_class (Global.env ()) (constr_of_global gr))
    | Explicit -> ((iid,bk,cl), avoid)
  in c

let compute_constraint_freevars env (oid, _, x) =
  let bound = match snd oid with Name n -> Idset.add n env | Anonymous -> env in
  let ids = free_vars_of_constr_expr x ~bound [] in
    freevars_of_ids env (List.rev ids)

let resolve_class_binder env c = 
  let cstr = full_class_binder env c in
  let fv_ctx = 
    let elts = compute_constraint_freevars env cstr in
      List.map (fun id -> (dummy_loc, id), CHole (dummy_loc, None)) elts
  in fv_ctx, cstr
    
let generalize_class_binder_raw env c = 
  let env = Idset.union env (Termops.vars_of_env (Global.env())) in
  let fv_ctx, cstr = resolve_class_binder env c in
  let ids' = List.fold_left (fun acc ((loc, id), t) -> Idset.add id acc) env fv_ctx in
  let ctx' = List.map (fun ((loc, id), t) -> ((loc, Name id), Implicit, t)) fv_ctx in
    ids', ctx', cstr

let generalize_class_binders_raw env l = 
  let env = Idset.union env (Termops.vars_of_env (Global.env())) in
  let fv_ctx, cstrs = resolve_class_binders env l in
    List.map (fun ((loc, id), t) -> ((loc, Name id), Implicit, t)) fv_ctx,
  List.map (fun (iid, bk, c) -> (iid, Implicit, c)) cstrs
	
let implicits_of_rawterm l = 
  let rec aux i c = 
    match c with
	RProd (loc, na, bk, t, b) | RLambda (loc, na, bk, t, b) -> 
	  let rest = aux (succ i) b in
	    if bk = Implicit then
	      let name =
		match na with
		    Name id -> Some id
		  | Anonymous -> None
	      in
		(ExplByPos (i, name), (true, true)) :: rest
	    else rest
      | RLetIn (loc, na, t, b) -> aux i b
      | _ -> []
  in aux 1 l
