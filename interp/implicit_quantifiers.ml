(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id: classes.ml 6748 2005-02-18 22:17:50Z herbelin $ i*)

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
(*i*)

(* Auxilliary functions for the inference of implicitly quantified variables. *)    

let free_vars_of_constr_expr c ?(bound=Idset.empty) l = 
  let found id bdvars l = if Idset.mem id bdvars then l else if List.mem id l then l else id :: l in
  let rec aux bdvars l c = match c with
    | CRef (Ident (_,id)) -> found id bdvars l
    | CNotation (_, "{ _ : _ | _ }", (CRef (Ident (_, id))) :: _) when not (Idset.mem id bdvars) ->
	fold_constr_expr_with_binders (fun a l -> Idset.add a l) aux (Idset.add id bdvars) l c
    | c -> fold_constr_expr_with_binders (fun a l -> Idset.add a l) aux bdvars l c
  in aux bound l c


let locate_reference qid =
  match Nametab.extended_locate qid with
    | TrueGlobal ref -> ref
    | SyntacticDef kn -> 
	match Syntax_def.search_syntactic_definition dummy_loc kn with
	  | Rawterm.RRef (_,ref) -> ref
	  | _ -> raise Not_found

let is_global id =
  try 
    let _ = locate_reference (make_short_qualid id) in true
  with Not_found -> 
    false

let is_freevar ids env x =
  try
    if Idset.mem x ids then false
    else
      try ignore(Environ.lookup_named x env) ; false
      with _ -> not (is_global x)
  with _ -> true

let rec make_fresh ids env x =
  if is_freevar ids env x then x else make_fresh ids env (Nameops.lift_ident x)

let freevars_of_ids env ids = 
  List.filter (is_freevar env (Global.env())) ids

let compute_constrs_freevars env constrs =
  let ids = 
    List.rev (List.fold_left 
		 (fun acc x -> free_vars_of_constr_expr x acc) 
		 [] constrs)
  in freevars_of_ids env ids

(* let compute_context_freevars env ctx = *)
(*   let ids = *)
(*     List.rev *)
(*       (List.fold_left *)
(* 	  (fun acc (_,i,x) -> free_vars_of_constr_expr x acc) *)
(* 	  [] constrs) *)
(*   in freevars_of_ids ids *)

let compute_constrs_freevars_binders env constrs =
  let elts = compute_constrs_freevars env constrs in
    List.map (fun id -> (dummy_loc, id), CHole dummy_loc) elts
      
let next_ident_away_from id avoid = make_fresh avoid (Global.env ()) id
(*   let rec name_rec id = *)
(*     if Idset.mem id avoid then name_rec (Nameops.lift_ident id) else id in  *)
(*   name_rec id  *)

let ids_of_named_context_avoiding avoid l =
  List.fold_left (fun (ids, avoid) id -> 
    let id' = next_ident_away_from id avoid in id' :: ids, Idset.add id' avoid) 
    ([], avoid) (Termops.ids_of_named_context l)
    
let combine_params avoid applied needed =
  let rec aux ids avoid app need =
    match app, need with
	[], need -> 
	  let need', avoid = ids_of_named_context_avoiding avoid (List.map snd need) in
	    List.rev ids @ (List.rev_map mkIdentC need'), avoid
      | _, (true, (id, _, _)) :: need -> 
	  let id' = next_ident_away_from id avoid in
	    aux (CRef (Ident (dummy_loc, id')) :: ids) (Idset.add id' avoid) app need
      | x :: app, (false, _) :: need -> aux (x :: ids) avoid app need    
      | _ :: _, [] -> failwith "combine_params: overly applied typeclass"
  in aux [] avoid applied needed

let compute_context_vars env l =
  List.fold_left (fun avoid (iid, _, c) -> 
    (match snd iid with Name i -> [i] | Anonymous -> []) @ (free_vars_of_constr_expr c ~bound:env avoid))
    [] l

let destClassApp cl =
  match cl with
    | CApp (loc, (None,CRef (Ident f)), l) -> f, List.map fst l
    | _ -> raise Not_found

let ids_of_list l = 
  List.fold_right Idset.add l Idset.empty

let full_class_binders env l = 
  let avoid = Idset.union env (ids_of_list (compute_context_vars env l)) in
  let l', avoid =
    List.fold_left (fun (l', avoid) (iid, bk, cl as x) -> 
      match bk with
	  Explicit -> 
	    let (id, l) = destClassApp cl in
	      (try
		  let c = class_info (snd id) in
		  let args, avoid = combine_params avoid l 
		    (List.rev_map (fun x -> false, x) c.cl_context @ 
			List.rev_map (fun x -> true, x) c.cl_super @ 
			List.rev_map (fun x -> false, x) c.cl_params) 
		  in
		    (iid, bk, CAppExpl (fst id, (None, Ident id), args)) :: l', avoid
		with Not_found -> unbound_class (Global.env ()) id)
	| Implicit -> (x :: l', avoid))
      ([], avoid) l
  in List.rev l'
      
let constr_expr_of_constraint (kind, id) l =
  match kind with
    | Explicit -> CAppExpl (fst id, (None, Ident id), l)
    | Implicit -> CApp (fst id, (None, CRef (Ident id)),
		       List.map (fun x -> x, None) l)

(*    | CApp of loc * (proj_flag * constr_expr) *  *)
(*         (constr_expr * explicitation located option) list *)


let constrs_of_context l =
  List.map (fun (_, id, l) -> constr_expr_of_constraint id l) l

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
      List.map (fun id -> (dummy_loc, id), CHole dummy_loc) elts
  in
    fv_ctx, ctx

let generalize_class_binders env l = 
  let fv_ctx, cstrs = resolve_class_binders env l in
    List.map (fun ((loc, id), t) -> LocalRawAssum ([loc, Name id], Default Implicit, t)) fv_ctx,
  List.map (fun (iid, bk, c) -> LocalRawAssum ([iid], Default Implicit, c)) 
    cstrs

let generalize_class_binders_raw env l = 
  let env = Idset.union env (Termops.vars_of_env (Global.env())) in
  let fv_ctx, cstrs = resolve_class_binders env l in
    List.map (fun ((loc, id), t) -> ((loc, Name id), Implicit, t)) fv_ctx,
  List.map (fun (iid, bk, c) -> (iid, Implicit, c)) cstrs

let ctx_of_class_binders env l = 
  let (x, y) = generalize_class_binders env l in x @ y
	
let implicits_of_binders l = 
  let rec aux i l = 
    match l with 
	[] -> []
      | hd :: tl -> 
	  let res, reslen = 
	    match hd with
		LocalRawAssum (nal, Default Implicit, t) -> 
		  list_map_i (fun i (_,id) ->
		    let name =
		      match id with
			  Name id -> Some id
			| Anonymous -> None
		    in ExplByPos (i, name), (true, true))
		    i nal, List.length nal
	      | LocalRawAssum (nal, _, _) -> [], List.length nal
	      | LocalRawDef _ -> [], 1
	  in res @ (aux (i + reslen) tl)
  in aux 1 l
  
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

let nf_named_context sigma ctx = 
  Sign.map_named_context (Reductionops.nf_evar sigma) ctx

let nf_rel_context sigma ctx = 
  Sign.map_rel_context (Reductionops.nf_evar sigma) ctx
    
let nf_env sigma env = 
  let nc' = nf_named_context sigma (Environ.named_context env) in
  let rel' = nf_rel_context sigma (Environ.rel_context env) in
    push_rel_context rel' (reset_with_named_context (val_of_named_context nc') env)
