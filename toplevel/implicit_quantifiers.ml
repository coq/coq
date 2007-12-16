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
open Topconstr
open Libnames
open Typeclasses
open Typeclasses_errors
(*i*)

(* Auxilliary functions for the inference of implicitly quantified variables. *)    

let free_vars_of_constr_expr c ?(bound=[]) l = 
  let rec aux bdvars l = function
  | CRef (Ident (_,id)) -> if List.mem id bdvars then l else if List.mem id l then l else id :: l
  | c -> fold_constr_expr_with_binders (fun a l -> a::l) aux bdvars l c
  in aux bound l c

let is_freevar env x =
  try
    try ignore(Environ.lookup_named x env) ; false
    with _ ->
      ignore(Constrintern.global_reference x); false 
  with _ -> true

let freevars_of_ids env ids = 
  List.filter (is_freevar env) ids

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
      
let ids_of_named_context_avoiding avoid l =
  List.fold_left (fun (ids, avoid) id -> 
    let id' = Nameops.next_ident_away_from id avoid in id' :: ids, id' :: avoid) 
    ([], avoid) (Termops.ids_of_named_context l)
    
let combine_params avoid applied needed =
  let rec aux ids app need =
    match app, need with
	[], need -> 
	  let need', avoid = ids_of_named_context_avoiding avoid need in
	    List.rev ids @ (List.map mkIdentC need'), avoid
      | x :: app, _ :: need -> aux (x :: ids) app need    
      | _ :: _, [] -> failwith "combine_params: overly applied typeclass"
  in aux [] applied needed

let compute_context_vars env l =
  List.fold_right (fun (iid, (_,id), l) ids -> 
    (match snd iid with Name i -> [i] | Anonymous -> []) @ compute_constrs_freevars env l)
    l []

let full_class_binders env l = 
  let avoid = compute_context_vars env l in
  let l', avoid =
    List.fold_left (fun (l', avoid) (iid, (bk,id), l as x) -> 
      match bk with
	  Explicit -> 
	    (try 
		let c = class_info (snd id) in
		let args, avoid = combine_params avoid l (List.rev c.cl_context @ List.rev c.cl_super @ List.rev c.cl_params) in
		  (iid, (bk,id), args) :: l', avoid
	      with Not_found -> unbound_class env id)
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
	let bound = match snd oid with Name n -> n :: bound | Anonymous -> bound in
	  List.fold_left (fun (bound, acc) x -> bound, free_vars_of_constr_expr x ~bound acc) 
	    (bound, acc) x)
      ([],[]) ctx
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
    List.map (fun ((loc, id), t) -> LocalRawAssum ([loc, Name id], Implicit, t)) fv_ctx,
  List.map (fun (iid, id, c) -> LocalRawAssum ([iid], Implicit, constr_expr_of_constraint id c)) 
    cstrs

let ctx_of_class_binders env l = 
  let (x, y) = generalize_class_binders env l in x @ y
	
let implicits_of_binders l = 
  let rec aux i l = 
    match l with 
	[] -> []
      | hd :: tl -> 
	  let res, reslen = 
	    match hd with
		LocalRawAssum (nal, Implicit, t) -> 
		  list_map_i (fun i (_,id) ->
		    let name =
		      match id with
			  Name id -> Some id
			| Anonymous -> None
		    in ExplByPos (i, name), (true, true))
		    i nal, List.length nal
	      | LocalRawAssum (nal, Explicit, _) -> [], List.length nal
	      | LocalRawDef _ -> [], 1
	  in res @ (aux (i + reslen) tl)
  in aux 1 l
  
let nf_named_context sigma ctx = 
  Sign.map_named_context (Reductionops.nf_evar sigma) ctx

let nf_rel_context sigma ctx = 
  Sign.map_rel_context (Reductionops.nf_evar sigma) ctx
    
let nf_env sigma env = 
  let nc' = nf_named_context sigma (Environ.named_context env) in
  let rel' = nf_rel_context sigma (Environ.rel_context env) in
    push_rel_context rel' (reset_with_named_context (val_of_named_context nc') env)

type substitution = (identifier * constr) list

let substitution_of_named_context isevars env id n subst l = 
  List.fold_right
    (fun (na, _, t) subst -> 
      let t' = replace_vars subst t in
      let b = Evarutil.e_new_evar isevars env ~src:(dummy_loc, ImplicitArg (VarRef id, (n, Some na))) t' in
	(na, b) :: subst)
    l subst

let nf_substitution sigma subst = 
  List.map (function (na, c) -> na, Reductionops.nf_evar sigma c) subst
