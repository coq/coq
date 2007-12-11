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

let free_vars_of_constr_expr c l = 
  let rec aux bdvars l = function
  | CRef (Ident (_,id)) -> if List.mem id bdvars then l else if List.mem id l then l else id :: l
  | c -> fold_constr_expr_with_binders (fun a l -> a::l) aux bdvars l c
  in aux [] l c

let compute_constrs_freevars env constrs =
  let ids = 
    List.rev (List.fold_left 
		 (fun acc x -> free_vars_of_constr_expr x acc) 
		 [] constrs)
  in
    List.filter (fun x -> try
	try ignore(Environ.lookup_named x env) ; false
	with _ ->
	  ignore(Constrintern.global_reference x); false 
      with _ -> true) ids

let compute_constrs_freevars_binders env constrs =
  let elts = compute_constrs_freevars env constrs in
    List.map (fun id -> (dummy_loc, id), CHole dummy_loc) elts
      
let ids_of_named_context_avoiding avoid l =
  let (ids, avoid) =
    List.fold_left (fun (ids, avoid) id -> 
      let id' = Nameops.next_ident_away_from id avoid in id' :: ids, id' :: avoid) 
      ([], avoid) (Termops.ids_of_named_context l)
  in List.rev ids

let combine_params avoid applied needed =
  let rec aux ids app need =
    match app, need with
	[], need -> List.rev ids @ 
	  (List.map mkIdentC (ids_of_named_context_avoiding avoid need))
      | x :: app, _ :: need -> aux (x :: ids) app need    
      | _ :: _, [] -> failwith "combine_params: overly applied typeclass"
  in aux [] applied needed

type typeclass_context = (identifier located * constr_expr list) list

let resolve_class_binders env l = 
  let avoid = compute_constrs_freevars env (List.concat (List.map (fun ((_,id), l) -> l) l)) in
  let cstrs = List.map (fun (id, l) -> 
    let c = class_info (snd id) in
    let args = combine_params avoid l (c.cl_params @ c.cl_super) in
      mkAppC (CRef (Ident id), args)) l 
  in
  let fv_ctx = compute_constrs_freevars_binders env cstrs in
    fv_ctx, cstrs

let ctx_of_class_binders env l = 
  let fv_ctx, cstrs = resolve_class_binders env l in
    List.map (fun ((loc, id), t) -> LocalRawAssum ([loc, Name id], Implicit, t)) fv_ctx @ 
      List.map (fun c -> LocalRawAssum ([dummy_loc, Anonymous], Implicit, c)) cstrs
	
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
