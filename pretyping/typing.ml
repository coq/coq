(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Util
open Names
open Term
open Environ
open Reductionops
open Type_errors
open Pretype_errors
open Inductive
open Inductiveops
open Typeops
open Evd

let meta_type evd mv =
  let ty =
    try Evd.meta_ftype evd mv
    with Not_found -> anomaly ("unknown meta ?"^Nameops.string_of_meta mv) in
  meta_instance evd ty

let constant_type_knowing_parameters env cst jl =
  let paramstyp = Array.map (fun j -> j.uj_type) jl in
  type_of_constant_knowing_parameters env (constant_type env cst) paramstyp

let inductive_type_knowing_parameters env ind jl =
  let (mib,mip) = lookup_mind_specif env ind in
  let paramstyp = Array.map (fun j -> j.uj_type) jl in
  Inductive.type_of_inductive_knowing_parameters env mip paramstyp

(* The typing machine without information, without universes but with
   existential variables. *)

(* cstr must be in n.f. w.r.t. evars and execute returns a judgement
   where both the term and type are in n.f. *)
let rec execute env evd cstr =
  match kind_of_term cstr with
    | Meta n ->
        { uj_val = cstr; uj_type = nf_evar (evars_of evd) (meta_type evd n) }

    | Evar ev ->
        let sigma = Evd.evars_of evd in
	let ty = Evd.existential_type sigma ev in
	let jty = execute env evd (nf_evar (evars_of evd) ty) in
	let jty = assumption_of_judgment env jty in
	{ uj_val = cstr; uj_type = jty }
	
    | Rel n -> 
	j_nf_evar (evars_of evd) (judge_of_relative env n)

    | Var id -> 
        j_nf_evar (evars_of evd) (judge_of_variable env id)
	  
    | Const c ->
        make_judge cstr (nf_evar (evars_of evd) (type_of_constant env c))
	  
    | Ind ind ->
	make_judge cstr (nf_evar (evars_of evd) (type_of_inductive env ind))
	  
    | Construct cstruct -> 
	make_judge cstr
          (nf_evar (evars_of evd) (type_of_constructor env cstruct))

    | Case (ci,p,c,lf) ->
        let cj = execute env evd c in
        let pj = execute env evd p in
        let lfj = execute_array env evd lf in
        let (j,_) = judge_of_case env ci pj cj lfj in
        j
  
    | Fix ((vn,i as vni),recdef) ->
        let (_,tys,_ as recdef') = execute_recdef env evd recdef in
	let fix = (vni,recdef') in
        check_fix env fix;
	make_judge (mkFix fix) tys.(i)
	  
    | CoFix (i,recdef) ->
        let (_,tys,_ as recdef') = execute_recdef env evd recdef in
        let cofix = (i,recdef') in
        check_cofix env cofix;
	make_judge (mkCoFix cofix) tys.(i)
	  
    | Sort (Prop c) -> 
	judge_of_prop_contents c

    | Sort (Type u) ->
	judge_of_type u
	  
    | App (f,args) ->
        let jl = execute_array env evd args in
	let j =
	  match kind_of_term f with
	    | Ind ind ->
		(* Sort-polymorphism of inductive types *)
		make_judge f
		  (inductive_type_knowing_parameters env ind
		    (jv_nf_evar (evars_of evd) jl))
	    | Const cst -> 
		(* Sort-polymorphism of inductive types *)
		make_judge f
		  (constant_type_knowing_parameters env cst
		    (jv_nf_evar (evars_of evd) jl))
	    | _ -> 
		execute env evd f
	in
	fst (judge_of_apply env j jl)
	    
    | Lambda (name,c1,c2) -> 
        let j = execute env evd c1 in
	let var = type_judgment env j in
	let env1 = push_rel (name,None,var.utj_val) env in
        let j' = execute env1 evd c2 in 
        judge_of_abstraction env1 name var j'
	  
    | Prod (name,c1,c2) ->
        let j = execute env evd c1 in
        let varj = type_judgment env j in
	let env1 = push_rel (name,None,varj.utj_val) env in
        let j' = execute env1 evd c2 in
        let varj' = type_judgment env1 j' in
	judge_of_product env name varj varj'

     | LetIn (name,c1,c2,c3) ->
        let j1 = execute env evd c1 in
        let j2 = execute env evd c2 in
        let j2 = type_judgment env j2 in
        let _ =  judge_of_cast env j1 DEFAULTcast j2 in
        let env1 = push_rel (name,Some j1.uj_val,j2.utj_val) env in
        let j3 = execute env1 evd c3 in
        judge_of_letin env name j1 j2 j3
  
    | Cast (c,k,t) ->
        let cj = execute env evd c in
        let tj = execute env evd t in
	let tj = type_judgment env tj in
        let j, _ = judge_of_cast env cj k tj in
	j

and execute_recdef env evd (names,lar,vdef) =
  let larj = execute_array env evd lar in
  let lara = Array.map (assumption_of_judgment env) larj in
  let env1 = push_rec_types (names,lara,vdef) env in
  let vdefj = execute_array env1 evd vdef in
  let vdefv = Array.map j_val vdefj in
  let _ = type_fixpoint env1 names lara vdefj in
  (names,lara,vdefv)

and execute_array env evd = Array.map (execute env evd)

and execute_list env evd = List.map (execute env evd)

let mcheck env evd c t =
  let sigma = Evd.evars_of evd in
  let j = execute env evd (nf_evar sigma c) in
  if not (is_conv_leq env sigma j.uj_type t) then
    error_actual_type env j (nf_evar sigma t)

(* Type of a constr *)
 
let mtype_of env evd c =
  let j = execute env evd (nf_evar (evars_of evd) c) in
  (* We are outside the kernel: we take fresh universes *)
  (* to avoid tactics and co to refresh universes themselves *)
  Termops.refresh_universes j.uj_type

let msort_of env evd c =
  let j = execute env evd (nf_evar (evars_of evd) c) in
  let a = type_judgment env j in
  a.utj_type

let type_of env sigma c =
  mtype_of env (Evd.create_evar_defs sigma) c
let sort_of env sigma c =
  msort_of env (Evd.create_evar_defs sigma) c
let check env sigma c   =
  mcheck env (Evd.create_evar_defs sigma) c

(* The typed type of a judgment. *)

let mtype_of_type env evd constr =
  let j = execute env evd (nf_evar (evars_of evd) constr) in
  assumption_of_judgment env j
