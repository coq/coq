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
open Typeops

let vect_lift = Array.mapi lift
let vect_lift_type = Array.mapi (fun i t -> type_app (lift i) t)

(* The typing machine without information, without universes but with
   existential variables. *)

let assumption_of_judgment env evd j =
  assumption_of_judgment env (j_nf_evar (Evd.evars_of evd) j)

let type_judgment env evd j =
  type_judgment env (j_nf_evar (Evd.evars_of evd) j)

let check_type env evd j ty =
  let sigma = Evd.evars_of evd in
  if not (is_conv_leq env sigma j.uj_type ty) then
    error_actual_type env (j_nf_evar sigma j) (nf_evar sigma ty)

let rec execute env evd cstr =
  match kind_of_term cstr with
    | Meta n ->
        { uj_val = cstr; uj_type = Evarutil.meta_type evd n }

    | Evar ev ->
        let sigma = Evd.evars_of evd in
	let ty = Evd.existential_type sigma ev in
	let jty = execute env evd ty in
	let jty = assumption_of_judgment env evd jty in
	{ uj_val = cstr; uj_type = jty }
	
    | Rel n -> 
	judge_of_relative env n

    | Var id -> 
        judge_of_variable env id
	  
    | Const c ->
        make_judge cstr (constant_type env c)
	  
    | Ind ind ->
	make_judge cstr (type_of_inductive env ind)
	  
    | Construct cstruct -> 
	make_judge cstr (type_of_constructor env cstruct)
	  
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
	let j = execute env evd f in
        let jl = execute_array env evd args in
	let (j,_) = judge_of_apply env j jl in
	j
	    
    | Lambda (name,c1,c2) -> 
        let j = execute env evd c1 in
	let var = type_judgment env evd j in
	let env1 = push_rel (name,None,var.utj_val) env in
        let j' = execute env1 evd c2 in 
        judge_of_abstraction env1 name var j'
	  
    | Prod (name,c1,c2) ->
        let j = execute env evd c1 in
        let varj = type_judgment env evd j in
	let env1 = push_rel (name,None,varj.utj_val) env in
        let j' = execute env1 evd c2 in
        let varj' = type_judgment env1 evd j' in
	judge_of_product env name varj varj'

     | LetIn (name,c1,c2,c3) ->
        let j1 = execute env evd c1 in
        let j2 = execute env evd c2 in
        let j2 = type_judgment env evd j2 in
        let _ =  judge_of_cast env j1 j2 in
        let env1 = push_rel (name,Some j1.uj_val,j2.utj_val) env in
        let j3 = execute env1 evd c3 in
        judge_of_letin env name j1 j2 j3
  
    | Cast (c,t) ->
        let cj = execute env evd c in
        let tj = execute env evd t in
	let tj = type_judgment env evd tj in
        let j, _ = judge_of_cast env cj tj in
	j

and execute_recdef env evd (names,lar,vdef) =
  let larj = execute_array env evd lar in
  let lara = Array.map (assumption_of_judgment env evd) larj in
  let env1 = push_rec_types (names,lara,vdef) env in
  let vdefj = execute_array env1 evd vdef in
  let vdefv = Array.map j_val vdefj in
  let _ = type_fixpoint env1 names lara vdefj in
  (names,lara,vdefv)

and execute_array env evd v =
  let jl = execute_list env evd (Array.to_list v) in
  Array.of_list jl

and execute_list env evd = function
  | [] -> 
      []
  | c::r -> 
      let j = execute env evd c in 
      let jr = execute_list env evd r in
      j::jr

let mcheck env evd c t =
  let j = execute env evd c in
  check_type env evd j t

(* Type of a constr *)
 
let mtype_of env evd c =
  let j = execute env evd c in
  (* No normalization: it breaks Pattern! *)
  (*nf_betaiota*) (body_of_type j.uj_type)

let msort_of env evd c =
  let j = execute env evd c in
  let a = type_judgment env evd j in
  a.utj_type

let type_of env sigma c =
  mtype_of env (Evd.create_evar_defs sigma) c
let sort_of env sigma c =
  msort_of env (Evd.create_evar_defs sigma) c
let check env sigma c   =
  mcheck env (Evd.create_evar_defs sigma) c

(* The typed type of a judgment. *)

let mtype_of_type env evd constr =
  let j = execute env evd constr in
  assumption_of_judgment env evd j
