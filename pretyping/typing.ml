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

type 'a mach_flags = {
  fix : bool;
  nocheck : bool }

(* The typing machine without information, without universes but with
   existential variables. *)

let assumption_of_judgment env sigma j =
  assumption_of_judgment env (j_nf_evar sigma j)

let type_judgment env sigma j =
  type_judgment env (j_nf_evar sigma j)


let rec execute mf env sigma cstr =
  match kind_of_term cstr with
    | Meta n ->
	error "execute: found a non-instanciated goal"

    | Evar ev ->
	let ty = Instantiate.existential_type sigma ev in
	let jty = execute mf env sigma ty in
	let jty = assumption_of_judgment env sigma jty in
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
        let cj = execute mf env sigma c in
        let pj = execute mf env sigma p in
        let lfj = execute_array mf env sigma lf in
        let (j,_) = judge_of_case env ci pj cj lfj in
        j
  
    | Fix ((vn,i as vni),recdef) ->
        if (not mf.fix) && array_exists (fun n -> n < 0) vn then
          error "General Fixpoints not allowed";
        let (_,tys,_ as recdef') = execute_recdef mf env sigma recdef in
	let fix = (vni,recdef') in
        check_fix env fix;
	make_judge (mkFix fix) tys.(i)
	  
    | CoFix (i,recdef) ->
        let (_,tys,_ as recdef') = execute_recdef mf env sigma recdef in
        let cofix = (i,recdef') in
        check_cofix env cofix;
	make_judge (mkCoFix cofix) tys.(i)
	  
    | Sort (Prop c) -> 
	judge_of_prop_contents c

    | Sort (Type u) ->
	judge_of_type u
	  
    | App (f,args) ->
	let j = execute mf env sigma f in
        let jl = execute_array mf env sigma args in
	let (j,_) = judge_of_apply env j jl in
	j
	    
    | Lambda (name,c1,c2) -> 
        let j = execute mf env sigma c1 in
	let var = type_judgment env sigma j in
	let env1 = push_rel (name,None,var.utj_val) env in
        let j' = execute mf env1 sigma c2 in 
        judge_of_abstraction env1 name var j'
	  
    | Prod (name,c1,c2) ->
        let j = execute mf env sigma c1 in
        let varj = type_judgment env sigma j in
	let env1 = push_rel (name,None,varj.utj_val) env in
        let j' = execute mf env1 sigma c2 in
        let varj' = type_judgment env1 sigma j' in
	judge_of_product env name varj varj'

     | LetIn (name,c1,c2,c3) ->
        let j1 = execute mf env sigma c1 in
        let j2 = execute mf env sigma c2 in
        let j2 = type_judgment env sigma j2 in
        let _ =  judge_of_cast env j1 j2 in
        let env1 = push_rel (name,Some j1.uj_val,j2.utj_val) env in
        let j3 = execute mf env1 sigma c3 in
        judge_of_letin env name j1 j2 j3
  
    | Cast (c,t) ->
        let cj = execute mf env sigma c in
        let tj = execute mf env sigma t in
	let tj = type_judgment env sigma tj in
        let j, _ = judge_of_cast env cj tj in
	j

and execute_recdef mf env sigma (names,lar,vdef) =
  let larj = execute_array mf env sigma lar in
  let lara = Array.map (assumption_of_judgment env sigma) larj in
  let env1 = push_rec_types (names,lara,vdef) env in
  let vdefj = execute_array mf env1 sigma vdef in
  let vdefv = Array.map j_val vdefj in
  let _ = type_fixpoint env1 names lara vdefj in
  (names,lara,vdefv)

and execute_array mf env sigma v =
  let jl = execute_list mf env sigma (Array.to_list v) in
  Array.of_list jl

and execute_list mf env sigma = function
  | [] -> 
      []
  | c::r -> 
      let j = execute mf env sigma c in 
      let jr = execute_list mf env sigma r in
      j::jr


let safe_machine env sigma constr = 
  let mf = { fix = false; nocheck = false } in
  execute mf env sigma constr

let unsafe_machine env sigma constr =
  let mf = { fix = false; nocheck = true } in
  execute mf env sigma constr

(* Type of a constr *)

let type_of env sigma c = 
  let j = safe_machine env sigma c in 
  (* No normalization: it breaks Pattern! *)
  (*nf_betaiota*) (body_of_type j.uj_type)

(* The typed type of a judgment. *)

let execute_type env sigma constr = 
  let j = execute { fix=false; nocheck=true } env sigma constr in
  assumption_of_judgment env sigma j

let execute_rec_type env sigma constr = 
  let j = execute { fix=false; nocheck=false } env sigma constr in
  assumption_of_judgment env sigma j

