(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Util
open Names
open Term
open Environ
open Reduction
open Type_errors
open Typeops

let vect_lift = Array.mapi lift
let vect_lift_type = Array.mapi (fun i t -> type_app (lift i) t)

type 'a mach_flags = {
  fix : bool;
  nocheck : bool }

(* The typing machine without information, without universes but with
   existential variables. *)

let rec execute mf env sigma cstr =
  match kind_of_term cstr with
    | IsMeta n ->
	error "execute: found a non-instanciated goal"

    | IsEvar ev ->
	let ty = type_of_existential env sigma ev in
	let jty = execute mf env sigma ty in
	let jty = assumption_of_judgment env sigma jty in
	{ uj_val = cstr; uj_type = jty }
	
    | IsRel n -> 
	relative env n

    | IsVar id -> 
      (try
         make_judge cstr (snd (lookup_named id env))
       with Not_found ->
         error ("execute: variable " ^ (Identifier.string_of_id id) ^ " not defined"))
	  
    | IsConst c ->
        make_judge cstr (type_of_constant env sigma c)
	  
    | IsMutInd ind ->
	make_judge cstr (type_of_inductive env sigma ind)
	  
    | IsMutConstruct cstruct -> 
	make_judge cstr (type_of_constructor env sigma cstruct)
	  
    | IsMutCase (ci,p,c,lf) ->
        let cj = execute mf env sigma c in
        let pj = execute mf env sigma p in
        let lfj = execute_array mf env sigma lf in
        let (j,_) = judge_of_case env sigma ci pj cj lfj in
        j
  
    | IsFix ((vn,i as vni),recdef) ->
        if (not mf.fix) && array_exists (fun n -> n < 0) vn then
          error "General Fixpoints not allowed";
        let (_,tys,_ as recdef') = execute_fix mf env sigma recdef in
	let fix = (vni,recdef') in
        check_fix env sigma fix;
	make_judge (mkFix fix) tys.(i)
	  
    | IsCoFix (i,recdef) ->
        let (_,tys,_ as recdef') = execute_fix mf env sigma recdef in
        let cofix = (i,recdef') in
        check_cofix env sigma cofix;
	make_judge (mkCoFix cofix) tys.(i)
	  
    | IsSort (Prop c) -> 
	judge_of_prop_contents c

    | IsSort (Type u) ->
	let (j,_) = judge_of_type u in j
	  
    | IsApp (f,args) ->
	let j = execute mf env sigma f in
        let jl = execute_list mf env sigma (Array.to_list args) in
	let (j,_) = apply_rel_list env sigma mf.nocheck jl j in
	j
	    
    | IsLambda (name,c1,c2) -> 
        let j = execute mf env sigma c1 in
	let var = assumption_of_judgment env sigma j in
	let env1 = push_rel_assum (name,var) env in
        let j' = execute mf env1 sigma c2 in 
        let (j,_) = abs_rel env1 sigma name var j' in
	j
	  
    | IsProd (name,c1,c2) ->
        let j = execute mf env sigma c1 in
        let varj = type_judgment env sigma j in
	let env1 = push_rel_assum (name,varj.utj_val) env in
        let j' = execute mf env1 sigma c2 in
        let varj' = type_judgment env sigma j' in
	let (j,_) = gen_rel env1 sigma name varj varj' in
	j

     | IsLetIn (name,c1,c2,c3) ->
        let j1 = execute mf env sigma c1 in
        let j2 = execute mf env sigma c2 in
	let tj2 = assumption_of_judgment env sigma j2 in
	let { uj_val = b; uj_type = t },_ = cast_rel env sigma j1 tj2 in
        let j3 = execute mf (push_rel_def (name,b,t) env) sigma c3 in
	{ uj_val = mkLetIn (name, j1.uj_val, tj2, j3.uj_val) ;
	  uj_type = type_app (subst1 j1.uj_val) j3.uj_type }
  
    | IsCast (c,t) ->
        let cj = execute mf env sigma c in
        let tj = execute mf env sigma t in
	let tj = assumption_of_judgment env sigma tj in
        let j, _ = cast_rel env sigma cj tj in
	j
	  
and execute_fix mf env sigma (names,lar,vdef) =
  let larj = execute_array mf env sigma lar in
  let lara = Array.map (assumption_of_judgment env sigma) larj in
  let ctxt = 
    array_map2_i (fun i na ty -> (na, type_app (lift i) ty)) names lara in
  let env1 = 
    Array.fold_left (fun env nvar -> push_rel_assum nvar env) env ctxt in
  let vdefj = execute_array mf env1 sigma vdef in
  let vdefv = Array.map j_val vdefj in
  let cst3 = type_fixpoint env1 sigma names lara vdefj in
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
  nf_betaiota (body_of_type j.uj_type)

(* The typed type of a judgment. *)

let execute_type env sigma constr = 
  let j = execute { fix=false; nocheck=true } env sigma constr in
  assumption_of_judgment env sigma j

let execute_rec_type env sigma constr = 
  let j = execute { fix=false; nocheck=false } env sigma constr in
  assumption_of_judgment env sigma j

