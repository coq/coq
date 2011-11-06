(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2011     *)
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

let e_judge_of_apply env evdref funj argjv =
  let rec apply_rec n typ = function
  | [] ->
      { uj_val  = mkApp (j_val funj, Array.map j_val argjv);
        uj_type = typ }
  | hj::restjl ->
      match kind_of_term (whd_betadeltaiota env !evdref typ) with
      | Prod (_,c1,c2) ->
	 if Evarconv.e_cumul env evdref hj.uj_type c1 then
	   apply_rec (n+1) (subst1 hj.uj_val c2) restjl
	 else
	   error_cant_apply_bad_type env (n,c1, hj.uj_type) funj argjv
      | _ ->
	  error_cant_apply_not_functional env funj argjv
  in
  apply_rec 1 funj.uj_type (Array.to_list argjv)

let check_branch_types env evdref cj (lfj,explft) =
  if Array.length lfj <> Array.length explft then
    error_number_branches env cj (Array.length explft);
  for i = 0 to Array.length explft - 1 do
    if not (Evarconv.e_cumul env evdref lfj.(i).uj_type explft.(i)) then
      error_ill_formed_branch env cj.uj_val i lfj.(i).uj_type explft.(i)
  done

let e_judge_of_case env evdref ci pj cj lfj =
  let indspec =
    try find_mrectype env !evdref cj.uj_type
    with Not_found -> error_case_not_inductive env cj in
  let _ = check_case_info env (fst indspec) ci in
  let (bty,rslty,univ) = type_case_branches env indspec pj cj.uj_val in
  check_branch_types env evdref cj (lfj,bty);
  { uj_val  = mkCase (ci, pj.uj_val, cj.uj_val, Array.map j_val lfj);
    uj_type = rslty }

let e_judge_of_cast env evdref cj k tj =
  let expected_type = tj.utj_val in
  if not (Evarconv.e_cumul env evdref cj.uj_type expected_type) then
    error_actual_type env cj expected_type;
  { uj_val = mkCast (cj.uj_val, k, expected_type);
    uj_type = expected_type }

(* The typing machine without information, without universes but with
   existential variables. *)

(* cstr must be in n.f. w.r.t. evars and execute returns a judgement
   where both the term and type are in n.f. *)
let rec execute env evdref cstr =
  match kind_of_term cstr with
    | Meta n ->
        { uj_val = cstr; uj_type = meta_type !evdref n }

    | Evar ev ->
	let ty = Evd.existential_type !evdref ev in
	let jty = execute env evdref (whd_evar !evdref ty) in
	let jty = assumption_of_judgment env jty in
	{ uj_val = cstr; uj_type = jty }

    | Rel n ->
	judge_of_relative env n

    | Var id ->
        judge_of_variable env id

    | Const c ->
        make_judge cstr (type_of_constant env c)

    | Ind ind ->
	make_judge cstr (type_of_inductive env ind)

    | Construct cstruct ->
	make_judge cstr (type_of_constructor env cstruct)

    | Case (ci,p,c,lf) ->
        let cj = execute env evdref c in
        let pj = execute env evdref p in
        let lfj = execute_array env evdref lf in
        e_judge_of_case env evdref ci pj cj lfj

    | Fix ((vn,i as vni),recdef) ->
        let (_,tys,_ as recdef') = execute_recdef env evdref recdef in
	let fix = (vni,recdef') in
        check_fix env fix;
	make_judge (mkFix fix) tys.(i)

    | CoFix (i,recdef) ->
        let (_,tys,_ as recdef') = execute_recdef env evdref recdef in
        let cofix = (i,recdef') in
        check_cofix env cofix;
	make_judge (mkCoFix cofix) tys.(i)

    | Sort (Prop c) ->
	judge_of_prop_contents c

    | Sort (Type u) ->
	judge_of_type u

    | App (f,args) ->
        let jl = execute_array env evdref args in
	let j =
	  match kind_of_term f with
	    | Ind ind ->
		(* Sort-polymorphism of inductive types *)
		make_judge f
		  (inductive_type_knowing_parameters env ind
		    (jv_nf_evar !evdref jl))
	    | Const cst ->
		(* Sort-polymorphism of inductive types *)
		make_judge f
		  (constant_type_knowing_parameters env cst
		    (jv_nf_evar !evdref jl))
	    | _ ->
		execute env evdref f
	in
	e_judge_of_apply env evdref j jl

    | Lambda (name,c1,c2) ->
        let j = execute env evdref c1 in
	let var = type_judgment env j in
	let env1 = push_rel (name,None,var.utj_val) env in
        let j' = execute env1 evdref c2 in
        judge_of_abstraction env1 name var j'

    | Prod (name,c1,c2) ->
        let j = execute env evdref c1 in
        let varj = type_judgment env j in
	let env1 = push_rel (name,None,varj.utj_val) env in
        let j' = execute env1 evdref c2 in
        let varj' = type_judgment env1 j' in
	judge_of_product env name varj varj'

     | LetIn (name,c1,c2,c3) ->
        let j1 = execute env evdref c1 in
        let j2 = execute env evdref c2 in
        let j2 = type_judgment env j2 in
        let _ =  judge_of_cast env j1 DEFAULTcast j2 in
        let env1 = push_rel (name,Some j1.uj_val,j2.utj_val) env in
        let j3 = execute env1 evdref c3 in
        judge_of_letin env name j1 j2 j3

    | Cast (c,k,t) ->
        let cj = execute env evdref c in
        let tj = execute env evdref t in
	let tj = type_judgment env tj in
        e_judge_of_cast env evdref cj k tj

and execute_recdef env evdref (names,lar,vdef) =
  let larj = execute_array env evdref lar in
  let lara = Array.map (assumption_of_judgment env) larj in
  let env1 = push_rec_types (names,lara,vdef) env in
  let vdefj = execute_array env1 evdref vdef in
  let vdefv = Array.map j_val vdefj in
  let _ = type_fixpoint env1 names lara vdefj in
  (names,lara,vdefv)

and execute_array env evdref = Array.map (execute env evdref)

and execute_list env evdref = List.map (execute env evdref)

let check env evd c t =
  let evdref = ref evd in
  let j = execute env evdref c in
  if not (Evarconv.e_cumul env evdref j.uj_type t) then
    error_actual_type env j (nf_evar evd t)

(* Type of a constr *)

let type_of env evd c =
  let j = execute env (ref evd) c in
  (* We are outside the kernel: we take fresh universes *)
  (* to avoid tactics and co to refresh universes themselves *)
  Termops.refresh_universes j.uj_type

(* Sort of a type *)

let sort_of env evd c =
  let j = execute env (ref evd) c in
  let a = type_judgment env j in
  a.utj_type

(* Try to solve the existential variables by typing *)

let solve_evars env evd c =
  let evdref = ref evd in
  let c = (execute env evdref c).uj_val in
  (* side-effect on evdref *)
  nf_evar !evdref c
  
