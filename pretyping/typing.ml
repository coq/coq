(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Errors
open Util
open Term
open Vars
open Environ
open Reductionops
open Type_errors
open Inductive
open Inductiveops
open Typeops
open Arguments_renaming

let meta_type evd mv =
  let ty =
    try Evd.meta_ftype evd mv
    with Not_found -> anomaly (str "unknown meta ?" ++ str (Nameops.string_of_meta mv)) in
  meta_instance evd ty

let constant_type_knowing_parameters env cst jl =
  let paramstyp = Array.map (fun j -> lazy j.uj_type) jl in
  type_of_constant_knowing_parameters_in env cst paramstyp

let inductive_type_knowing_parameters env (ind,u) jl =
  let mspec = lookup_mind_specif env ind in
  let paramstyp = Array.map (fun j -> lazy j.uj_type) jl in
  Inductive.type_of_inductive_knowing_parameters env (mspec,u) paramstyp

let e_type_judgment env evdref j =
  match kind_of_term (whd_betadeltaiota env !evdref j.uj_type) with
    | Sort s -> {utj_val = j.uj_val; utj_type = s }
    | Evar ev ->
        let (evd,s) = Evarutil.define_evar_as_sort env !evdref ev in
        evdref := evd; { utj_val = j.uj_val; utj_type = s }
    | _ -> error_not_type env j

let e_assumption_of_judgment env evdref j =
  try (e_type_judgment env evdref j).utj_val
  with TypeError _ ->
    error_assumption env j

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
      | Evar ev ->
	  let (evd',t) = Evarutil.define_evar_as_product !evdref ev in
          evdref := evd';
          let (_,_,c2) = destProd t in
	  apply_rec (n+1) (subst1 hj.uj_val c2) restjl
      | _ ->
	  error_cant_apply_not_functional env funj argjv
  in
  apply_rec 1 funj.uj_type (Array.to_list argjv)

let e_check_branch_types env evdref (ind,u) cj (lfj,explft) =
  if not (Int.equal (Array.length lfj) (Array.length explft)) then
    error_number_branches env cj (Array.length explft);
  for i = 0 to Array.length explft - 1 do
    if not (Evarconv.e_cumul env evdref lfj.(i).uj_type explft.(i)) then
      error_ill_formed_branch env cj.uj_val ((ind,i+1),u) lfj.(i).uj_type explft.(i)
  done

let max_sort l =
  if Sorts.List.mem InType l then InType else
  if Sorts.List.mem InSet l then InSet else InProp

let e_is_correct_arity env evdref c pj ind specif params =
  let arsign = make_arity_signature env true (make_ind_family (ind,params)) in
  let allowed_sorts = elim_sorts specif in
  let error () = error_elim_arity env ind allowed_sorts c pj None in
  let rec srec env pt ar =
    let pt' = whd_betadeltaiota env !evdref pt in
    match kind_of_term pt', ar with
    | Prod (na1,a1,t), (_,None,a1')::ar' ->
        if not (Evarconv.e_cumul env evdref a1 a1') then error ();
        srec (push_rel (na1,None,a1) env) t ar'
    | Sort s, [] ->
        if not (Sorts.List.mem (Sorts.family s) allowed_sorts)
        then error ()
    | Evar (ev,_), [] ->
        let evd, s = Evd.fresh_sort_in_family env !evdref (max_sort allowed_sorts) in
        evdref := Evd.define ev (mkSort s) evd
    | _, (_,Some _,_ as d)::ar' ->
        srec (push_rel d env) (lift 1 pt') ar'
    | _ ->
        error ()
  in
  srec env pj.uj_type (List.rev arsign)

let e_type_case_branches env evdref (ind,largs) pj c =
  let specif = lookup_mind_specif env (fst ind) in
  let nparams = inductive_params specif in
  let (params,realargs) = List.chop nparams largs in
  let p = pj.uj_val in
  let univ = e_is_correct_arity env evdref c pj ind specif params in
  let lc = build_branches_type ind specif params p in
  let n = (snd specif).Declarations.mind_nrealargs in
  let ty =
    whd_betaiota !evdref (Reduction.betazeta_appvect (n+1) p (Array.of_list (realargs@[c]))) in
  (lc, ty, univ)

let e_judge_of_case env evdref ci pj cj lfj =
  let indspec =
    try find_mrectype env !evdref cj.uj_type
    with Not_found -> error_case_not_inductive env cj in
  let _ = check_case_info env (fst indspec) ci in
  let (bty,rslty,univ) = e_type_case_branches env evdref indspec pj cj.uj_val in
  e_check_branch_types env evdref (fst indspec) cj (lfj,bty);
  { uj_val  = mkCase (ci, pj.uj_val, cj.uj_val, Array.map j_val lfj);
    uj_type = rslty }

(* FIXME: might depend on the level of actual parameters!*)
let check_allowed_sort env sigma ind c p =
  let pj = Retyping.get_judgment_of env sigma p in
  let ksort = family_of_sort (sort_of_arity env sigma pj.uj_type) in
  let specif = Global.lookup_inductive (fst ind) in
  let sorts = elim_sorts specif in
  if not (List.exists ((==) ksort) sorts) then
    let s = inductive_sort_family (snd specif) in
    error_elim_arity env ind sorts c pj
      (Some(ksort,s,error_elim_explain ksort s))

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
	let jty = e_assumption_of_judgment env evdref jty in
	{ uj_val = cstr; uj_type = jty }

    | Rel n ->
	judge_of_relative env n

    | Var id ->
        judge_of_variable env id

    | Const c ->
        make_judge cstr (rename_type_of_constant env c)

    | Ind ind ->
	make_judge cstr (rename_type_of_inductive env ind)

    | Construct cstruct ->
	make_judge cstr (rename_type_of_constructor env cstruct)

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

    | Proj (p, c) -> 
        let cj = execute env evdref c in
	  judge_of_projection env p (Evarutil.j_nf_evar !evdref cj)

    | App (f,args) ->
        let jl = execute_array env evdref args in
	let j =
	  match kind_of_term f with
	    | Ind ind when Environ.template_polymorphic_pind ind env ->
		(* Sort-polymorphism of inductive types *)
		make_judge f
		  (inductive_type_knowing_parameters env ind
		    (Evarutil.jv_nf_evar !evdref jl))
	    | Const cst when Environ.template_polymorphic_pconstant cst env ->
		(* Sort-polymorphism of inductive types *)
		make_judge f
		  (constant_type_knowing_parameters env cst
		    (Evarutil.jv_nf_evar !evdref jl))
	    | _ ->
		execute env evdref f
	in
	e_judge_of_apply env evdref j jl

    | Lambda (name,c1,c2) ->
        let j = execute env evdref c1 in
	let var = e_type_judgment env evdref j in
	let env1 = push_rel (name,None,var.utj_val) env in
        let j' = execute env1 evdref c2 in
        judge_of_abstraction env1 name var j'

    | Prod (name,c1,c2) ->
        let j = execute env evdref c1 in
        let varj = e_type_judgment env evdref j in
	let env1 = push_rel (name,None,varj.utj_val) env in
        let j' = execute env1 evdref c2 in
        let varj' = e_type_judgment env1 evdref j' in
	judge_of_product env name varj varj'

     | LetIn (name,c1,c2,c3) ->
        let j1 = execute env evdref c1 in
        let j2 = execute env evdref c2 in
        let j2 = e_type_judgment env evdref j2 in
        let _ =  e_judge_of_cast env evdref j1 DEFAULTcast j2 in
        let env1 = push_rel (name,Some j1.uj_val,j2.utj_val) env in
        let j3 = execute env1 evdref c3 in
        judge_of_letin env name j1 j2 j3

    | Cast (c,k,t) ->
        let cj = execute env evdref c in
        let tj = execute env evdref t in
	let tj = e_type_judgment env evdref tj in
        e_judge_of_cast env evdref cj k tj

and execute_recdef env evdref (names,lar,vdef) =
  let larj = execute_array env evdref lar in
  let lara = Array.map (e_assumption_of_judgment env evdref) larj in
  let env1 = push_rec_types (names,lara,vdef) env in
  let vdefj = execute_array env1 evdref vdef in
  let vdefv = Array.map j_val vdefj in
  let _ = type_fixpoint env1 names lara vdefj in
  (names,lara,vdefv)

and execute_array env evdref = Array.map (execute env evdref)

let check env evdref c t =
  let j = execute env evdref c in
  if not (Evarconv.e_cumul env evdref j.uj_type t) then
    error_actual_type env j (nf_evar !evdref t)

(* Type of a constr *)

let type_of env evd c =
  let j = execute env (ref evd) c in
    j.uj_type

(* Sort of a type *)

let sort_of env evdref c =
  let j = execute env evdref c in
  let a = e_type_judgment env evdref j in
  a.utj_type

(* Try to solve the existential variables by typing *)

let e_type_of ?(refresh=false) env evd c =
  let evdref = ref evd in
  let j = execute env evdref c in
  (* side-effect on evdref *)
    if refresh then
      Evarsolve.refresh_universes ~onlyalg:true (Some false) env !evdref j.uj_type
    else !evdref, j.uj_type

let solve_evars env evdref c =
  let c = (execute env evdref c).uj_val in
  (* side-effect on evdref *)
  nf_evar !evdref c

let _ = Evarconv.set_solve_evars solve_evars
