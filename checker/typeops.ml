(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open CErrors
open Util
open Names
open Cic
open Term
open Reduction
open Type_errors
open Inductive
open Environ

let inductive_of_constructor = fst

let conv_leq_vecti env v1 v2 =
  Array.fold_left2_i
    (fun i _ t1 t2 ->
      (try conv_leq env t1 t2
      with NotConvertible -> raise (NotConvertibleVect i)); ())
    ()
    v1
    v2

let check_constraints cst env = 
  if Environ.check_constraints cst env then ()
  else error_unsatisfied_constraints env cst

(* This should be a type (a priori without intension to be an assumption) *)
let type_judgment env (c,ty as j) =
  match whd_all env ty with
    | Sort s -> (c,s)
    | _ -> error_not_type env j

(* This should be a type intended to be assumed. The error message is *)
(* not as useful as for [type_judgment]. *)
let assumption_of_judgment env j =
  try fst(type_judgment env j)
  with TypeError _ ->
    error_assumption env j

(************************************************)
(* Incremental typing rules: builds a typing judgement given the *)
(* judgements for the subterms. *)

(*s Type of sorts *)

(* Prop and Set *)

let judge_of_prop = Sort (Type Univ.type1_univ)

(* Type of Type(i). *)

let judge_of_type u = Sort (Type (Univ.super u))

(*s Type of a de Bruijn index. *)

let judge_of_relative env n =
  try
    let LocalAssum (_,typ) | LocalDef (_,_,typ) = lookup_rel n env in
    lift n typ
  with Not_found ->
    error_unbound_rel env n

(* Type of constants *)

let judge_of_constant env (kn,u as cst) =
  let _cb =
    try lookup_constant kn env
    with Not_found ->
      failwith ("Cannot find constant: "^Constant.to_string kn)
  in
  let ty, cu = constant_type env cst in
  let () = check_constraints cu env in
    ty

(* Type of an application. *)

let judge_of_apply env (f,funj) argjv =
  let rec apply_rec n typ = function
    | [] -> typ
    | (h,hj)::restjl ->
        (match whd_all env typ with
          | Prod (_,c1,c2) ->
	      (try conv_leq env hj c1
	      with NotConvertible ->
		error_cant_apply_bad_type env (n,c1, hj) (f,funj) argjv);
	      apply_rec (n+1) (subst1 h c2) restjl
          | _ ->
	      error_cant_apply_not_functional env (f,funj) argjv)
  in
  apply_rec 1 funj (Array.to_list argjv)

(* Type of product *)

let sort_of_product env domsort rangsort =
  match (domsort, rangsort) with
    (* Product rule (s,Prop,Prop) *)
    | _,       Prop  -> rangsort
    (* Product rule (Prop/Set,Set,Set) *)
    | (Prop | Set),  Set -> rangsort
    (* Product rule (Type,Set,?) *)
    | Type u1, Set ->
        if engagement env = ImpredicativeSet then
          (* Rule is (Type,Set,Set) in the Set-impredicative calculus *)
          rangsort
        else
          (* Rule is (Type_i,Set,Type_i) in the Set-predicative calculus *)
          Type (Univ.sup u1 Univ.type0_univ)
    (* Product rule (Prop,Type_i,Type_i) *)
    | Set,  Type u2  -> Type (Univ.sup Univ.type0_univ u2)
    (* Product rule (Prop,Type_i,Type_i) *)
    | Prop, Type _  -> rangsort
    (* Product rule (Type_i,Type_i,Type_i) *)
    | Type u1, Type u2 -> Type (Univ.sup u1 u2)

(* Type of a type cast *)

(* [judge_of_cast env (c,typ1) (typ2,s)] implements the rule

    env |- c:typ1    env |- typ2:s    env |- typ1 <= typ2
    ---------------------------------------------------------------------
         env |- c:typ2
*)

let judge_of_cast env (c,cj) k tj =
  let conversion =
    match k with
    | VMcast | NATIVEcast -> vm_conv CUMUL
    | DEFAULTcast -> conv_leq in
  try
    conversion env cj tj
  with NotConvertible ->
    error_actual_type env (c,cj) tj

(* Inductive types. *)

(* The type is parametric over the uniform parameters whose conclusion
   is in Type; to enforce the internal constraints between the
   parameters and the instances of Type occurring in the type of the
   constructors, we use the level variables _statically_ assigned to
   the conclusions of the parameters as mediators: e.g. if a parameter
   has conclusion Type(alpha), static constraints of the form alpha<=v
   exist between alpha and the Type's occurring in the constructor
   types; when the parameters is finally instantiated by a term of
   conclusion Type(u), then the constraints u<=alpha is computed in
   the App case of execute; from this constraints, the expected
   dynamic constraints of the form u<=v are enforced *)

let judge_of_inductive_knowing_parameters env (ind,u) (paramstyp:constr array) =
  let specif =
    try lookup_mind_specif env ind
    with Not_found ->
      failwith ("Cannot find mutual inductive block: "^MutInd.to_string (fst ind))
  in
  type_of_inductive_knowing_parameters env (specif,u) paramstyp

let judge_of_inductive env ind =
  judge_of_inductive_knowing_parameters env ind [||]

(* Constructors. *)

let judge_of_constructor env (c,u) =
  let ind = inductive_of_constructor c in
  let specif =
    try lookup_mind_specif env ind
    with Not_found ->
      failwith ("Cannot find mutual inductive block: "^MutInd.to_string (fst ind))
  in
  type_of_constructor (c,u) specif

(* Case. *)

let check_branch_types env (c,cj) (lfj,explft) =
  try conv_leq_vecti env lfj explft
  with
      NotConvertibleVect i ->
        error_ill_formed_branch env c i lfj.(i) explft.(i)
    | Invalid_argument _ ->
        error_number_branches env (c,cj) (Array.length explft)

let judge_of_case env ci pj (c,cj) lfj =
  let indspec =
    try find_rectype env cj
    with Not_found -> error_case_not_inductive env (c,cj) in
  let _ = check_case_info env (fst (fst indspec)) ci in
  let (bty,rslty) = type_case_branches env indspec pj c in
  check_branch_types env (c,cj) (lfj,bty);
  rslty

(* Projection. *)

let judge_of_projection env p c ct =
  let pty = lookup_projection p env in
  let (ind,u), args =
    try find_rectype env ct
    with Not_found -> error_case_not_inductive env (c, ct)
  in
  let ty = subst_instance_constr u pty in
  substl (c :: List.rev args) ty

(* Fixpoints. *)

(* Checks the type of a general (co)fixpoint, i.e. without checking *)
(* the specific guard condition. *)

let type_fixpoint env lna lar lbody vdefj =
  let lt = Array.length vdefj in
  assert (Array.length lar = lt && Array.length lbody = lt);
  try
    conv_leq_vecti env vdefj (Array.map (fun ty -> lift lt ty) lar)
  with NotConvertibleVect i ->
    let vdefj = Array.map2 (fun b ty -> b,ty) lbody vdefj in
    error_ill_typed_rec_body env i lna vdefj lar

(************************************************************************)
(************************************************************************)


(* let refresh_arity env ar = *)
(*   let ctxt, hd = decompose_prod_assum ar in *)
(*   match hd with *)
(*       Sort (Type u) when not (is_univ_variable u) -> *)
(*         let u' = fresh_local_univ() in *)
(*         let env' = add_constraints (enforce_leq u u' empty_constraint) env in *)
(*         env', mkArity (ctxt,Type u') *)
(*     | _ -> env, ar *)


(* The typing machine. *)
let rec execute env cstr =
  match cstr with
    (* Atomic terms *)
    | Sort (Prop | Set) -> judge_of_prop

    | Sort (Type u) -> judge_of_type u

    | Rel n -> judge_of_relative env n

    | Var _ -> anomaly (Pp.str "Section variable in Coqchk!")

    | Const c -> judge_of_constant env c

    (* Lambda calculus operators *)
    | App (App (f,args),args') ->
        execute env (App(f,Array.append args args'))

    | App (f,args) ->
        let jl = execute_array env args in
	let j =
	  match f with
	    | Ind ind ->
		judge_of_inductive_knowing_parameters env ind jl
	    | _ ->
		(* No template polymorphism *)
		execute env f
	in
        let jl = Array.map2 (fun c ty -> c,ty) args jl in
	judge_of_apply env (f,j) jl

    | Proj (p, c) ->
        let ct = execute env c in
          judge_of_projection env p c ct

    | Lambda (name,c1,c2) ->
        let _ = execute_type env c1 in
	let env1 = push_rel (LocalAssum (name,c1)) env in
        let j' = execute env1 c2 in
        Prod(name,c1,j')

    | Prod (name,c1,c2) ->
        let varj = execute_type env c1 in
	let env1 = push_rel (LocalAssum (name,c1)) env in
        let varj' = execute_type env1 c2 in
	Sort (sort_of_product env varj varj')

    | LetIn (name,c1,c2,c3) ->
        let j1 = execute env c1 in
        (* /!\ c2 can be an inferred type => refresh
           (but the pushed type is still c2) *)
        let _ =
          let env',c2' = (* refresh_arity env *) env, c2 in
          let _ = execute_type env' c2' in
          judge_of_cast env' (c1,j1) DEFAULTcast c2' in
        let env1 = push_rel (LocalDef (name,c1,c2)) env in
        let j' = execute env1 c3 in
        subst1 c1 j'

    | Cast (c,k,t) ->
        let cj = execute env c in
        let _ = execute_type env t in
	judge_of_cast env (c,cj) k t;
        t

    (* Inductive types *)
    | Ind ind -> judge_of_inductive env ind

    | Construct c -> judge_of_constructor env c

    | Case (ci,p,c,lf) ->
        let cj = execute env c in
        let pj = execute env p in
        let lfj = execute_array env lf in
        judge_of_case env ci (p,pj) (c,cj) lfj
    | Fix ((_,i as vni),recdef) ->
        let fix_ty = execute_recdef env recdef i in
        let fix = (vni,recdef) in
        check_fix env fix;
	fix_ty

    | CoFix (i,recdef) ->
        let fix_ty = execute_recdef env recdef i in
        let cofix = (i,recdef) in
        check_cofix env cofix;
	fix_ty

    (* Partial proofs: unsupported by the kernel *)
    | Meta _ ->
	anomaly (Pp.str "the kernel does not support metavariables.")

    | Evar _ ->
	anomaly (Pp.str "the kernel does not support existential variables.")

and execute_type env constr =
  let j = execute env constr in
  snd (type_judgment env (constr,j))

and execute_recdef env (names,lar,vdef) i =
  let larj = execute_array env lar in
  let larj = Array.map2 (fun c ty -> c,ty) lar larj in
  let lara = Array.map (assumption_of_judgment env) larj in
  let env1 = push_rec_types (names,lara,vdef) env in
  let vdefj = execute_array env1 vdef in
  type_fixpoint env1 names lara vdef vdefj;
  lara.(i)

and execute_array env = Array.map (execute env)

(* Derived functions *)
let infer env constr = execute env constr
let infer_type env constr = execute_type env constr

(* Typing of several terms. *)

let check_ctxt env rels =
  fold_rel_context (fun d env ->
    match d with
      | LocalAssum (_,ty) ->
          let _ = infer_type env ty in
          push_rel d env
      | LocalDef (_,bd,ty) ->
          let j1 = infer env bd in
          let _ = infer env ty in
          conv_leq env j1 ty;
          push_rel d env)
    rels ~init:env

(* Polymorphic arities utils *)

let check_kind env ar u =
  match (snd (dest_prod env ar)) with
  | Sort (Type u') when Univ.Universe.equal u' (Univ.Universe.make u) -> ()
  | _ -> failwith "not the correct sort"

let check_polymorphic_arity env params par =
  let pl = par.template_param_levels in
  let rec check_p env pl params =
    match pl, params with
        Some u::pl, LocalAssum (na,ty)::params ->
          check_kind env ty u;
          check_p (push_rel (LocalAssum (na,ty)) env) pl params
      | None::pl,d::params -> check_p (push_rel d env) pl params
      | [], _ -> ()
      | _ -> failwith "check_poly: not the right number of params" in
  check_p env pl (List.rev params)
