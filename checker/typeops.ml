(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id: typeops.ml 9314 2006-10-29 20:11:08Z herbelin $ *)

open Util
open Names
open Univ
open Term
open Reduction
open Type_errors
open Declarations
open Inductive
open Environ

let inductive_of_constructor = fst

let conv_leq_vecti env v1 v2 =
  array_fold_left2_i
    (fun i _ t1 t2 ->
      (try conv_leq env t1 t2
      with NotConvertible -> raise (NotConvertibleVect i)); ())
    ()
    v1
    v2

(* This should be a type (a priori without intension to be an assumption) *)
let type_judgment env (c,ty as j) =
  match whd_betadeltaiota env ty with
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

let judge_of_prop = Sort (Type type1_univ)

(* Type of Type(i). *)

let judge_of_type u = Sort (Type (super u))

(*s Type of a de Bruijn index. *)

let judge_of_relative env n =
  try
    let (_,_,typ) = lookup_rel n env in
    lift n typ
  with Not_found ->
    error_unbound_rel env n

(* Type of variables *)
let judge_of_variable env id =
  try named_type id env
  with Not_found ->
    error_unbound_var env id

(* Management of context of variables. *)

(* Checks if a context of variable can be instantiated by the
   variables of the current env *)
(* TODO: check order? *)
let rec check_hyps_inclusion env sign =
  fold_named_context
    (fun (id,_,ty1) () ->
      let ty2 = named_type id env in
      if not (eq_constr ty2 ty1) then
        error "types do not match")
    sign
    ~init:()


let check_args env c hyps =
  try check_hyps_inclusion env hyps
  with UserError _ | Not_found ->
    error_reference_variables env c


(* Checks if the given context of variables [hyps] is included in the
   current context of [env]. *)
(*
let check_hyps id env hyps =
  let hyps' = named_context env in
  if not (hyps_inclusion env hyps hyps') then
    error_reference_variables env id
*)
(* Instantiation of terms on real arguments. *)

(* Make a type polymorphic if an arity *)

let extract_level env p =
  let _,c = dest_prod_assum env p in
  match c with Sort (Type u) -> Some u | _ -> None

let extract_context_levels env =
  List.fold_left
    (fun l (_,b,p) -> if b=None then extract_level env p::l else l) []

let make_polymorphic_if_arity env t =
  let params, ccl = dest_prod_assum env t in
  match ccl with
  | Sort (Type u) ->
      let param_ccls = extract_context_levels env params in
      let s = { poly_param_levels = param_ccls; poly_level = u} in
      PolymorphicArity (params,s)
  | _ ->
      NonPolymorphicType t

(* Type of constants *)

let type_of_constant_knowing_parameters env t paramtyps =
  match t with
  | NonPolymorphicType t -> t
  | PolymorphicArity (sign,ar) ->
      let ctx = List.rev sign in
      let ctx,s = instantiate_universes env ctx ar paramtyps in
      mkArity (List.rev ctx,s)

let type_of_constant_type env t =
  type_of_constant_knowing_parameters env t [||]

let type_of_constant env cst =
  type_of_constant_type env (constant_type env cst)

let judge_of_constant_knowing_parameters env cst paramstyp =
  let c = Const cst in
  let cb =
    try lookup_constant cst env
    with Not_found ->
      failwith ("Cannot find constant: "^string_of_con cst) in
  let _ = check_args env c cb.const_hyps in
  type_of_constant_knowing_parameters env cb.const_type paramstyp

let judge_of_constant env cst =
  judge_of_constant_knowing_parameters env cst [||]

(* Type of an application. *)

let judge_of_apply env (f,funj) argjv =
  let rec apply_rec n typ = function
    | [] -> typ
    | (h,hj)::restjl ->
        (match whd_betadeltaiota env typ with
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
    | (_,       Prop Null)  -> rangsort
    (* Product rule (Prop/Set,Set,Set) *)
    | (Prop _,  Prop Pos) -> rangsort
    (* Product rule (Type,Set,?) *)
    | (Type u1, Prop Pos) ->
        if engagement env = Some ImpredicativeSet then
          (* Rule is (Type,Set,Set) in the Set-impredicative calculus *)
          rangsort
        else
          (* Rule is (Type_i,Set,Type_i) in the Set-predicative calculus *)
          Type (sup u1 type0_univ)
    (* Product rule (Prop,Type_i,Type_i) *)
    | (Prop Pos,  Type u2)  -> Type (sup type0_univ u2)
    (* Product rule (Prop,Type_i,Type_i) *)
    | (Prop Null, Type _)  -> rangsort
    (* Product rule (Type_i,Type_i,Type_i) *)
    | (Type u1, Type u2) -> Type (sup u1 u2)

(* Type of a type cast *)

(* [judge_of_cast env (c,typ1) (typ2,s)] implements the rule

    env |- c:typ1    env |- typ2:s    env |- typ1 <= typ2
    ---------------------------------------------------------------------
         env |- c:typ2
*)

let judge_of_cast env (c,cj) k tj =
  let conversion =
    match k with
    | VMcast -> vm_conv CUMUL
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

let judge_of_inductive_knowing_parameters env ind (paramstyp:constr array) =
  let c = Ind ind in
  let (mib,mip) =
    try lookup_mind_specif env ind
    with Not_found ->
      failwith ("Cannot find inductive: "^string_of_mind (fst ind)) in
  check_args env c mib.mind_hyps;
  type_of_inductive_knowing_parameters env mip paramstyp

let judge_of_inductive env ind =
  judge_of_inductive_knowing_parameters env ind [||]

(* Constructors. *)

let judge_of_constructor env c =
  let constr = Construct c in
  let _ =
    let ((kn,_),_) = c in
    let mib =
      try lookup_mind kn env
      with Not_found ->
        failwith ("Cannot find inductive: "^string_of_mind (fst (fst c))) in
    check_args env constr mib.mind_hyps in
  let specif = lookup_mind_specif env (inductive_of_constructor c) in
  type_of_constructor c specif

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
  let _ = check_case_info env (fst indspec) ci in
  let (bty,rslty) = type_case_branches env indspec pj c in
  check_branch_types env (c,cj) (lfj,bty);
  rslty

(* Fixpoints. *)

(* Checks the type of a general (co)fixpoint, i.e. without checking *)
(* the specific guard condition. *)

let type_fixpoint env lna lar lbody vdefj =
  let lt = Array.length vdefj in
  assert (Array.length lar = lt && Array.length lbody = lt);
  try
    conv_leq_vecti env vdefj (Array.map (fun ty -> lift lt ty) lar)
  with NotConvertibleVect i ->
    let vdefj = array_map2 (fun b ty -> b,ty) lbody vdefj in
    error_ill_typed_rec_body env i lna vdefj lar

(************************************************************************)
(************************************************************************)


let refresh_arity env ar =
  let ctxt, hd = decompose_prod_assum ar in
  match hd with
      Sort (Type u) when not (is_univ_variable u) ->
        let u' = fresh_local_univ() in
        let env' = add_constraints (enforce_geq u' u Constraint.empty) env in
        env', mkArity (ctxt,Type u')
    | _ -> env, ar


(* The typing machine. *)
let rec execute env cstr =
  match cstr with
    (* Atomic terms *)
    | Sort (Prop _) -> judge_of_prop

    | Sort (Type u) -> judge_of_type u

    | Rel n -> judge_of_relative env n

    | Var id -> judge_of_variable env id

    | Const c -> judge_of_constant env c

    (* Lambda calculus operators *)
    | App (App (f,args),args') ->
        execute env (App(f,Array.append args args'))

    | App (f,args) ->
        let jl = execute_array env args in
	let j =
	  match f with
	    | Ind ind ->
		(* Sort-polymorphism of inductive types *)
		judge_of_inductive_knowing_parameters env ind jl
	    | Const cst ->
		(* Sort-polymorphism of constant *)
		judge_of_constant_knowing_parameters env cst jl
	    | _ ->
		(* No sort-polymorphism *)
		execute env f
	in
        let jl = array_map2 (fun c ty -> c,ty) args jl in
	judge_of_apply env (f,j) jl

    | Lambda (name,c1,c2) ->
        let _ = execute_type env c1 in
	let env1 = push_rel (name,None,c1) env in
        let j' = execute env1 c2 in
        Prod(name,c1,j')

    | Prod (name,c1,c2) ->
        let varj = execute_type env c1 in
	let env1 = push_rel (name,None,c1) env in
        let varj' = execute_type env1 c2 in
	Sort (sort_of_product env varj varj')

    | LetIn (name,c1,c2,c3) ->
        let j1 = execute env c1 in
        (* /!\ c2 can be an inferred type => refresh
           (but the pushed type is still c2) *)
        let _ =
          let env',c2' = refresh_arity env c2 in
          let _ = execute_type env' c2' in
          judge_of_cast env' (c1,j1) DEFAULTcast c2' in
        let env1 = push_rel (name,Some c1,c2) env in
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
	anomaly "the kernel does not support metavariables"

    | Evar _ ->
	anomaly "the kernel does not support existential variables"

and execute_type env constr =
  let j = execute env constr in
  snd (type_judgment env (constr,j))

and execute_recdef env (names,lar,vdef) i =
  let larj = execute_array env lar in
  let larj = array_map2 (fun c ty -> c,ty) lar larj in
  let lara = Array.map (assumption_of_judgment env) larj in
  let env1 = push_rec_types (names,lara,vdef) env in
  let vdefj = execute_array env1 vdef in
  type_fixpoint env1 names lara vdef vdefj;
  lara.(i)

and execute_array env = Array.map (execute env)

and execute_list env = List.map (execute env)

(* Derived functions *)
let infer env constr = execute env constr
let infer_type env constr = execute_type env constr
let infer_v env cv = execute_array env cv

(* Typing of several terms. *)

let check_ctxt env rels =
  fold_rel_context (fun d env ->
    match d with
        (_,None,ty) ->
          let _ = infer_type env ty in
          push_rel d env
      | (_,Some bd,ty) ->
          let j1 = infer env bd in
          let _ = infer env ty in
          conv_leq env j1 ty;
          push_rel d env)
    rels ~init:env

let check_named_ctxt env ctxt =
  fold_named_context (fun (id,_,_ as d) env ->
    let _ =
      try
        let _ = lookup_named id env in
        failwith ("variable "^string_of_id id^" defined twice")
      with Not_found -> () in
    match d with
        (_,None,ty) ->
          let _ = infer_type env ty in
          push_named d env
      | (_,Some bd,ty) ->
          let j1 = infer env bd in
          let _ = infer env ty in
          conv_leq env j1 ty;
          push_named d env)
    ctxt ~init:env

(* Polymorphic arities utils *)

let check_kind env ar u =
  if snd (dest_prod env ar) = Sort(Type u) then ()
  else failwith "not the correct sort"

let check_polymorphic_arity env params par =
  let pl = par.poly_param_levels in
  let rec check_p env pl params =
    match pl, params with
        Some u::pl, (na,None,ty)::params ->
          check_kind env ty u;
          check_p (push_rel (na,None,ty) env) pl params
      | None::pl,d::params -> check_p (push_rel d env) pl params
      | [], _ -> ()
      | _ -> failwith "check_poly: not the right number of params" in
  check_p env pl (List.rev params)
