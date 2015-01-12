(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Errors
open Util
open Names
open Univ
open Term
open Vars
open Declarations
open Environ
open Reduction
open Inductive
open Type_errors

let conv_leq l2r env x y = default_conv CUMUL ~l2r env x y

let conv_leq_vecti env v1 v2 =
  Array.fold_left2_i
    (fun i _ t1 t2 ->
      try conv_leq false env t1 t2
      with NotConvertible -> raise (NotConvertibleVect i))
    ()
    v1
    v2

let check_constraints cst env = 
  if Environ.check_constraints cst env then ()
  else error_unsatisfied_constraints env cst

(* This should be a type (a priori without intension to be an assumption) *)
let type_judgment env c t =
  match kind_of_term(whd_betadeltaiota env t) with
    | Sort s -> {utj_val = c; utj_type = s }
    | _ -> error_not_type env (make_judge c t)

let check_type env c t =
  match kind_of_term(whd_betadeltaiota env t) with
  | Sort s -> s
  | _ -> error_not_type env (make_judge c t)

(* This should be a type intended to be assumed. The error message is *)
(* not as useful as for [type_judgment]. *)
let assumption_of_judgment env t ty =
  try let _ = check_type env t ty in t
  with TypeError _ ->
    error_assumption env (make_judge t ty)

(************************************************)
(* Incremental typing rules: builds a typing judgement given the *)
(* judgements for the subterms. *)

(*s Type of sorts *)

(* Prop and Set *)

let judge_of_prop = mkSort type1_sort

let judge_of_prop_contents _ = judge_of_prop

(* Type of Type(i). *)

let judge_of_type u =
  let uu = Universe.super u in
    mkType uu

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

(* Checks if a context of variables can be instantiated by the
   variables of the current env *)
(* TODO: check order? *)
let check_hyps_inclusion env f c sign =
  Context.fold_named_context
    (fun (id,_,ty1) () ->
      try
        let ty2 = named_type id env in
        if not (eq_constr ty2 ty1) then raise Exit
      with Not_found | Exit ->
        error_reference_variables env id (f c))
    sign
    ~init:()

(* Instantiation of terms on real arguments. *)

(* Make a type polymorphic if an arity *)

(* Type of constants *)


let type_of_constant_knowing_parameters_arity env t paramtyps =
  match t with
  | RegularArity t -> t
  | TemplateArity (sign,ar) ->
      let ctx = List.rev sign in
      let ctx,s = instantiate_universes env ctx ar paramtyps in
      mkArity (List.rev ctx,s)

let type_of_constant_knowing_parameters env cst paramtyps =
  let ty, cu = constant_type env cst in
    type_of_constant_knowing_parameters_arity env ty paramtyps, cu

let judge_of_constant_knowing_parameters env (kn,u as cst) args =
  let cb = lookup_constant kn env in
  let () = check_hyps_inclusion env mkConstU cst cb.const_hyps in
  let ty, cu = type_of_constant_knowing_parameters env cst args in
  let () = check_constraints cu env in
    ty

let judge_of_constant env cst =
  judge_of_constant_knowing_parameters env cst [||]

(* Type of a lambda-abstraction. *)

(* [judge_of_abstraction env name var j] implements the rule

 env, name:typ |- j.uj_val:j.uj_type     env, |- (name:typ)j.uj_type : s
 -----------------------------------------------------------------------
          env |- [name:typ]j.uj_val : (name:typ)j.uj_type

  Since all products are defined in the Calculus of Inductive Constructions
  and no upper constraint exists on the sort $s$, we don't need to compute $s$
*)

let judge_of_abstraction env name var ty =
  mkProd (name, var, ty)

(* Type of an application. *)

let make_judgev c t = 
  Array.map2 make_judge c t

let judge_of_apply env func funt argsv argstv =
  let len = Array.length argsv in
  let rec apply_rec i typ = 
    if Int.equal i len then typ
    else 
      (match kind_of_term (whd_betadeltaiota env typ) with
      | Prod (_,c1,c2) ->
	let arg = argsv.(i) and argt = argstv.(i) in
	  (try
	     let () = conv_leq false env argt c1 in
	       apply_rec (i+1) (subst1 arg c2)
	   with NotConvertible ->
	     error_cant_apply_bad_type env
	       (i+1,c1,argt)
	       (make_judge func funt)
	       (make_judgev argsv argstv))
	    
      | _ ->
	error_cant_apply_not_functional env 
	  (make_judge func funt)
	  (make_judgev argsv argstv))
  in apply_rec 0 funt

(* Type of product *)

let sort_of_product env domsort rangsort =
  match (domsort, rangsort) with
    (* Product rule (s,Prop,Prop) *)
    | (_,       Prop Null)  -> rangsort
    (* Product rule (Prop/Set,Set,Set) *)
    | (Prop _,  Prop Pos) -> rangsort
    (* Product rule (Type,Set,?) *)
    | (Type u1, Prop Pos) ->
        begin match engagement env with
        | Some ImpredicativeSet ->
          (* Rule is (Type,Set,Set) in the Set-impredicative calculus *)
          rangsort
        | _ ->
          (* Rule is (Type_i,Set,Type_i) in the Set-predicative calculus *)
          Type (Universe.sup Universe.type0 u1)
        end
    (* Product rule (Prop,Type_i,Type_i) *)
    | (Prop Pos,  Type u2)  -> Type (Universe.sup Universe.type0 u2)
    (* Product rule (Prop,Type_i,Type_i) *)
    | (Prop Null, Type _)  -> rangsort
    (* Product rule (Type_i,Type_i,Type_i) *)
    | (Type u1, Type u2) -> Type (Universe.sup u1 u2)

(* [judge_of_product env name (typ1,s1) (typ2,s2)] implements the rule

    env |- typ1:s1       env, name:typ1 |- typ2 : s2
    -------------------------------------------------------------------------
         s' >= (s1,s2), env |- (name:typ)j.uj_val : s'

  where j.uj_type is convertible to a sort s2
*)
let judge_of_product env name s1 s2 =
  let s = sort_of_product env s1 s2 in
    mkSort s

(* Type of a type cast *)

(* [judge_of_cast env (c,typ1) (typ2,s)] implements the rule

    env |- c:typ1    env |- typ2:s    env |- typ1 <= typ2
    ---------------------------------------------------------------------
         env |- c:typ2
*)

let judge_of_cast env c ct k expected_type =
  try
    match k with
    | VMcast ->
      vm_conv CUMUL env ct expected_type
    | DEFAULTcast ->
      default_conv ~l2r:false CUMUL env ct expected_type
    | REVERTcast ->
      default_conv ~l2r:true CUMUL env ct expected_type
    | NATIVEcast ->
      let sigma = Nativelambda.empty_evars in
      native_conv CUMUL sigma env ct expected_type
  with NotConvertible ->
    error_actual_type env (make_judge c ct) expected_type

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

let judge_of_inductive_knowing_parameters env (ind,u as indu) args =
  let (mib,mip) as spec = lookup_mind_specif env ind in
  check_hyps_inclusion env mkIndU indu mib.mind_hyps;
  let t,cst = Inductive.constrained_type_of_inductive_knowing_parameters 
    env (spec,u) args
  in
    check_constraints cst env;
    t

let judge_of_inductive env (ind,u as indu) =
  let (mib,mip) = lookup_mind_specif env ind in
  check_hyps_inclusion env mkIndU indu mib.mind_hyps;
  let t,cst = Inductive.constrained_type_of_inductive env ((mib,mip),u) in
    check_constraints cst env;
    t

(* Constructors. *)

let judge_of_constructor env (c,u as cu) =
  let _ =
    let ((kn,_),_) = c in
    let mib = lookup_mind kn env in
    check_hyps_inclusion env mkConstructU cu mib.mind_hyps in
  let specif = lookup_mind_specif env (inductive_of_constructor c) in
  let t,cst = constrained_type_of_constructor cu specif in
  let () = check_constraints cst env in
    t

(* Case. *)

let check_branch_types env (ind,u) c ct lft explft =
  try conv_leq_vecti env lft explft
  with
      NotConvertibleVect i ->
        error_ill_formed_branch env c ((ind,i+1),u) lft.(i) explft.(i)
    | Invalid_argument _ ->
        error_number_branches env (make_judge c ct) (Array.length explft)

let judge_of_case env ci p pt c ct lf lft =
  let (pind, _ as indspec) =
    try find_rectype env ct
    with Not_found -> error_case_not_inductive env (make_judge c ct) in
  let _ = check_case_info env pind ci in
  let (bty,rslty) =
    type_case_branches env indspec (make_judge p pt) c in
  let () = check_branch_types env pind c ct lft bty in
    rslty

let judge_of_projection env p c ct =
  let pb = lookup_projection p env in
  let (ind,u), args =
    try find_rectype env ct
    with Not_found -> error_case_not_inductive env (make_judge c ct)
  in
    assert(eq_mind pb.proj_ind (fst ind));
    let ty = Vars.subst_instance_constr u pb.Declarations.proj_type in
      substl (c :: List.rev args) ty
      

(* Fixpoints. *)

(* Checks the type of a general (co)fixpoint, i.e. without checking *)
(* the specific guard condition. *)

let type_fixpoint env lna lar vdef vdeft =
  let lt = Array.length vdeft in
  assert (Int.equal (Array.length lar) lt);
  try
    conv_leq_vecti env vdeft (Array.map (fun ty -> lift lt ty) lar)
  with NotConvertibleVect i ->
    error_ill_typed_rec_body env i lna (make_judgev vdef vdeft) lar

(************************************************************************)
(************************************************************************)

(* The typing machine. *)
    (* ATTENTION : faudra faire le typage du contexte des Const,
    Ind et Constructsi un jour cela devient des constructions
    arbitraires et non plus des variables *)
let rec execute env cstr =
  match kind_of_term cstr with
    (* Atomic terms *)
    | Sort (Prop c) ->
      judge_of_prop_contents c
	
    | Sort (Type u) ->
      judge_of_type u

    | Rel n ->
      judge_of_relative env n

    | Var id ->
      judge_of_variable env id

    | Const c ->
      judge_of_constant env c
	
    | Proj (p, c) ->
        let ct = execute env c in
          judge_of_projection env p c ct

    (* Lambda calculus operators *)
    | App (f,args) ->
        let argst = execute_array env args in
	let ft =
	  match kind_of_term f with
	  | Ind ind when Environ.template_polymorphic_pind ind env ->
	      (* Template sort-polymorphism of inductive types *)
	    let args = Array.map (fun t -> lazy t) argst in
	      judge_of_inductive_knowing_parameters env ind args
	  | Const cst when Environ.template_polymorphic_pconstant cst env ->
	      (* Template sort-polymorphism of constants *)
	    let args = Array.map (fun t -> lazy t) argst in
	      judge_of_constant_knowing_parameters env cst args
	  | _ ->
	    (* Full or no sort-polymorphism *)
	    execute env f
	in

	  judge_of_apply env f ft args argst

    | Lambda (name,c1,c2) ->
      let _ = execute_is_type env c1 in
      let env1 = push_rel (name,None,c1) env in
      let c2t = execute env1 c2 in
        judge_of_abstraction env name c1 c2t

    | Prod (name,c1,c2) ->
      let vars = execute_is_type env c1 in
      let env1 = push_rel (name,None,c1) env in
      let vars' = execute_is_type env1 c2 in
	judge_of_product env name vars vars'

    | LetIn (name,c1,c2,c3) ->
      let c1t = execute env c1 in
      let _c2s = execute_is_type env c2 in
      let _ = judge_of_cast env c1 c1t DEFAULTcast c2 in
      let env1 = push_rel (name,Some c1,c2) env in
      let c3t = execute env1 c3 in
	subst1 c1 c3t

    | Cast (c,k,t) ->
      let ct = execute env c in
      let _ts = execute_type env t in
      let _ = judge_of_cast env c ct k t in
	t

    (* Inductive types *)
    | Ind ind ->
      judge_of_inductive env ind

    | Construct c ->
      judge_of_constructor env c

    | Case (ci,p,c,lf) ->
        let ct = execute env c in
        let pt = execute env p in
        let lft = execute_array env lf in
          judge_of_case env ci p pt c ct lf lft

    | Fix ((vn,i as vni),recdef) ->
      let (fix_ty,recdef') = execute_recdef env recdef i in
      let fix = (vni,recdef') in
        check_fix env fix; fix_ty
	  
    | CoFix (i,recdef) ->
      let (fix_ty,recdef') = execute_recdef env recdef i in
      let cofix = (i,recdef') in
        check_cofix env cofix; fix_ty
	  
    (* Partial proofs: unsupported by the kernel *)
    | Meta _ ->
	anomaly (Pp.str "the kernel does not support metavariables")

    | Evar _ ->
	anomaly (Pp.str "the kernel does not support existential variables")

and execute_is_type env constr =
  let t = execute env constr in
    check_type env constr t

and execute_type env constr =
  let t = execute env constr in
    type_judgment env constr t

and execute_recdef env (names,lar,vdef) i =
  let lart = execute_array env lar in
  let lara = Array.map2 (assumption_of_judgment env) lar lart in
  let env1 = push_rec_types (names,lara,vdef) env in
  let vdeft = execute_array env1 vdef in
  let () = type_fixpoint env1 names lara vdef vdeft in
    (lara.(i),(names,lara,vdef))

and execute_array env = Array.map (execute env)

(* Derived functions *)
let infer env constr =
  let t = execute env constr in
    make_judge constr t

let infer = 
  if Flags.profile then
    let infer_key = Profile.declare_profile "Fast_infer" in
      Profile.profile2 infer_key infer
  else infer

let infer_type env constr =
  execute_type env constr

let infer_v env cv =
  let jv = execute_array env cv in
    make_judgev cv jv
