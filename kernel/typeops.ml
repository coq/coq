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
open Context
open Declarations
open Environ
open Entries
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
let type_judgment env j =
  match kind_of_term(whd_betadeltaiota env j.uj_type) with
    | Sort s -> {utj_val = j.uj_val; utj_type = s }
    | _ -> error_not_type env j

(* This should be a type intended to be assumed. The error message is *)
(* not as useful as for [type_judgment]. *)
let assumption_of_judgment env j =
  try (type_judgment env j).utj_val
  with TypeError _ ->
    error_assumption env j

(************************************************)
(* Incremental typing rules: builds a typing judgement given the *)
(* judgements for the subterms. *)

(*s Type of sorts *)

(* Prop and Set *)

let judge_of_prop =
  { uj_val = mkProp;
    uj_type = mkSort type1_sort }

let judge_of_set =
  { uj_val = mkSet;
    uj_type = mkSort type1_sort }

let judge_of_prop_contents = function
  | Null -> judge_of_prop
  | Pos -> judge_of_set

(* Type of Type(i). *)

let judge_of_type u =
  let uu = Universe.super u in
    { uj_val = mkType u;
      uj_type = mkType uu }

(*s Type of a de Bruijn index. *)

let judge_of_relative env n =
  try
    let (_,_,typ) = lookup_rel n env in
    { uj_val  = mkRel n;
      uj_type = lift n typ }
  with Not_found ->
    error_unbound_rel env n

(* Type of variables *)
let judge_of_variable env id =
  try
    let ty = named_type id env in
    make_judge (mkVar id) ty
  with Not_found ->
    error_unbound_var env id

(* Management of context of variables. *)

(* Checks if a context of variables can be instantiated by the
   variables of the current env.
   Order does not have to be checked assuming that all names are distinct *)
let check_hyps_inclusion env c sign =
  Context.fold_named_context
    (fun (id,b1,ty1) () ->
      try
        let (_,b2,ty2) = lookup_named id env in
        conv env ty2 ty1;
        (match b2,b1 with
        | None, None -> ()
        | None, Some _ ->
            (* This is wrong, because we don't know if the body is
               needed or not for typechecking: *) ()
        | Some _, None -> raise NotConvertible
        | Some b2, Some b1 -> conv env b2 b1);
      with Not_found | NotConvertible | Option.Heterogeneous ->
        error_reference_variables env id c)
    sign
    ~init:()

(* Instantiation of terms on real arguments. *)

(* Make a type polymorphic if an arity *)

let extract_level env p =
  let _,c = dest_prod_assum env p in
  match kind_of_term c with Sort (Type u) -> Univ.Universe.level u | _ -> None

let extract_context_levels env l =
  let fold l (_, b, p) = match b with
  | None -> extract_level env p :: l
  | _ -> l
  in
  List.fold_left fold [] l

let make_polymorphic_if_constant_for_ind env {uj_val = c; uj_type = t} =
  let params, ccl = dest_prod_assum env t in
  match kind_of_term ccl with
  | Sort (Type u) when isInd (fst (decompose_app (whd_betadeltaiota env c))) ->
      let param_ccls = extract_context_levels env params in
      let s = { template_param_levels = param_ccls; template_level = u} in
      TemplateArity (params,s)
  | _ ->
      RegularArity t

(* Type of constants *)

let type_of_constant_type_knowing_parameters env t paramtyps =
  match t with
  | RegularArity t -> t
  | TemplateArity (sign,ar) ->
      let ctx = List.rev sign in
      let ctx,s = instantiate_universes env ctx ar paramtyps in
      mkArity (List.rev ctx,s)

let type_of_constant_knowing_parameters env cst paramtyps =
  let cb = lookup_constant (fst cst) env in
  let _ = check_hyps_inclusion env (mkConstU cst) cb.const_hyps in
  let ty, cu = constant_type env cst in
    type_of_constant_type_knowing_parameters env ty paramtyps, cu

let type_of_constant_knowing_parameters_in env cst paramtyps =
  let cb = lookup_constant (fst cst) env in
  let _ = check_hyps_inclusion env (mkConstU cst) cb.const_hyps in
  let ty = constant_type_in env cst in
    type_of_constant_type_knowing_parameters env ty paramtyps

let type_of_constant_type env t =
  type_of_constant_type_knowing_parameters env t [||]

let type_of_constant env cst =
  type_of_constant_knowing_parameters env cst [||]

let type_of_constant_in env cst =
  let cb = lookup_constant (fst cst) env in
  let _ = check_hyps_inclusion env (mkConstU cst) cb.const_hyps in
  let ar = constant_type_in env cst in
    type_of_constant_type_knowing_parameters env ar [||]

let judge_of_constant_knowing_parameters env (kn,u as cst) args =
  let c = mkConstU cst in
  let ty, cu = type_of_constant_knowing_parameters env cst args in
  let _ = Environ.check_constraints cu env in
    make_judge c ty

let judge_of_constant env cst =
  judge_of_constant_knowing_parameters env cst [||]

let type_of_projection env (p,u) =
  let cst = Projection.constant p in
  let cb = lookup_constant cst env in
  match cb.const_proj with
  | Some pb -> 
    if cb.const_polymorphic then
      Vars.subst_instance_constr u pb.proj_type
    else pb.proj_type
  | None -> raise (Invalid_argument "type_of_projection: not a projection")


(* Type of a lambda-abstraction. *)

(* [judge_of_abstraction env name var j] implements the rule

 env, name:typ |- j.uj_val:j.uj_type     env, |- (name:typ)j.uj_type : s
 -----------------------------------------------------------------------
          env |- [name:typ]j.uj_val : (name:typ)j.uj_type

  Since all products are defined in the Calculus of Inductive Constructions
  and no upper constraint exists on the sort $s$, we don't need to compute $s$
*)

let judge_of_abstraction env name var j =
  { uj_val = mkLambda (name, var.utj_val, j.uj_val);
    uj_type = mkProd (name, var.utj_val, j.uj_type) }

(* Type of let-in. *)

let judge_of_letin env name defj typj j =
  { uj_val = mkLetIn (name, defj.uj_val, typj.utj_val, j.uj_val) ;
    uj_type = subst1 defj.uj_val j.uj_type }

(* Type of an application. *)

let judge_of_apply env funj argjv =
  let rec apply_rec n typ = function
    | [] ->
	{ uj_val  = mkApp (j_val funj, Array.map j_val argjv);
          uj_type = typ }
    | hj::restjl ->
        (match kind_of_term (whd_betadeltaiota env typ) with
          | Prod (_,c1,c2) ->
	      (try
		 let () = conv_leq false env hj.uj_type c1 in
		   apply_rec (n+1) (subst1 hj.uj_val c2) restjl
	      with NotConvertible ->
		error_cant_apply_bad_type env
		  (n,c1, hj.uj_type)
		  funj argjv)

          | _ ->
	      error_cant_apply_not_functional env funj argjv)
  in
  apply_rec 1
    funj.uj_type
    (Array.to_list argjv)

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
let judge_of_product env name t1 t2 =
  let s = sort_of_product env t1.utj_type t2.utj_type in
  { uj_val = mkProd (name, t1.utj_val, t2.utj_val);
    uj_type = mkSort s }

(* Type of a type cast *)

(* [judge_of_cast env (c,typ1) (typ2,s)] implements the rule

    env |- c:typ1    env |- typ2:s    env |- typ1 <= typ2
    ---------------------------------------------------------------------
         env |- c:typ2
*)

let judge_of_cast env cj k tj =
  let expected_type = tj.utj_val in
  try
    let c, cst =
      match k with
      | VMcast ->
          mkCast (cj.uj_val, k, expected_type),
          vm_conv CUMUL env cj.uj_type expected_type
      | DEFAULTcast ->
          mkCast (cj.uj_val, k, expected_type),
          default_conv ~l2r:false CUMUL env cj.uj_type expected_type
      | REVERTcast ->
          cj.uj_val,
          default_conv ~l2r:true CUMUL env cj.uj_type expected_type
      | NATIVEcast ->
	 let sigma = Nativelambda.empty_evars in
         mkCast (cj.uj_val, k, expected_type),
         native_conv CUMUL sigma env cj.uj_type expected_type
    in
      { uj_val = c;
	uj_type = expected_type }
  with NotConvertible ->
    error_actual_type env cj expected_type

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
  let c = mkIndU indu in
  let (mib,mip) as spec = lookup_mind_specif env ind in
  check_hyps_inclusion env c mib.mind_hyps;
  let t,cst = Inductive.constrained_type_of_inductive_knowing_parameters 
    env (spec,u) args
  in
    check_constraints cst env;
    make_judge c t

let judge_of_inductive env (ind,u as indu) =
  let c = mkIndU indu in
  let (mib,mip) as spec = lookup_mind_specif env ind in
  check_hyps_inclusion env c mib.mind_hyps;
  let t,cst = Inductive.constrained_type_of_inductive env (spec,u) in
    check_constraints cst env;
    (make_judge c t)

(* Constructors. *)

let judge_of_constructor env (c,u as cu) =
  let constr = mkConstructU cu in
  let _ =
    let ((kn,_),_) = c in
    let mib = lookup_mind kn env in
    check_hyps_inclusion env constr mib.mind_hyps in
  let specif = lookup_mind_specif env (inductive_of_constructor c) in
  let t,cst = constrained_type_of_constructor cu specif in
  let () = check_constraints cst env in
    (make_judge constr t)

(* Case. *)

let check_branch_types env (ind,u) cj (lfj,explft) =
  try conv_leq_vecti env (Array.map j_type lfj) explft
  with
      NotConvertibleVect i ->
        error_ill_formed_branch env cj.uj_val ((ind,i+1),u) lfj.(i).uj_type explft.(i)
    | Invalid_argument _ ->
        error_number_branches env cj (Array.length explft)

let judge_of_case env ci pj cj lfj =
  let (pind, _ as indspec) =
    try find_rectype env cj.uj_type
    with Not_found -> error_case_not_inductive env cj in
  let _ = check_case_info env pind ci in
  let (bty,rslty) =
    type_case_branches env indspec pj cj.uj_val in
  let () = check_branch_types env pind cj (lfj,bty) in
  ({ uj_val  = mkCase (ci, (*nf_betaiota*) pj.uj_val, cj.uj_val,
                       Array.map j_val lfj);
     uj_type = rslty })

let judge_of_projection env p cj =
  let pb = lookup_projection p env in
  let (ind,u), args =
    try find_rectype env cj.uj_type
    with Not_found -> error_case_not_inductive env cj
  in
    assert(eq_mind pb.proj_ind (fst ind));
    let ty = Vars.subst_instance_constr u pb.Declarations.proj_type in
    let ty = substl (cj.uj_val :: List.rev args) ty in
      {uj_val = mkProj (p,cj.uj_val);
       uj_type = ty}

(* Fixpoints. *)

(* Checks the type of a general (co)fixpoint, i.e. without checking *)
(* the specific guard condition. *)

let type_fixpoint env lna lar vdefj =
  let lt = Array.length vdefj in
  assert (Int.equal (Array.length lar) lt);
  try
    conv_leq_vecti env (Array.map j_type vdefj) (Array.map (fun ty -> lift lt ty) lar)
  with NotConvertibleVect i ->
    error_ill_typed_rec_body env i lna vdefj lar

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
        let cj = execute env c in
          judge_of_projection env p cj

    (* Lambda calculus operators *)
    | App (f,args) ->
        let jl = execute_array env args in
	let j =
	  match kind_of_term f with
	    | Ind ind when Environ.template_polymorphic_pind ind env ->
		(* Sort-polymorphism of inductive types *)
	      let args = Array.map (fun j -> lazy j.uj_type) jl in
		judge_of_inductive_knowing_parameters env ind args
	    | Const cst when Environ.template_polymorphic_pconstant cst env ->
		(* Sort-polymorphism of constant *)
	      let args = Array.map (fun j -> lazy j.uj_type) jl in
		judge_of_constant_knowing_parameters env cst args
	    | _ ->
		(* No sort-polymorphism *)
		execute env f
	in
	  judge_of_apply env j jl

    | Lambda (name,c1,c2) ->
      let varj = execute_type env c1 in
      let env1 = push_rel (name,None,varj.utj_val) env in
      let j' = execute env1 c2 in
        judge_of_abstraction env name varj j'

    | Prod (name,c1,c2) ->
      let varj = execute_type env c1 in
      let env1 = push_rel (name,None,varj.utj_val) env in
      let varj' = execute_type env1 c2 in
	judge_of_product env name varj varj'

    | LetIn (name,c1,c2,c3) ->
      let j1 = execute env c1 in
      let j2 = execute_type env c2 in
      let _ = judge_of_cast env j1 DEFAULTcast j2 in
      let env1 = push_rel (name,Some j1.uj_val,j2.utj_val) env in
      let j' = execute env1 c3 in
        judge_of_letin env name j1 j2 j'

    | Cast (c,k, t) ->
      let cj = execute env c in
      let tj = execute_type env t in
        judge_of_cast env cj k tj

    (* Inductive types *)
    | Ind ind ->
      judge_of_inductive env ind

    | Construct c ->
      judge_of_constructor env c

    | Case (ci,p,c,lf) ->
        let cj = execute env c in
        let pj = execute env p in
        let lfj = execute_array env lf in
          judge_of_case env ci pj cj lfj

    | Fix ((vn,i as vni),recdef) ->
      let (fix_ty,recdef') = execute_recdef env recdef i in
      let fix = (vni,recdef') in
        check_fix env fix;
	make_judge (mkFix fix) fix_ty
	  
    | CoFix (i,recdef) ->
      let (fix_ty,recdef') = execute_recdef env recdef i in
      let cofix = (i,recdef') in
        check_cofix env cofix;
	(make_judge (mkCoFix cofix) fix_ty)
	  
    (* Partial proofs: unsupported by the kernel *)
    | Meta _ ->
	anomaly (Pp.str "the kernel does not support metavariables")

    | Evar _ ->
	anomaly (Pp.str "the kernel does not support existential variables")

and execute_type env constr =
  let j = execute env constr in
    type_judgment env j

and execute_recdef env (names,lar,vdef) i =
  let larj = execute_array env lar in
  let lara = Array.map (assumption_of_judgment env) larj in
  let env1 = push_rec_types (names,lara,vdef) env in
  let vdefj = execute_array env1 vdef in
  let vdefv = Array.map j_val vdefj in
  let () = type_fixpoint env1 names lara vdefj in
    (lara.(i),(names,lara,vdefv))

and execute_array env = Array.map (execute env)

(* Derived functions *)
let infer env constr =
  let j = execute env constr in
    assert (eq_constr j.uj_val constr);
    j

(* let infer_key = Profile.declare_profile "infer" *)
(* let infer = Profile.profile2 infer_key infer *)

let infer_type env constr =
  let j = execute_type env constr in
    j

let infer_v env cv =
  let jv = execute_array env cv in
    jv

(* Typing of several terms. *)

let infer_local_decl env id = function
  | LocalDef c ->
      let j = infer env c in
      (Name id, Some j.uj_val, j.uj_type)
  | LocalAssum c ->
      let j = infer env c in
      (Name id, None, assumption_of_judgment env j)

let infer_local_decls env decls =
  let rec inferec env = function
  | (id, d) :: l ->
      let (env, l) = inferec env l in
      let d = infer_local_decl env id d in
	(push_rel d env, add_rel_decl d l)
  | [] -> (env, empty_rel_context) in
  inferec env decls
