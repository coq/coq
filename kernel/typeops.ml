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
open Univ
open Sorts
open Constr
open Vars
open Declarations
open Environ
open Reduction
open Inductive
open Type_errors

module RelDecl = Context.Rel.Declaration
module NamedDecl = Context.Named.Declaration

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

(* This should be a type (a priori without intention to be an assumption) *)
let check_type env c t =
  match kind(whd_all env t) with
  | Sort s -> s
  | _ -> error_not_type env (make_judge c t)

(* This should be a type intended to be assumed. The error message is
   not as useful as for [type_judgment]. *)
let check_assumption env t ty =
  try let _ = check_type env t ty in t
  with TypeError _ ->
    error_assumption env (make_judge t ty)

(************************************************)
(* Incremental typing rules: builds a typing judgment given the *)
(* judgments for the subterms. *)

(*s Type of sorts *)

(* Prop and Set *)

let type1 = mkSort Sorts.type1

(* Type of Type(i). *)

let type_of_type u =
  let uu = Universe.super u in
    mkType uu

let type_of_sort = function
  | Prop | Set -> type1
  | Type u -> type_of_type u

(*s Type of a de Bruijn index. *)

let type_of_relative env n =
  try
    env |> lookup_rel n |> RelDecl.get_type |> lift n
  with Not_found ->
    error_unbound_rel env n

(* Type of variables *)
let type_of_variable env id =
  try named_type id env
  with Not_found ->
    error_unbound_var env id

(* Management of context of variables. *)

(* Checks if a context of variables can be instantiated by the
   variables of the current env.
   Order does not have to be checked assuming that all names are distinct *)
let check_hyps_inclusion env f c sign =
  Context.Named.fold_outside
    (fun d1 () ->
      let open Context.Named.Declaration in
      let id = NamedDecl.get_id d1 in
      try
        let d2 = lookup_named id env in
        conv env (get_type d2) (get_type d1);
        (match d2,d1 with
        | LocalAssum _, LocalAssum _ -> ()
        | LocalAssum _, LocalDef _ ->
            (* This is wrong, because we don't know if the body is
               needed or not for typechecking: *) ()
        | LocalDef _, LocalAssum _ -> raise NotConvertible
        | LocalDef (_,b2,_), LocalDef (_,b1,_) -> conv env b2 b1);
      with Not_found | NotConvertible | Option.Heterogeneous ->
        error_reference_variables env id (f c))
    sign
    ~init:()

(* Instantiation of terms on real arguments. *)

(* Make a type polymorphic if an arity *)

(* Type of constants *)


let type_of_constant env (kn,u as cst) =
  let cb = lookup_constant kn env in
  let () = check_hyps_inclusion env mkConstU cst cb.const_hyps in
  let ty, cu = constant_type env cst in
  let () = check_constraints cu env in
    ty

let type_of_constant_in env (kn,u as cst) =
  let cb = lookup_constant kn env in
  let () = check_hyps_inclusion env mkConstU cst cb.const_hyps in
  constant_type_in env cst

(* Type of a lambda-abstraction. *)

(* [judge_of_abstraction env name var j] implements the rule

 env, name:typ |- j.uj_val:j.uj_type     env, |- (name:typ)j.uj_type : s
 -----------------------------------------------------------------------
          env |- [name:typ]j.uj_val : (name:typ)j.uj_type

  Since all products are defined in the Calculus of Inductive Constructions
  and no upper constraint exists on the sort $s$, we don't need to compute $s$
*)

let type_of_abstraction env name var ty =
  mkProd (name, var, ty)

(* Type of an application. *)

let make_judgev c t = 
  Array.map2 make_judge c t

let type_of_apply env func funt argsv argstv =
  let len = Array.length argsv in
  let rec apply_rec i typ = 
    if Int.equal i len then typ
    else 
      (match kind (whd_all env typ) with
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
    | (_,       Prop)  -> rangsort
    (* Product rule (Prop/Set,Set,Set) *)
    | ((Prop | Set),  Set) -> rangsort
    (* Product rule (Type,Set,?) *)
    | (Type u1, Set) ->
        if is_impredicative_set env then
          (* Rule is (Type,Set,Set) in the Set-impredicative calculus *)
          rangsort
        else
          (* Rule is (Type_i,Set,Type_i) in the Set-predicative calculus *)
          Type (Universe.sup Universe.type0 u1)
    (* Product rule (Prop,Type_i,Type_i) *)
    | (Set,  Type u2)  -> Type (Universe.sup Universe.type0 u2)
    (* Product rule (Prop,Type_i,Type_i) *)
    | (Prop, Type _)  -> rangsort
    (* Product rule (Type_i,Type_i,Type_i) *)
    | (Type u1, Type u2) -> Type (Universe.sup u1 u2)

(* [judge_of_product env name (typ1,s1) (typ2,s2)] implements the rule

    env |- typ1:s1       env, name:typ1 |- typ2 : s2
    -------------------------------------------------------------------------
         s' >= (s1,s2), env |- (name:typ)j.uj_val : s'

  where j.uj_type is convertible to a sort s2
*)
let type_of_product env name s1 s2 =
  let s = sort_of_product env s1 s2 in
    mkSort s

(* Type of a type cast *)

(* [judge_of_cast env (c,typ1) (typ2,s)] implements the rule

    env |- c:typ1    env |- typ2:s    env |- typ1 <= typ2
    ---------------------------------------------------------------------
         env |- c:typ2
*)

let check_cast env c ct k expected_type =
  try
    match k with
    | VMcast ->
      Vconv.vm_conv CUMUL env ct expected_type
    | DEFAULTcast ->
      default_conv ~l2r:false CUMUL env ct expected_type
    | REVERTcast ->
      default_conv ~l2r:true CUMUL env ct expected_type
    | NATIVEcast ->
      let sigma = Nativelambda.empty_evars in
      Nativeconv.native_conv CUMUL sigma env ct expected_type
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

let type_of_inductive_knowing_parameters env (ind,u as indu) args =
  let (mib,mip) as spec = lookup_mind_specif env ind in
  check_hyps_inclusion env mkIndU indu mib.mind_hyps;
  let t,cst = Inductive.constrained_type_of_inductive_knowing_parameters 
    env (spec,u) args
  in
  check_constraints cst env;
  t

let type_of_inductive env (ind,u as indu) =
  let (mib,mip) = lookup_mind_specif env ind in
  check_hyps_inclusion env mkIndU indu mib.mind_hyps;
  let t,cst = Inductive.constrained_type_of_inductive env ((mib,mip),u) in
  check_constraints cst env;
  t

(* Constructors. *)

let type_of_constructor env (c,u as cu) =
  let () =
    let ((kn,_),_) = c in
    let mib = lookup_mind kn env in
    check_hyps_inclusion env mkConstructU cu mib.mind_hyps
  in
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

let type_of_case env ci p pt c ct lf lft =
  let (pind, _ as indspec) =
    try find_rectype env ct
    with Not_found -> error_case_not_inductive env (make_judge c ct) in
  let () = check_case_info env pind ci in
  let (bty,rslty) =
    type_case_branches env indspec (make_judge p pt) c in
  let () = check_branch_types env pind c ct lft bty in
  rslty

let type_of_projection env p c ct =
  let pty = lookup_projection p env in
  let (ind,u), args =
    try find_rectype env ct
    with Not_found -> error_case_not_inductive env (make_judge c ct)
  in
  assert(eq_ind (Projection.inductive p) ind);
  let ty = Vars.subst_instance_constr u pty in
  substl (c :: CList.rev args) ty
      

(* Fixpoints. *)

(* Checks the type of a general (co)fixpoint, i.e. without checking *)
(* the specific guard condition. *)

let check_fixpoint env lna lar vdef vdeft =
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
  let open Context.Rel.Declaration in
  match kind cstr with
    (* Atomic terms *)
    | Sort s -> type_of_sort s

    | Rel n ->
      type_of_relative env n

    | Var id ->
      type_of_variable env id

    | Const c ->
      type_of_constant env c
	
    | Proj (p, c) ->
        let ct = execute env c in
          type_of_projection env p c ct

    (* Lambda calculus operators *)
    | App (f,args) ->
        let argst = execute_array env args in
	let ft =
	  match kind f with
	  | Ind ind when Environ.template_polymorphic_pind ind env ->
	    let args = Array.map (fun t -> lazy t) argst in
              type_of_inductive_knowing_parameters env ind args
	  | _ ->
	    (* No template polymorphism *)
            execute env f
	in

          type_of_apply env f ft args argst

    | Lambda (name,c1,c2) ->
      let _ = execute_is_type env c1 in
      let env1 = push_rel (LocalAssum (name,c1)) env in
      let c2t = execute env1 c2 in
        type_of_abstraction env name c1 c2t

    | Prod (name,c1,c2) ->
      let vars = execute_is_type env c1 in
      let env1 = push_rel (LocalAssum (name,c1)) env in
      let vars' = execute_is_type env1 c2 in
        type_of_product env name vars vars'

    | LetIn (name,c1,c2,c3) ->
      let c1t = execute env c1 in
      let _c2s = execute_is_type env c2 in
      let () = check_cast env c1 c1t DEFAULTcast c2 in
      let env1 = push_rel (LocalDef (name,c1,c2)) env in
      let c3t = execute env1 c3 in
	subst1 c1 c3t

    | Cast (c,k,t) ->
      let ct = execute env c in
      let _ts = (check_type env t (execute env t)) in
      let () = check_cast env c ct k t in
	t

    (* Inductive types *)
    | Ind ind ->
      type_of_inductive env ind

    | Construct c ->
      type_of_constructor env c

    | Case (ci,p,c,lf) ->
        let ct = execute env c in
        let pt = execute env p in
        let lft = execute_array env lf in
          type_of_case env ci p pt c ct lf lft

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
	anomaly (Pp.str "the kernel does not support metavariables.")

    | Evar _ ->
	anomaly (Pp.str "the kernel does not support existential variables.")

and execute_is_type env constr =
  let t = execute env constr in
    check_type env constr t

and execute_recdef env (names,lar,vdef) i =
  let lart = execute_array env lar in
  let lara = Array.map2 (check_assumption env) lar lart in
  let env1 = push_rec_types (names,lara,vdef) env in
  let vdeft = execute_array env1 vdef in
  let () = check_fixpoint env1 names lara vdef vdeft in
    (lara.(i),(names,lara,vdef))

and execute_array env = Array.map (execute env)

(* Derived functions *)

let universe_levels_of_constr env c =
  let rec aux s c =
    match kind c with
    | Const (c, u) ->
       LSet.fold LSet.add (Instance.levels u) s
    | Ind ((mind,_), u) | Construct (((mind,_),_), u) ->
       LSet.fold LSet.add (Instance.levels u) s
    | Sort u when not (Sorts.is_small u) ->
      let u = Sorts.univ_of_sort u in
      LSet.fold LSet.add (Universe.levels u) s
    | _ -> Constr.fold aux s c
  in aux LSet.empty c

let check_wellformed_universes env c =
  let univs = universe_levels_of_constr env c in
  try UGraph.check_declared_universes (universes env) univs
  with UGraph.UndeclaredLevel u ->
    error_undeclared_universe env u

let infer env constr =
  let () = check_wellformed_universes env constr in
  let t = execute env constr in
    make_judge constr t

let infer = 
  if Flags.profile then
    let infer_key = CProfile.declare_profile "Fast_infer" in
      CProfile.profile2 infer_key (fun b c -> infer b c)
  else (fun b c -> infer b c)

let assumption_of_judgment env {uj_val=c; uj_type=t} =
  check_assumption env c t

let type_judgment env {uj_val=c; uj_type=t} =
  let s = check_type env c t in
  {utj_val = c; utj_type = s }

let infer_type env constr =
  let () = check_wellformed_universes env constr in
  let t = execute env constr in
  let s = check_type env constr t in
  {utj_val = constr; utj_type = s}

let infer_v env cv =
  let () = Array.iter (check_wellformed_universes env) cv in
  let jv = execute_array env cv in
    make_judgev cv jv

(* Typing of several terms. *)

let infer_local_decl env id = function
  | Entries.LocalDefEntry c ->
      let () = check_wellformed_universes env c in
      let t = execute env c in
      RelDecl.LocalDef (Name id, c, t)
  | Entries.LocalAssumEntry c ->
      let () = check_wellformed_universes env c in
      let t = execute env c in
      RelDecl.LocalAssum (Name id, check_assumption env c t)

let infer_local_decls env decls =
  let rec inferec env = function
  | (id, d) :: l ->
      let (env, l) = inferec env l in
      let d = infer_local_decl env id d in
        (push_rel d env, Context.Rel.add d l)
  | [] -> (env, Context.Rel.empty)
  in
  inferec env decls

let judge_of_prop = make_judge mkProp type1
let judge_of_set = make_judge mkSet type1
let judge_of_type u = make_judge (mkType u) (type_of_type u)

let judge_of_relative env k = make_judge (mkRel k) (type_of_relative env k)

let judge_of_variable env x = make_judge (mkVar x) (type_of_variable env x)

let judge_of_constant env cst = make_judge (mkConstU cst) (type_of_constant env cst)

let judge_of_projection env p cj =
  make_judge (mkProj (p,cj.uj_val)) (type_of_projection env p cj.uj_val cj.uj_type)

let dest_judgev v =
  Array.map j_val v, Array.map j_type v

let judge_of_apply env funj argjv =
  let args, argtys = dest_judgev argjv in
  make_judge (mkApp (funj.uj_val, args)) (type_of_apply env funj.uj_val funj.uj_type args argtys)

let judge_of_abstraction env x varj bodyj =
  make_judge (mkLambda (x, varj.utj_val, bodyj.uj_val))
             (type_of_abstraction env x varj.utj_val bodyj.uj_type)

let judge_of_product env x varj outj =
  make_judge (mkProd (x, varj.utj_val, outj.utj_val))
             (mkSort (sort_of_product env varj.utj_type outj.utj_type))

let judge_of_letin env name defj typj j =
  make_judge (mkLetIn (name, defj.uj_val, typj.utj_val, j.uj_val))
             (subst1 defj.uj_val j.uj_type)

let judge_of_cast env cj k tj =
  let () = check_cast env cj.uj_val cj.uj_type k tj.utj_val in
  let c = match k with | REVERTcast -> cj.uj_val | _ -> mkCast (cj.uj_val, k, tj.utj_val) in
  make_judge c tj.utj_val

let judge_of_inductive env indu =
  make_judge (mkIndU indu) (type_of_inductive env indu)

let judge_of_constructor env cu =
  make_judge (mkConstructU cu) (type_of_constructor env cu)

let judge_of_case env ci pj cj lfj =
  let lf, lft = dest_judgev lfj in
  make_judge (mkCase (ci, (*nf_betaiota*) pj.uj_val, cj.uj_val, lft))
             (type_of_case env ci pj.uj_val pj.uj_type cj.uj_val cj.uj_type lf lft)
