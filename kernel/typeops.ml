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
open Univ
open Term
open Declarations
open Sign
open Environ
open Entries
open Reduction
open Inductive
open Type_errors


(* This should be a type (a priori without intension to be an assumption) *)
let type_judgment env j =
  match kind_of_term(whd_betadeltaiota env (body_of_type j.uj_type)) with
    | Sort s -> {utj_val = j.uj_val; utj_type = s }
    | _ -> error_not_type env j

(* This should be a type intended to be assumed. The error message is *)
(* not as useful as for [type_judgment]. *)
let assumption_of_judgment env j =
  try (type_judgment env j).utj_val
  with TypeError _ ->
    error_assumption env j

(*
let aojkey = Profile.declare_profile "assumption_of_judgment";;
let assumption_of_judgment env j
  = Profile.profile2 aojkey assumption_of_judgment env j;;
*)

(************************************************)
(* Incremental typing rules: builds a typing judgement given the *)
(* judgements for the subterms. *)

(*s Type of sorts *)

(* Prop and Set *)

let judge_of_prop =
  { uj_val = body_of_type mkProp;
    uj_type = mkSort type_0 }

let judge_of_set =
  { uj_val = body_of_type mkSet;
    uj_type = mkSort type_0 }

let judge_of_prop_contents = function
  | Null -> judge_of_prop
  | Pos -> judge_of_set

(* Type of Type(i). *)

let judge_of_type u =
  let uu = super u in
  { uj_val = body_of_type (mkType u);
    uj_type = mkType uu }

(*s Type of a de Bruijn index. *)
	  
let judge_of_relative env n = 
  try
    let (_,_,typ) = lookup_rel n env in
    { uj_val  = mkRel n;
      uj_type = type_app (lift n) typ }
  with Not_found -> 
    error_unbound_rel env n

(*
let relativekey = Profile.declare_profile "judge_of_relative";;
let judge_of_relative env n =
  Profile.profile2 relativekey judge_of_relative env n;;
*)

(* Type of variables *)
let judge_of_variable env id =
  try
    let (_,_,ty) = lookup_named id env in
    make_judge (mkVar id) ty
  with Not_found -> 
    error_unbound_var env id

(* Management of context of variables. *)

(* Checks if a context of variable can be instanciated by the
   variables of the current env *)
(* TODO: check order? *)
let rec check_hyps_inclusion env sign =
  let env_sign = named_context env in
  Sign.fold_named_context
    (fun (id,_,ty1) () ->
      let (_,_,ty2) = Sign.lookup_named id env_sign in
      if not (eq_constr ty2 ty1) then
        error "types do not match")
    sign
    ~init:()


let check_args env c hyps =
  let hyps' = named_context env in
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

(* Type of constants *)
let judge_of_constant env cst =
  let constr = mkConst cst in
  let _ =
    let ce = lookup_constant cst env in
    check_args env constr ce.const_hyps in 
  make_judge constr (constant_type env cst)

(*
let tockey = Profile.declare_profile "type_of_constant";;
let type_of_constant env c 
  = Profile.profile3 tockey type_of_constant env c;;
*)

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
    uj_type = type_app (subst1 defj.uj_val) j.uj_type }

(* Type of an application. *)

let judge_of_apply env funj argjv =
  let rec apply_rec n typ cst = function
    | [] -> 
	{ uj_val  = mkApp (j_val funj, Array.map j_val argjv);
          uj_type = typ },
	cst
    | hj::restjl ->
        (match kind_of_term (whd_betadeltaiota env typ) with
          | Prod (_,c1,c2) ->
	      (try 
		let c = conv_leq env hj.uj_type c1 in
		let cst' = Constraint.union cst c in
		apply_rec (n+1) (subst1 hj.uj_val c2) cst' restjl
	      with NotConvertible -> 
		error_cant_apply_bad_type env
		  (n,c1, hj.uj_type)
		  funj argjv)

          | _ ->
	      error_cant_apply_not_functional env funj argjv)
  in 
  apply_rec 1
    funj.uj_type
    Constraint.empty
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
        if engagement env = Some ImpredicativeSet then
          (* Rule is (Type,Set,Set) in the Set-impredicative calculus *)
          rangsort
        else
          (* Rule is (Type_i,Set,Type_i) in the Set-predicative calculus *)
          domsort
    (* Product rule (Prop,Type_i,Type_i) *)
    | (Prop _,  Type _)  -> rangsort
    (* Product rule (Type_i,Type_i,Type_i) *) 
    | (Type u1, Type u2) -> Type (sup u1 u2)

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

let judge_of_cast env cj tj =
  let expected_type = tj.utj_val in
  try 
    let cst = conv_leq env cj.uj_type expected_type in
    { uj_val = mkCast (j_val cj, expected_type);
      uj_type = expected_type },
    cst
  with NotConvertible ->
    error_actual_type env cj expected_type

(* Inductive types. *)

let judge_of_inductive env i =
  let constr = mkInd i in
  let _ =
    let (kn,_) = i in
    let mib = lookup_mind kn env in
    check_args env constr mib.mind_hyps in 
  make_judge constr (type_of_inductive env i)

(*
let toikey = Profile.declare_profile "judge_of_inductive";;
let judge_of_inductive env i
  = Profile.profile2 toikey judge_of_inductive env i;;
*)

(* Constructors. *)

let judge_of_constructor env c =
  let constr = mkConstruct c in
  let _ =
    let ((kn,_),_) = c in
    let mib = lookup_mind kn env in
    check_args env constr mib.mind_hyps in 
  make_judge constr (type_of_constructor env c)

(*
let tockey = Profile.declare_profile "judge_of_constructor";;
let judge_of_constructor env cstr
  = Profile.profile2 tockey judge_of_constructor env cstr;;
*)

(* Case. *)

let check_branch_types env cj (lft,explft) = 
  try conv_leq_vecti env lft explft
  with
      NotConvertibleVect i ->
        error_ill_formed_branch env cj.uj_val i lft.(i) explft.(i)
    | Invalid_argument _ ->
        error_number_branches env cj (Array.length explft)

let judge_of_case env ci pj cj lfj =
  let indspec =
    try find_rectype env cj.uj_type
    with Not_found -> error_case_not_inductive env cj in
  let _ = check_case_info env (fst indspec) ci in
  let (bty,rslty,univ) =
    type_case_branches env indspec pj cj.uj_val in
  let (_,kind) = dest_arity env pj.uj_type in
  let lft = Array.map j_type lfj in
  let univ' = check_branch_types env cj (lft,bty) in
  ({ uj_val  = mkCase (ci, (*nf_betaiota*) pj.uj_val, cj.uj_val,
                       Array.map j_val lfj);
     uj_type = rslty },
  Constraint.union univ univ')

(*
let tocasekey = Profile.declare_profile "judge_of_case";;
let judge_of_case env ci pj cj lfj
  = Profile.profile6 tocasekey judge_of_case env ci pj cj lfj;;
*)

(* Fixpoints. *)

(* Checks the type of a general (co)fixpoint, i.e. without checking *)
(* the specific guard condition. *)

let type_fixpoint env lna lar vdefj =
  let lt = Array.length vdefj in
  assert (Array.length lar = lt);
  try
    conv_leq_vecti env
      (Array.map (fun j -> body_of_type j.uj_type) vdefj)
      (Array.map (fun ty -> lift lt ty) lar)
  with NotConvertibleVect i ->
    error_ill_typed_rec_body env i lna vdefj lar

(************************************************************************)
(************************************************************************)

(* This combinator adds the universe constraints both in the local
   graph and in the universes of the environment. This is to ensure
   that the infered local graph is satisfiable. *)
let univ_combinator (cst,univ) (j,c') =
  (j,(Constraint.union cst c', merge_constraints c' univ))

(* The typing machine. *)
    (* ATTENTION : faudra faire le typage du contexte des Const,
    Ind et Constructsi un jour cela devient des constructions
    arbitraires et non plus des variables *)
let rec execute env cstr cu =
  match kind_of_term cstr with
    (* Atomic terms *)
    | Sort (Prop c) -> 
	(judge_of_prop_contents c, cu)

    | Sort (Type u) ->
	(judge_of_type u, cu)

    | Rel n -> 
	(judge_of_relative env n, cu)

    | Var id -> 
	(judge_of_variable env id, cu)

    | Const c ->
        (judge_of_constant env c, cu)

    (* Lambda calculus operators *)
    | App (f,args) ->
	let (j,cu1) = execute env f cu in
        let (jl,cu2) = execute_array env args cu1 in
	univ_combinator cu2
	  (judge_of_apply env j jl)
	    
    | Lambda (name,c1,c2) -> 
        let (varj,cu1) = execute_type env c1 cu in
	let env1 = push_rel (name,None,varj.utj_val) env in
        let (j',cu2) = execute env1 c2 cu1 in 
        (judge_of_abstraction env name varj j', cu2)
	  
    | Prod (name,c1,c2) ->
        let (varj,cu1) = execute_type env c1 cu in
	let env1 = push_rel (name,None,varj.utj_val) env in
        let (varj',cu2) = execute_type env1 c2 cu1 in
	(judge_of_product env name varj varj', cu2)

    | LetIn (name,c1,c2,c3) ->
        let (j1,cu1) = execute env c1 cu in
        let (j2,cu2) = execute_type env c2 cu1 in
        let (_,cu3) = univ_combinator cu2 (judge_of_cast env j1 j2) in
        let env1 = push_rel (name,Some j1.uj_val,j2.utj_val) env in
        let (j',cu4) = execute env1 c3 cu3 in
        (judge_of_letin env name j1 j2 j', cu4)
	  
    | Cast (c,t) ->
        let (cj,cu1) = execute env c cu in
        let (tj,cu2) = execute_type env t cu1 in
	univ_combinator cu2
          (judge_of_cast env cj tj)

    (* Inductive types *)
    | Ind ind ->
	(judge_of_inductive env ind, cu)

    | Construct c -> 
	(judge_of_constructor env c, cu)

    | Case (ci,p,c,lf) ->
        let (cj,cu1) = execute env c cu in
        let (pj,cu2) = execute env p cu1 in
        let (lfj,cu3) = execute_array env lf cu2 in
        univ_combinator cu3
          (judge_of_case env ci pj cj lfj)
  
    | Fix ((vn,i as vni),recdef) ->
        let ((fix_ty,recdef'),cu1) = execute_recdef env recdef i cu in
        let fix = (vni,recdef') in
        check_fix env fix;
	(make_judge (mkFix fix) fix_ty, cu1)
	  
    | CoFix (i,recdef) ->
        let ((fix_ty,recdef'),cu1) = execute_recdef env recdef i cu in
        let cofix = (i,recdef') in
        check_cofix env cofix;
	(make_judge (mkCoFix cofix) fix_ty, cu1)

    (* Partial proofs: unsupported by the kernel *)
    | Meta _ ->
	anomaly "the kernel does not support metavariables"

    | Evar _ ->
	anomaly "the kernel does not support existential variables"

and execute_type env constr cu = 
  let (j,cu1) = execute env constr cu in
  (type_judgment env j, cu1)
	  
and execute_recdef env (names,lar,vdef) i cu =
  let (larj,cu1) = execute_array env lar cu in
  let lara = Array.map (assumption_of_judgment env) larj in
  let env1 = push_rec_types (names,lara,vdef) env in
  let (vdefj,cu2) = execute_array env1 vdef cu1 in
  let vdefv = Array.map j_val vdefj in
  let cst = type_fixpoint env1 names lara vdefj in
  univ_combinator cu2
    ((lara.(i),(names,lara,vdefv)),cst)

and execute_array env v cu =
  let (jl,cu1) = execute_list env (Array.to_list v) cu in
  (Array.of_list jl, cu1)

and execute_list env l cu =
  match l with
  | [] -> 
      ([], cu)
  | c::r -> 
      let (j,cu1) = execute env c cu in 
      let (jr,cu2) = execute_list env r cu1 in
      (j::jr, cu2)

(* Derived functions *)
let infer env constr =
  let (j,(cst,_)) =
    execute env constr (Constraint.empty, universes env) in
  let j = if j.uj_val = constr then { j with uj_val = constr } else
    (error "Kernel built a body different from its input\n";
     flush stdout; j) in
  (j, cst)

let infer_type env constr =
  let (j,(cst,_)) =
    execute_type env constr (Constraint.empty, universes env) in
  (j, cst)

let infer_v env cv =
  let (jv,(cst,_)) =
    execute_array env cv (Constraint.empty, universes env) in
  (jv, cst)
 
(* Typing of several terms. *)

let infer_local_decl env id = function
  | LocalDef c -> 
      let (j,cst) = infer env c in
      (Name id, Some j.uj_val, j.uj_type), cst
  | LocalAssum c ->
      let (j,cst) = infer env c in
      (Name id, None, assumption_of_judgment env j), cst

let infer_local_decls env decls =
  let rec inferec env = function
  | (id, d) :: l -> 
      let env, l, cst1 = inferec env l in
      let d, cst2 = infer_local_decl env id d in
      push_rel d env, add_rel_decl d l, Constraint.union cst1 cst2
  | [] -> env, empty_rel_context, Constraint.empty in
  inferec env decls

(* Exported typing functions *)

let typing env c = 
  let (j,cst) = infer env c in
  let _ = add_constraints cst env in
  j
