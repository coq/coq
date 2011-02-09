(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

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

let conv_leq = default_conv CUMUL

let conv_leq_vecti env v1 v2 =
  array_fold_left2_i
    (fun i c t1 t2 ->
      let c' =
        try default_conv CUMUL env t1 t2
        with NotConvertible -> raise (NotConvertibleVect i) in
      Constraint.union c c')
    Constraint.empty
    v1
    v2

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

let type_of_prop = mkSort type1_sort

let judge_of_prop =
  make_judge mkProp type_of_prop

let type_of_set = type_of_prop

let judge_of_set =
  make_judge mkSet type_of_set

let type_of_prop_constents _ = type_of_prop

let judge_of_prop_contents = function
  | Null -> judge_of_prop
  | Pos -> judge_of_set

(* Type of Type(i). *)

let type_of_type u = mkType (super u) 

let judge_of_type u =
  make_judge (mkType u) (type_of_type u)

(*s Type of a de Bruijn index. *)

let type_of_relative env n =
  try 
    let (_,_,typ) = lookup_rel n env in lift n typ 
  with Not_found -> 
    error_unbound_rel env n

let judge_of_relative env n =
  make_judge (mkRel n) (type_of_relative env n)

(* Type of variables *)

let type_of_variable env id =
  try named_type id env 
  with Not_found ->
    error_unbound_var env id

let judge_of_variable env id =
  make_judge (mkVar id) (type_of_variable env id)

(* Management of context of variables. *)

(* Checks if a context of variable can be instantiated by the
   variables of the current env *)
(* TODO: check order? *)
let rec check_hyps_inclusion env sign =
  Sign.fold_named_context
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
  match kind_of_term c with Sort (Type u) -> Some u | _ -> None

let extract_context_levels env =
  List.fold_left
    (fun l (_,b,p) -> if b=None then extract_level env p::l else l) []

let make_polymorphic_if_constant_for_ind env {uj_val = c; uj_type = t} =
  let params, ccl = dest_prod_assum env t in
  match kind_of_term ccl with
  | Sort (Type u) when isInd (fst (decompose_app (whd_betadeltaiota env c))) ->
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

let internal_type_of_constant_knowing_parameters env c cst paramtyps =
  let cb = lookup_constant cst env in
  let _ = check_args env c cb.const_hyps in
  type_of_constant_knowing_parameters env cb.const_type paramtyps
 
let internal_type_of_constant env c cst =
  internal_type_of_constant_knowing_parameters env c cst [||]

let judge_of_constant_knowing_parameters env cst jl =
  let c = mkConst cst in
  let paramtyps = Array.map (fun j -> j.uj_type) jl in  
  let t = internal_type_of_constant_knowing_parameters env c cst paramtyps in
  make_judge c t

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

let type_of_abstraction env name dom codom =
  mkProd (name, dom, codom)

let judge_of_abstraction env name var j =
  { uj_val = mkLambda (name, var.utj_val, j.uj_val);
    uj_type = type_of_abstraction env name var.utj_val j.uj_type }

(* Type of let-in. *)

let type_of_letin env def t = subst1 def t

let judge_of_letin env name defj typj j =
  { uj_val = mkLetIn (name, defj.uj_val, typj.utj_val, j.uj_val) ;
    uj_type = type_of_letin env defj.uj_val j.uj_type }

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
          Type (sup u1 type0_univ)
    (* Product rule (Prop,Type_i,Type_i) *)
    | (Prop Pos,  Type u2)  -> Type (sup type0_univ u2)
    (* Product rule (Prop,Type_i,Type_i) *)
    | (Prop Null, Type _)  -> rangsort
    (* Product rule (Type_i,Type_i,Type_i) *)
    | (Type u1, Type u2) -> Type (sup u1 u2)

(* [judge_of_product env name (typ1,s1) (typ2,s2)] implements the rule

    env |- typ1:s1       env, name:typ1 |- typ2 : s2
    -------------------------------------------------------------------------
         s' >= (s1,s2), env |- (name:typ)j.uj_val : s'

  where j.uj_type is convertible to a sort s2
*)

let type_of_product env s1 s2 =
  mkSort (sort_of_product env s1 s2)

let judge_of_product env name t1 t2 =
  make_judge (mkProd (name, t1.utj_val, t2.utj_val))
    (type_of_product env t1.utj_type t2.utj_type)

(* Type of a type cast *)

(* [judge_of_cast env (c,typ1) (typ2,s)] implements the rule

    env |- c:typ1    env |- typ2:s    env |- typ1 <= typ2
    ---------------------------------------------------------------------
         env |- c:typ2
*)

let type_of_cast env c t k expected_type =
  try
    let cst =
      match k with
      | VMcast -> vm_conv CUMUL env t expected_type
      | DEFAULTcast -> conv_leq env t expected_type in
    expected_type, cst
  with NotConvertible ->
    error_actual_type env (make_judge c t) expected_type

let judge_of_cast env cj k tj =
  let expected_type = tj.utj_val in
  let t, cst = type_of_cast env cj.uj_val cj.uj_type k expected_type in
  make_judge (mkCast (cj.uj_val, k, t)) t, cst


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

let type_of_inductive_knowing_parameters env c ind paramtyps =
  let (mib,mip) = lookup_mind_specif env ind in
  check_args env c mib.mind_hyps;
  Inductive.type_of_inductive_knowing_parameters env mip paramtyps

let type_of_inductive env c ind = 
  type_of_inductive_knowing_parameters env c ind [||]

let judge_of_inductive_knowing_parameters env ind jl =
  let c = mkInd ind in
  let paramtyps = Array.map (fun j -> j.uj_type) jl in
  let t = type_of_inductive_knowing_parameters env c ind paramtyps in
  make_judge c t

let judge_of_inductive env ind =
  judge_of_inductive_knowing_parameters env ind [||]

(* Constructors. *)

let type_of_constructor env constr c =
  let _ =
    let ((kn,_),_) = c in
    let mib = lookup_mind kn env in
    check_args env constr mib.mind_hyps in
  let specif = lookup_mind_specif env (inductive_of_constructor c) in
  type_of_constructor c specif

let judge_of_constructor env c =
  let constr = mkConstruct c in
  make_judge constr (type_of_constructor env constr c)

(* Case. *)

let check_branch_types env cj (lfj,explft) =
  try conv_leq_vecti env (Array.map j_type lfj) explft
  with
      NotConvertibleVect i ->
        error_ill_formed_branch env cj.uj_val i lfj.(i).uj_type explft.(i)
    | Invalid_argument _ ->
        error_number_branches env cj (Array.length explft)

let judge_of_case env ci pj cj lfj =
  let indspec =
    try find_rectype env cj.uj_type
    with Not_found -> error_case_not_inductive env cj in
  let _ = check_case_info env (fst indspec) ci in
  let (bty,rslty,univ) =
    type_case_branches env indspec pj cj.uj_val in
  let univ' = check_branch_types env cj (lfj,bty) in
  ({ uj_val  = mkCase (ci, (*nf_betaiota*) pj.uj_val, cj.uj_val,
                       Array.map j_val lfj);
     uj_type = rslty },
  Constraint.union univ univ')

(* Fixpoints. *)

(* Checks the type of a general (co)fixpoint, i.e. without checking *)
(* the specific guard condition. *)

let type_of_fixpoint env lna lar l tl =
  let lt = Array.length tl in
  assert (Array.length lar = lt);
  try
    conv_leq_vecti env tl (Array.map (fun ty -> lift lt ty) lar)
  with NotConvertibleVect i ->
    error_ill_typed_rec_body env i lna (array_map2 make_judge l tl) lar

let type_fixpoint env lna lar vdefj =
  let lt = Array.length vdefj in
  assert (Array.length lar = lt);
  try
    conv_leq_vecti env (Array.map j_type vdefj) (Array.map (fun ty -> lift lt ty) lar)
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

type renv = 
    { 
              hconstruct  : (constructor, types) Hashtbl.t;
      mutable rc          : constraints;
      mutable int_checked : bool;
      mutable int_constr  : constr;
      mutable arr_checked : bool;
      mutable arr_constr  : constr
    }

let empty_renv () = { 
  hconstruct = Hashtbl.create 17;
  rc = Constraint.empty;
  int_checked = false;
  int_constr = mkRel 0;
  arr_checked = false;
  arr_constr = mkRel 0;
}

let type_of_apply renv env f tf args targs =
  let typ = ref tf in
  let check_app n ta =
    match kind_of_term (whd_betadeltaiota env !typ) with
    | Prod(_,c1,c2) ->
	begin try 
	  let c = conv_leq env ta c1 in 
	  renv.rc <- Constraint.union renv.rc c; 
	  typ := subst1 args.(n) c2
	with NotConvertible -> 
	  let funj = make_judge f tf in
	  let argjv =  array_map2 make_judge args targs in
	  error_cant_apply_bad_type env (n+1,c1,ta) funj argjv
	end
    | _ ->
	let funj = make_judge f tf in
	let argjv =  array_map2 make_judge args targs in
	error_cant_apply_not_functional env funj argjv in
  Array.iteri check_app targs;
  !typ

let get_constructor_type renv env constr c =
  try Hashtbl.find renv.hconstruct c 
  with Not_found ->
    let t = type_of_constructor env constr c in
    Hashtbl.add renv.hconstruct c t;
    t

let type_of_int env =
  match (retroknowledge env).Pre_env.retro_int31 with
  | Some (_,c) -> c
  | None -> raise 
	(Invalid_argument "Typeops.type_of_int: int31 not_defined")

let internal_type_of_int renv env = 
  if renv.int_checked then renv.int_constr
  else 
    let c = type_of_int env in
    renv.int_checked <- true;
    renv.int_constr <- c;
    c

let judge_of_int env i =
  make_judge (mkInt i) (type_of_int env)

let type_of_array env = 
  match (retroknowledge env).Pre_env.retro_array with
  | Some (_,c) -> c
  | None -> raise 
	(Invalid_argument "Typeops.type_of_array: array not_defined")

let internal_type_of_array renv env =
  if renv.arr_checked then renv.arr_constr
  else 
    let c = type_of_array env in
    renv.arr_checked <- true;
    renv.arr_constr <- c;
    c

let judge_of_array env tj pj =
  let t = tj.utj_val in
  Array.iter (fun j -> 
    let _ = type_of_cast env j.uj_val j.uj_type DEFAULTcast t in ()) pj;
  make_judge (mkArray(t, Array.map j_val pj))
    (mkApp (type_of_array env, [|t|]))
  
let rec execute renv env cstr =
  match kind_of_term cstr with
    (* Atomic terms *)
    | Sort (Prop c) -> 
	type_of_prop_constents c

    | Sort (Type u) -> 
	type_of_type u

    | Rel n -> 
	type_of_relative env n

    | Var id -> 
	type_of_variable env id

    | Const c -> 
	internal_type_of_constant env cstr c

    (* Lambda calculus operators *)
    | App (f,args) ->
        let targs = execute_array renv env args in
	let tf =
	  match kind_of_term f with
	  | Ind ind ->
	      (* Sort-polymorphism of inductive types *)
	      type_of_inductive_knowing_parameters env f ind targs
	  | Const cst ->
	      (* Sort-polymorphism of constant *)
	      internal_type_of_constant_knowing_parameters env f cst targs
	  | _ ->
	      (* No sort-polymorphism *)
	      execute renv env f
	in
	type_of_apply renv env f tf args targs
	  
    | Lambda (name,c1,c2) ->
	let _ = execute_type renv env c1 in
	let env1 = push_rel (name, None, c1) env in
	let t2 = execute renv env1 c2 in
	type_of_abstraction env name c1 t2
	  
    | Prod (name,c1,c2) ->
	let t1 = execute_type renv env c1 in
	let env1 = push_rel (name,None, c1) env in
	let t2 = execute_type renv env1 c2 in
	type_of_product env t1 t2
	  
    | LetIn (name,c1,c2,c3) ->
	let t1 = execute renv env c1 in
	let _ = execute_type renv env c2 in
	let _, cte = type_of_cast env c1 t1 DEFAULTcast c2 in
	renv.rc <- Constraint.union renv.rc cte;
        let env1 = push_rel (name,Some c1, c2) env in
	let t3 = execute renv env1 c3 in
	type_of_letin env c1 t3

    | Cast (c,k,t) ->
        let tc = execute renv env c in
        let _ = execute_type renv env t in
	let tc, cte = type_of_cast env c tc k t in
	renv.rc <- Constraint.union renv.rc cte;
	tc

    (* Inductive types *)
    | Ind ind -> 
	type_of_inductive env cstr ind

    | Construct c -> 
	get_constructor_type renv env cstr c

    | Case (ci,p,c,lf) ->   
	let tc = execute renv env c in
        let tp = execute renv env p in
        let tlf = execute_array renv env lf in
	let (j,cst) = 
	  judge_of_case env ci 
	    (make_judge p tp) (make_judge c tc) 
	    (array_map2 make_judge lf tlf) in
	renv.rc <- Constraint.union renv.rc cst;
	j.uj_type
  
   | Fix ((vn,i as vni),recdef) ->
        let fix_ty = execute_recdef renv env recdef i in
        let fix = (vni,recdef) in
        check_fix env fix;
	fix_ty
	  
    | CoFix (i,recdef) ->
        let fix_ty = execute_recdef renv env recdef i in
        let cofix = (i,recdef) in
        check_cofix env cofix;
	fix_ty
   
    (* Native representation *)
    | NativeInt _ -> internal_type_of_int renv env

    | NativeArr (t,p) -> 
	let _ = execute_type renv env t in
	let ta = internal_type_of_array renv env in
	Array.iter (fun e ->
	  let te = execute renv env e in
	  let _,cte = type_of_cast env e te DEFAULTcast t in
	  renv.rc <- Constraint.union renv.rc cte) p;
	mkApp(ta, [|t|]) 

    (* Partial proofs: unsupported by the kernel *)
    | Meta _ ->
	anomaly "the kernel does not support metavariables"

    | Evar _ ->
	anomaly "the kernel does not support existential variables"

and execute_type renv env constr = 
  let t = execute renv env constr in
  match kind_of_term(whd_betadeltaiota env t) with
  |  Sort s -> s 
  | _ -> error_not_type env (make_judge constr t)
	  
and execute_recdef renv env (names,lar,vdef) i =
  let _ = execute_array renv env lar in
  let env1 = push_rec_types (names,lar,vdef) env in
  let tvdef = execute_array renv env1 vdef in
  let cst = type_of_fixpoint env1 names lar vdef tvdef in
  renv.rc <- Constraint.union renv.rc cst;
  lar.(i)

and execute_array renv env = Array.map (execute renv env)


(* Derived functions *)
let infer env constr =
  let renv = empty_renv () in
  let t = execute renv env constr in
  let _ = merge_constraints renv.rc (universes env) in
  make_judge constr t,  renv.rc 

let infer_type env constr =
  let renv = empty_renv () in
  let s = execute_type renv env constr in
  let _ = merge_constraints renv.rc (universes env) in
  {utj_val = constr; utj_type = s }, renv.rc

let infer_v env cv =
  let renv = empty_renv () in
  let tv = execute_array renv env cv in
  let _ = merge_constraints renv.rc (universes env) in 
  array_map2 make_judge cv tv, renv.rc

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


(* Building type of primitive operators and type *)

open Native
let check_primitive_error () =
    raise 
      (Invalid_argument "Typeops.check_primitive_type:Not the expected type")
  
let check_caml_prim_type env op t =
  Printf.eprintf "check_caml_prim_type: not yet implemented\n"

let check_iterator_type env op t =
  Printf.eprintf "check_iterator_type: not yet implemented\n"

let typeof_prim env op = 
  let i = 
    try type_of_int env 
    with _ -> 
      raise (Invalid_argument 
	       "typeof_prim: the type int31 should be register first") 
  in
  let type_of_bool env =
    match (retroknowledge env).Pre_env.retro_bool with
    | Some ((ind,_),_) -> mkInd ind
    | _ -> raise (Invalid_argument 
	       "typeof_prim: the type bool should be register first") in
  let type_of_carry env =
    match (retroknowledge env).Pre_env.retro_carry with
    | Some ((ind,_),_) -> mkInd ind
    | _ -> raise (Invalid_argument 
	       "typeof_prim: the type carry should be register first") in
  let type_of_pair env =
    match (retroknowledge env).Pre_env.retro_pair with
    | Some (ind,_) -> mkInd ind
    | _ -> raise (Invalid_argument 
	       "typeof_prim: the type pair should be register first") in
  let type_of_cmp env =
    match (retroknowledge env).Pre_env.retro_cmp with
    | Some ((ind,_),_,_) -> mkInd ind
    | _ -> raise (Invalid_argument 
	       "typeof_prim: the type comparison should be register first") in
  match op with
  | Int31head0 | Int31tail0 ->
      mkArrow i i
  | Int31add | Int31sub | Int31mul | Int31div | Int31mod 
  | Int31lsr | Int31lsl | Int31land | Int31lor | Int31lxor -> 
      mkArrow i (mkArrow i i)
  | Int31addc | Int31subc | Int31addCarryC | Int31subCarryC ->
      let c = type_of_carry env in
      mkArrow i (mkArrow i (mkApp (c,[|i|])))
  | Int31mulc | Int31diveucl ->
      let p = type_of_pair env in
      mkArrow i (mkArrow i (mkApp (p,[|i;i|])))
  | Int31div21 ->
      let p = type_of_pair env in
      mkArrow i (mkArrow i (mkArrow i (mkApp (p,[|i;i|]))))
  | Int31addMulDiv ->
      mkArrow i (mkArrow i (mkArrow i i))
  | Int31eq | Int31lt | Int31le ->
      let b = type_of_bool env in
      mkArrow i (mkArrow i b)
  | Int31compare ->
      let cmp = type_of_cmp env in
      mkArrow i (mkArrow i cmp)
  | Int31eqb_correct -> 
     raise  (Invalid_argument "typeof_prim:Int31eqb_correct:not implemented") 

let check_prim_type env op t =
  if op = Int31eqb_correct then
    Format.eprintf "Warning check_prim_type: Int31eqb_correct not implemented@."
  else
    if not (eq_constr (typeof_prim env op) t) then
      raise (Invalid_argument "check_prim_type: not the expected type")

let check_primitive_type env op_t t =
  match op_t with
  | OT_type PT_int31 -> 
      if not (eq_constr t mkSet) then check_primitive_error ()
  | OT_type PT_array -> 
      if isProd t then
	let (_,dom,codom) = destProd t in
	(if not (is_Type dom && is_Type codom) then check_primitive_error ())
      else check_primitive_error ()
  | OT_op op -> 
      match op with
      | Ocaml_prim op -> check_caml_prim_type env op t
      | Oiterator op -> check_iterator_type env op t
      | Oprim op -> check_prim_type env op t


