(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
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
open Term
open Constr
open Context
open Vars
open Declarations
open Environ
open Reduction
open Inductive
open Type_errors

module RelDecl = Context.Rel.Declaration
module NamedDecl = Context.Named.Declaration

exception NotConvertibleVect of int

let conv_leq env x y = default_conv CUMUL env x y

let conv_leq_vecti env v1 v2 =
  Array.fold_left2_i
    (fun i _ t1 t2 ->
      try conv_leq env t1 t2
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
let infer_assumption env t ty =
  try
    let s = check_type env t ty in
    (match s with Sorts.SProp -> Irrelevant | _ -> Relevant)
  with TypeError _ ->
    error_assumption env (make_judge t ty)

let warn_bad_relevance_name = "bad-relevance"
let warn_bad_relevance =
  CWarnings.create ~name:warn_bad_relevance_name ~category:"debug" ~default:CWarnings.Disabled
    Pp.(function
        | None ->  str "Bad relevance in case annotation."
        | Some x -> str "Bad relevance for binder " ++ Name.print x.binder_name ++ str ".")

let warn_bad_relevance_ci ?loc () = warn_bad_relevance ?loc None
let warn_bad_relevance ?loc x = warn_bad_relevance ?loc (Some x)

let check_assumption env x t ty =
  let r = x.binder_relevance in
  let r' = infer_assumption env t ty in
  let x = if Sorts.relevance_equal r r'
    then x
    else (warn_bad_relevance x; {x with binder_relevance = r'})
  in
  x

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
  | SProp | Prop | Set -> type1
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
let check_hyps_inclusion env ?evars c sign =
  let conv env a b = conv env ?evars a b in
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
        error_reference_variables env id c)
    sign
    ~init:()

(* Instantiation of terms on real arguments. *)

(* Make a type polymorphic if an arity *)

(* Type of constants *)


let type_of_constant env (kn,_u as cst) =
  let cb = lookup_constant kn env in
  let () = check_hyps_inclusion env (GlobRef.ConstRef kn) cb.const_hyps in
  let ty, cu = constant_type env cst in
  let () = check_constraints cu env in
    ty

let type_of_constant_in env (kn,_u as cst) =
  let cb = lookup_constant kn env in
  let () = check_hyps_inclusion env (GlobRef.ConstRef kn) cb.const_hyps in
  constant_type_in env cst

(* Type of a lambda-abstraction. *)

(* [judge_of_abstraction env name var j] implements the rule

 env, name:typ |- j.uj_val:j.uj_type     env, |- (name:typ)j.uj_type : s
 -----------------------------------------------------------------------
          env |- [name:typ]j.uj_val : (name:typ)j.uj_type

  Since all products are defined in the Calculus of Inductive Constructions
  and no upper constraint exists on the sort $s$, we don't need to compute $s$
*)

let type_of_abstraction _env name var ty =
  mkProd (name, var, ty)

(* Type of an application. *)

let make_judgev c t =
  Array.map2 make_judge c t

let rec check_empty_stack = function
| [] -> true
| CClosure.Zupdate _ :: s -> check_empty_stack s
| _ -> false

let type_of_apply env func funt argsv argstv =
  let open CClosure in
  let len = Array.length argsv in
  let infos = create_clos_infos all env in
  let tab = create_tab () in
  let rec apply_rec i typ =
    if Int.equal i len then term_of_fconstr typ
    else
      let typ, stk = whd_stack infos tab typ [] in
      (** The return stack is known to be empty *)
      let () = assert (check_empty_stack stk) in
      match fterm_of typ with
      | FProd (_, c1, c2, e) ->
        let arg = argsv.(i) in
        let argt = argstv.(i) in
        let c1 = term_of_fconstr c1 in
        begin match conv_leq env argt c1 with
        | () -> apply_rec (i+1) (mk_clos (Esubst.subs_cons (inject arg) e) c2)
        | exception NotConvertible ->
          error_cant_apply_bad_type env
            (i+1,c1,argt)
            (make_judge func funt)
            (make_judgev argsv argstv)
        end
      | _ ->
        error_cant_apply_not_functional env
          (make_judge func funt)
          (make_judgev argsv argstv)
  in
  apply_rec 0 (inject funt)

(* Type of primitive constructs *)
let type_of_prim_type _env u (type a) (prim : a CPrimitives.prim_type) = match prim with
  | CPrimitives.PT_int63 ->
    assert (Univ.Instance.is_empty u);
    Constr.mkSet
  | CPrimitives.PT_float64 ->
    assert (Univ.Instance.is_empty u);
    Constr.mkSet
  | CPrimitives.PT_array ->
    begin match Univ.Instance.to_array u with
    | [|u|] ->
      let ty = Constr.mkType (Univ.Universe.make u) in
      Constr.mkProd(Context.anonR, ty , ty)
    | _ -> anomaly Pp.(str"universe instance for array type should have length 1")
    end

let type_of_int env =
  match env.retroknowledge.Retroknowledge.retro_int63 with
  | Some c -> mkConst c
  | None -> CErrors.user_err Pp.(str"The type int must be registered before this construction can be typechecked.")

let type_of_float env =
  match env.retroknowledge.Retroknowledge.retro_float64 with
  | Some c -> mkConst c
  | None -> CErrors.user_err Pp.(str"The type float must be registered before this construction can be typechecked.")

let type_of_array env u =
  assert (Univ.Instance.length u = 1);
  match env.retroknowledge.Retroknowledge.retro_array with
  | Some c -> mkConstU (c,u)
  | None -> CErrors.user_err Pp.(str"The type array must be registered before this construction can be typechecked.")

(* Type of product *)

let sort_of_product env domsort rangsort =
  match (domsort, rangsort) with
    | (_, SProp) | (SProp, _) -> rangsort
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
          Sorts.sort_of_univ (Universe.sup Universe.type0 u1)
    (* Product rule (Prop,Type_i,Type_i) *)
    | (Set,  Type u2)  -> Sorts.sort_of_univ (Universe.sup Universe.type0 u2)
    (* Product rule (Prop,Type_i,Type_i) *)
    | (Prop, Type _)  -> rangsort
    (* Product rule (Type_i,Type_i,Type_i) *)
    | (Type u1, Type u2) -> Sorts.sort_of_univ (Universe.sup u1 u2)

(* [judge_of_product env name (typ1,s1) (typ2,s2)] implements the rule

    env |- typ1:s1       env, name:typ1 |- typ2 : s2
    -------------------------------------------------------------------------
         s' >= (s1,s2), env |- (name:typ)j.uj_val : s'

  where j.uj_type is convertible to a sort s2
*)
let type_of_product env _name s1 s2 =
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
      default_conv CUMUL env ct expected_type
    | NATIVEcast ->
      let sigma = Nativelambda.empty_evars in
      Nativeconv.native_conv CUMUL sigma env ct expected_type
  with NotConvertible ->
    error_actual_type env (make_judge c ct) expected_type

let judge_of_int env i =
  make_judge (Constr.mkInt i) (type_of_int env)

let judge_of_float env f =
  make_judge (Constr.mkFloat f) (type_of_float env)

let judge_of_array env u tj defj =
  let def = defj.uj_val in
  let ty = defj.uj_type in
  Array.iter (fun j -> check_cast env j.uj_val j.uj_type DEFAULTcast ty) tj;
  make_judge (mkArray(u, Array.map j_val tj, def, ty)) (mkApp (type_of_array env u, [|ty|]))

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

let type_of_inductive_knowing_parameters env (ind,u) args =
  let (mib,_mip) as spec = lookup_mind_specif env ind in
  check_hyps_inclusion env (GlobRef.IndRef ind) mib.mind_hyps;
  let t,cst = Inductive.constrained_type_of_inductive_knowing_parameters
      (spec,u) (Inductive.make_param_univs env args)
  in
  check_constraints cst env;
  t

let type_of_inductive env (ind,u) =
  let (mib,mip) = lookup_mind_specif env ind in
  check_hyps_inclusion env (GlobRef.IndRef ind) mib.mind_hyps;
  let t,cst = Inductive.constrained_type_of_inductive ((mib,mip),u) in
  check_constraints cst env;
  t

(* Constructors. *)

let type_of_constructor env (c,_u as cu) =
  let () =
    let ((kn,_),_) = c in
    let mib = lookup_mind kn env in
    check_hyps_inclusion env (GlobRef.ConstructRef c) mib.mind_hyps
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

let should_invert_case env ci =
  ci.ci_relevance == Sorts.Relevant &&
  let mib,mip = lookup_mind_specif env ci.ci_ind in
  mip.mind_relevance == Sorts.Irrelevant &&
  (* NB: it's possible to have 2 ctors or arguments to 1 ctor by unsetting univ checks
     but we don't do special reduction in such cases

     XXX Someday consider more carefully what happens with letin params and arguments
     (currently they're squashed, see indtyping)
 *)
  Array.length mip.mind_nf_lc = 1 &&
  List.length (fst mip.mind_nf_lc.(0)) = List.length mib.mind_params_ctxt

let type_of_case env ci p pt iv c ct _lf lft =
  let (pind, _ as indspec) =
    try find_rectype env ct
    with Not_found -> error_case_not_inductive env (make_judge c ct) in
  let _, sp = try dest_arity env pt
    with NotArity -> error_elim_arity env pind c (make_judge p pt) None in
  let rp = Sorts.relevance_of_sort sp in
  let ci = if ci.ci_relevance == rp then ci
    else (warn_bad_relevance_ci (); {ci with ci_relevance=rp})
  in
  let () = check_case_info env pind rp ci in
  let () =
    let is_inversion = match iv with
      | NoInvert -> false
      | CaseInvert _ -> true (* contents already checked *)
    in
    if not (is_inversion = should_invert_case env ci)
    then error_bad_invert env
  in
  let (bty,rslty) =
    type_case_branches env indspec (make_judge p pt) c in
  let () = check_branch_types env pind c ct lft bty in
  ci, rslty

let type_of_projection env p c ct =
  let pty = lookup_projection p env in
  let (ind,u), args =
    try find_rectype env ct
    with Not_found -> error_case_not_inductive env (make_judge c ct)
  in
  assert(Ind.CanOrd.equal (Projection.inductive p) ind);
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

(* Global references *)

let type_of_global_in_context env r =
  let open Names.GlobRef in
  match r with
  | VarRef id -> Environ.named_type id env, Univ.AbstractContext.empty
  | ConstRef c ->
    let cb = Environ.lookup_constant c env in
    let univs = Declareops.constant_polymorphic_context cb in
    cb.Declarations.const_type, univs
  | IndRef ind ->
    let (mib,_ as specif) = Inductive.lookup_mind_specif env ind in
    let univs = Declareops.inductive_polymorphic_context mib in
    let inst = Univ.make_abstract_instance univs in
    Inductive.type_of_inductive (specif, inst), univs
  | ConstructRef cstr ->
    let (mib,_ as specif) =
      Inductive.lookup_mind_specif env (inductive_of_constructor cstr)
    in
    let univs = Declareops.inductive_polymorphic_context mib in
    let inst = Univ.make_abstract_instance univs in
    Inductive.type_of_constructor (cstr,inst) specif, univs

(************************************************************************)
(************************************************************************)

let check_binder_annot s x =
  let r = x.binder_relevance in
  let r' = Sorts.relevance_of_sort s in
  if r' == r
  then x
  else (warn_bad_relevance x; {x with binder_relevance = r'})

(* The typing machine. *)
    (* ATTENTION : faudra faire le typage du contexte des Const,
    Ind et Constructsi un jour cela devient des constructions
    arbitraires et non plus des variables *)
let rec execute env cstr =
  let open Context.Rel.Declaration in
  match kind cstr with
    (* Atomic terms *)
    | Sort s ->
      (match s with
       | SProp -> if not (Environ.sprop_allowed env) then error_disallowed_sprop env
       | _ -> ());
      cstr, type_of_sort s

    | Rel n ->
      cstr, type_of_relative env n

    | Var id ->
      cstr, type_of_variable env id

    | Const c ->
      cstr, type_of_constant env c

    | Proj (p, c) ->
      let c', ct = execute env c in
      let cstr = if c == c' then cstr else mkProj (p,c') in
      cstr, type_of_projection env p c' ct

    (* Lambda calculus operators *)
    | App (f,args) ->
      let args', argst = execute_array env args in
        let f', ft =
          match kind f with
          | Ind ind when Environ.template_polymorphic_pind ind env ->
            f, type_of_inductive_knowing_parameters env ind argst
          | _ ->
            (* No template polymorphism *)
            execute env f
        in
        let cstr = if f == f' && args == args' then cstr else mkApp (f',args') in
        cstr, type_of_apply env f' ft args' argst

    | Lambda (name,c1,c2) ->
      let c1', s = execute_is_type env c1 in
      let name' = check_binder_annot s name in
      let env1 = push_rel (LocalAssum (name',c1')) env in
      let c2', c2t = execute env1 c2 in
      let cstr = if name == name' && c1 == c1' && c2 == c2' then cstr else mkLambda(name',c1',c2') in
      cstr, type_of_abstraction env name' c1 c2t

    | Prod (name,c1,c2) ->
      let c1', vars = execute_is_type env c1 in
      let name' = check_binder_annot vars name in
      let env1 = push_rel (LocalAssum (name',c1')) env in
      let c2', vars' = execute_is_type env1 c2 in
      let cstr = if name == name' && c1 == c1' && c2 == c2' then cstr else mkProd(name',c1',c2') in
      cstr, type_of_product env name' vars vars'

    | LetIn (name,c1,c2,c3) ->
      let c1', c1t = execute env c1 in
      let c2', c2s = execute_is_type env c2 in
      let name' = check_binder_annot c2s name in
      let () = check_cast env c1' c1t DEFAULTcast c2' in
      let env1 = push_rel (LocalDef (name',c1',c2')) env in
      let c3', c3t = execute env1 c3 in
      let cstr = if name == name' && c1 == c1' && c2 == c2' && c3 == c3' then cstr
        else mkLetIn(name',c1',c2',c3')
      in
      cstr, subst1 c1 c3t

    | Cast (c,k,t) ->
      let c', ct = execute env c in
      let t', _ts = execute_is_type env t in
      let () = check_cast env c' ct k t' in
      let cstr = if c == c' && t == t' then cstr else mkCast(c',k,t') in
      cstr, t'

    (* Inductive types *)
    | Ind ind ->
      cstr, type_of_inductive env ind

    | Construct c ->
      cstr, type_of_constructor env c

    | Case (ci, u, pms, p, iv, c, lf) ->
        (** FIXME: change type_of_case to handle the compact form *)
        let (ci, p, iv, c, lf) = expand_case env (ci, u, pms, p, iv, c, lf) in
        let c', ct = execute env c in
        let iv' = match iv with
          | NoInvert -> NoInvert
          | CaseInvert {indices} ->
            let args = Array.append pms indices in
            let ct' = mkApp (mkIndU (ci.ci_ind,u), args) in
            let (ct', _) : constr * Sorts.t = execute_is_type env ct' in
            let () = conv_leq env ct ct' in
            let _, args' = decompose_appvect ct' in
            if args == args' then iv
            else CaseInvert {indices=Array.sub args' (Array.length pms) (Array.length indices)}
        in
        let p', pt = execute env p in
        let lf', lft = execute_array env lf in
        let ci', t = type_of_case env ci p' pt iv' c' ct lf' lft in
        let cstr = if ci == ci' && c == c' && p == p' && iv == iv' && lf == lf' then cstr
          else mkCase (Inductive.contract_case env (ci',p',iv',c',lf'))
        in
        cstr, t

    | Fix ((_vn,i as vni),recdef as fix) ->
      let (fix_ty,recdef') = execute_recdef env recdef i in
      let cstr, fix = if recdef == recdef' then cstr, fix else
          let fix = (vni,recdef') in mkFix fix, fix
      in
      check_fix env fix; cstr, fix_ty

    | CoFix (i,recdef as cofix) ->
      let (fix_ty,recdef') = execute_recdef env recdef i in
      let cstr, cofix = if recdef == recdef' then cstr, cofix else
          let cofix = (i,recdef') in mkCoFix cofix, cofix
      in
      check_cofix env cofix; cstr, fix_ty

    (* Primitive types *)
    | Int _ -> cstr, type_of_int env
    | Float _ -> cstr, type_of_float env
    | Array(u,t,def,ty) ->
      (* ty : Type@{u} and all of t,def : ty *)
      let ulev = match Univ.Instance.to_array u with
        | [|u|] -> u
        | _ -> assert false
      in
      let ty',tyty = execute env ty in
      check_cast env ty' tyty DEFAULTcast (mkType (Universe.make ulev));
      let def', def_ty = execute env def in
      check_cast env def' def_ty DEFAULTcast ty';
      let ta = type_of_array env u in
      let t' = Array.Smart.map (fun x ->
        let x', xt = execute env x in
        check_cast env x' xt DEFAULTcast ty';
        x') t in
      let cstr = if def'==def && t'==t && ty'==ty then cstr else mkArray(u, t',def',ty') in
      cstr, mkApp(ta, [|ty'|])

    (* Partial proofs: unsupported by the kernel *)
    | Meta _ ->
        anomaly (Pp.str "the kernel does not support metavariables.")

    | Evar _ ->
        anomaly (Pp.str "the kernel does not support existential variables.")

and execute_is_type env constr =
  let c, t = execute env constr in
    c, check_type env constr t

and execute_recdef env (names,lar,vdef as recdef) i =
  let lar', lart = execute_array env lar in
  let names' = Array.Smart.map_i (fun i na -> check_assumption env na lar'.(i) lart.(i)) names in
  let env1 = push_rec_types (names',lar',vdef) env in (* vdef is ignored *)
  let vdef', vdeft = execute_array env1 vdef in
  let () = check_fixpoint env1 names' lar' vdef' vdeft in
  let recdef = if names == names' && lar == lar' && vdef == vdef' then recdef else (names',lar',vdef') in
    (lar'.(i),recdef)

and execute_array env cs =
  let tys = Array.make (Array.length cs) mkProp in
  let cs = Array.Smart.map_i (fun i c -> let c, ty = execute env c in tys.(i) <- ty; c) cs in
  cs, tys

(* Derived functions *)

let check_wellformed_universes env c =
  let univs = universes_of_constr c in
  try UGraph.check_declared_universes (universes env) univs
  with UGraph.UndeclaredLevel u ->
    error_undeclared_universe env u

let infer env constr =
  let () = check_wellformed_universes env constr in
  let constr, t = execute env constr in
  make_judge constr t

let assumption_of_judgment env {uj_val=c; uj_type=t} =
  infer_assumption env c t

let type_judgment env {uj_val=c; uj_type=t} =
  let s = check_type env c t in
  {utj_val = c; utj_type = s }

let infer_type env constr =
  let () = check_wellformed_universes env constr in
  let constr, t = execute env constr in
  let s = check_type env constr t in
  {utj_val = constr; utj_type = s}

(* Typing of several terms. *)

let check_context env rels =
  let open Context.Rel.Declaration in
  Context.Rel.fold_outside (fun d (env,rels) ->
    match d with
      | LocalAssum (x,ty) ->
        let jty = infer_type env ty in
        let x = check_binder_annot jty.utj_type x in
        push_rel d env, LocalAssum (x,jty.utj_val) :: rels
      | LocalDef (x,bd,ty) ->
        let j1 = infer env bd in
        let jty = infer_type env ty in
        conv_leq env j1.uj_type ty;
        let x = check_binder_annot jty.utj_type x in
        push_rel d env, LocalDef (x,j1.uj_val,jty.utj_val) :: rels)
    rels ~init:(env,[])

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

(* let judge_of_abstraction env x varj bodyj = *)
(*   make_judge (mkLambda (x, varj.utj_val, bodyj.uj_val)) *)
(*              (type_of_abstraction env x varj.utj_val bodyj.uj_type) *)

(* let judge_of_product env x varj outj = *)
(*   make_judge (mkProd (x, varj.utj_val, outj.utj_val)) *)
(*              (mkSort (sort_of_product env varj.utj_type outj.utj_type)) *)

(* let judge_of_letin env name defj typj j = *)
(*   make_judge (mkLetIn (name, defj.uj_val, typj.utj_val, j.uj_val)) *)
(*              (subst1 defj.uj_val j.uj_type) *)

let judge_of_cast env cj k tj =
  let () = check_cast env cj.uj_val cj.uj_type k tj.utj_val in
  let c = mkCast (cj.uj_val, k, tj.utj_val) in
  make_judge c tj.utj_val

let judge_of_inductive env indu =
  make_judge (mkIndU indu) (type_of_inductive env indu)

let judge_of_constructor env cu =
  make_judge (mkConstructU cu) (type_of_constructor env cu)

(* Building type of primitive operators and type *)

let type_of_prim_const env _u c =
  let int_ty () = type_of_int env in
  match c with
  | CPrimitives.Arraymaxlength ->
    int_ty ()

let type_of_prim env u t =
  let int_ty () = type_of_int env in
  let float_ty () = type_of_float env in
  let array_ty u a = mkApp(type_of_array env u, [|a|]) in
  let bool_ty () =
    match env.retroknowledge.Retroknowledge.retro_bool with
    | Some ((ind,_),_) -> Constr.mkInd ind
    | None -> CErrors.user_err Pp.(str"The type bool must be registered before this primitive.")
  in
  let compare_ty () =
    match env.retroknowledge.Retroknowledge.retro_cmp with
    | Some ((ind,_),_,_) -> Constr.mkInd ind
    | None -> CErrors.user_err Pp.(str"The type compare must be registered before this primitive.")
  in
  let f_compare_ty () =
    match env.retroknowledge.Retroknowledge.retro_f_cmp with
    | Some ((ind,_),_,_,_) -> Constr.mkInd ind
    | None -> CErrors.user_err Pp.(str"The type float_comparison must be registered before this primitive.")
  in
  let f_class_ty () =
    match env.retroknowledge.Retroknowledge.retro_f_class with
    | Some ((ind,_),_,_,_,_,_,_,_,_) -> Constr.mkInd ind
    | None -> CErrors.user_err Pp.(str"The type float_class must be registered before this primitive.")
  in
  let pair_ty fst_ty snd_ty =
    match env.retroknowledge.Retroknowledge.retro_pair with
    | Some (ind,_) -> Constr.mkApp(Constr.mkInd ind, [|fst_ty;snd_ty|])
    | None -> CErrors.user_err Pp.(str"The type pair must be registered before this primitive.")
  in
  let carry_ty int_ty =
    match env.retroknowledge.Retroknowledge.retro_carry with
    | Some ((ind,_),_) -> Constr.mkApp(Constr.mkInd ind, [|int_ty|])
    | None -> CErrors.user_err Pp.(str"The type carry must be registered before this primitive.")
  in
  let open CPrimitives in
  let tr_prim_type (tr_type : ind_or_type -> constr) (type a) (ty : a prim_type) (t : a) = match ty with
    | PT_int63 -> int_ty t
    | PT_float64 -> float_ty t
    | PT_array -> array_ty (fst t) (tr_type (snd t))
  in
  let tr_ind (tr_type : ind_or_type -> constr) (type t) (i : t prim_ind) (a : t) = match i, a with
    | PIT_bool, () -> bool_ty ()
    | PIT_carry, t -> carry_ty (tr_type t)
    | PIT_pair, (t1, t2) -> pair_ty (tr_type t1) (tr_type t2)
    | PIT_cmp, () -> compare_ty ()
    | PIT_f_cmp, () -> f_compare_ty ()
    | PIT_f_class, () -> f_class_ty ()
  in
  let rec tr_type n = function
    | PITT_ind (i, a) -> tr_ind (tr_type n) i a
    | PITT_type (ty,t) -> tr_prim_type (tr_type n) ty t
    | PITT_param i -> Constr.mkRel (n+i)
  in
  let rec nary_op n ret_ty = function
    | [] -> tr_type n ret_ty
    | arg_ty :: r ->
        Constr.mkProd (Context.nameR (Id.of_string "x"),
                       tr_type n arg_ty, nary_op (n + 1) ret_ty r)
  in
  let params, args_ty, ret_ty = types t in
  assert (AbstractContext.size (univs t) = Instance.length u);
  Vars.subst_instance_constr u
    (Term.it_mkProd_or_LetIn (nary_op 0 ret_ty args_ty) params)

let type_of_prim_or_type env u = let open CPrimitives in
  function
  | OT_type t -> type_of_prim_type env u t
  | OT_op op -> type_of_prim env u op
  | OT_const c -> type_of_prim_const env u c
