(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
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
open Term
open Constr
open Context
open Vars
open Declarations
open Environ
open Conversion
open Inductive
open Type_errors

module RelDecl = Context.Rel.Declaration
module NamedDecl = Context.Named.Declaration

exception NotConvertible
exception NotConvertibleVect of int

let conv_leq env x y = default_conv CUMUL env x y

let conv_leq_vecti env v1 v2 =
  Array.fold_left2_i
    (fun i _ t1 t2 ->
      match conv_leq env t1 t2 with
      | Result.Ok () -> ()
      | Result.Error () -> raise (NotConvertibleVect i))
    ()
    v1
    v2

let check_constraints cst env =
  if Environ.check_constraints cst env then ()
  else error_unsatisfied_constraints env cst

let check_qconstraints qcst env =
  if Sorts.QConstraints.trivial qcst then ()
  else error_unsatisfied_qconstraints env qcst

(* This should be a type (a priori without intention to be an assumption) *)
let check_type env c t =
  match kind(Reduction.whd_all env t) with
  | Sort s -> s
  | _ -> error_not_type env (make_judge c t)

(* This should be a type intended to be assumed. The error message is
   not as useful as for [type_judgment]. *)
let infer_assumption env t ty =
  try
    let s = check_type env t ty in
    Sorts.relevance_of_sort s
  with TypeError _ ->
    error_assumption env (make_judge t ty)

let nf_relevance env = function
  | Sorts.RelevanceVar q as r ->
    if Environ.Internal.is_above_prop env q then Sorts.Relevant
    else r
  | (Sorts.Irrelevant | Sorts.Relevant) as r -> r

let check_relevance env r r' =
  Sorts.relevance_equal (nf_relevance env r) (nf_relevance env r')

let check_assumption env x t ty =
  let r = x.binder_relevance in
  let r' = infer_assumption env t ty in
  if check_relevance env r r' then ()
  else
    error_bad_binder_relevance env r' (RelDecl.LocalAssum (x, t))

let check_binding_relevance env na1 na2 =
  (* Since we know statically the relevance here, we are stricter *)
  assert (check_relevance env (binder_relevance na1) (binder_relevance na2))

let esubst u s c =
  Vars.esubst Vars.lift_substituend s (subst_instance_constr u c)

exception ArgumentsMismatch

let instantiate_context env u subst nas ctx =
  let open Context.Rel.Declaration in
  let instantiate_relevance na =
    { na with binder_relevance = UVars.subst_instance_relevance u na.binder_relevance }
  in
  let rec instantiate i ctx = match ctx with
  | [] -> if 0 <= i then raise ArgumentsMismatch else []
  | LocalAssum (na, ty) :: ctx ->
    let ctx = instantiate (pred i) ctx in
    let subst = Esubst.subs_liftn i subst in
    let na = instantiate_relevance na in
    let ty = esubst u subst ty in
    let () = check_binding_relevance env na nas.(i) in
    LocalAssum (nas.(i), ty) :: ctx
  | LocalDef (na, ty, bdy) :: ctx ->
    let ctx = instantiate (pred i) ctx in
    let subst = Esubst.subs_liftn i subst in
    let na = instantiate_relevance na in
    let ty = esubst u subst ty in
    let bdy = esubst u subst bdy in
    let () = check_binding_relevance env na nas.(i) in
    LocalDef (nas.(i), ty, bdy) :: ctx
  in
  instantiate (Array.length nas - 1) ctx

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
  | QSort (_, u) -> type_of_type u

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
        let () = match conv env (get_type d2) (get_type d1) with
        | Result.Ok () -> ()
        | Result.Error () -> raise NotConvertible
        in
        (match d2,d1 with
        | LocalAssum _, LocalAssum _ -> ()
        | LocalAssum _, LocalDef _ ->
            (* This is wrong, because we don't know if the body is
               needed or not for typechecking: *) ()
        | LocalDef _, LocalAssum _ -> raise NotConvertible
        | LocalDef (_,b2,_), LocalDef (_,b1,_) ->
          match conv env b2 b1 with
          | Result.Ok () -> ()
          | Result.Error () -> raise NotConvertible);
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
  let infos = create_clos_infos RedFlags.all env in
  let tab = create_tab () in
  let rec apply_rec i typ =
    if Int.equal i len then term_of_fconstr typ
    else
      let typ, stk = whd_stack infos tab typ [] in
      match fterm_of typ with
      | FProd (_, c1, c2, e) ->
        (** The return stack is known to be empty *)
        let () = assert (check_empty_stack stk) in
        let arg = argsv.(i) in
        let argt = argstv.(i) in
        let c1 = term_of_fconstr c1 in
        begin match conv_leq env argt c1 with
        | Result.Ok () -> apply_rec (i+1) (mk_clos (CClosure.usubs_cons (inject arg) e) c2)
        | Result.Error () ->
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

(* Checks that an array of terms has the type of a telescope. We assume that all
   inputs are well-typed separately. *)
let type_of_parameters env ctx u argsv argstv =
  let open Context.Rel.Declaration in
  let ctx = List.rev ctx in
  let rec apply_rec i subst ctx = match ctx with
  | [] -> if Int.equal i (Array.length argsv) then subst else raise ArgumentsMismatch
  | LocalAssum (_, t) :: ctx ->
    let arg = argsv.(i) in
    let argt = argstv.(i) in
    let t = esubst u subst t in
    begin match conv_leq env argt t with
    | Result.Ok () -> apply_rec (i + 1) (Esubst.subs_cons (Vars.make_substituend arg) subst) ctx
    | Result.Error () ->
      error_actual_type env (make_judge arg argt) t
    end
  | LocalDef (_, b, _) :: ctx ->
    let b = esubst u subst b in
    apply_rec i (Esubst.subs_cons (Vars.make_substituend b) subst) ctx
  in
  apply_rec 0 (Esubst.subs_id 0) ctx

(* Type of primitive constructs *)
let type_of_prim_type _env u (type a) (prim : a CPrimitives.prim_type) = match prim with
  | CPrimitives.PT_int63 ->
    assert (UVars.Instance.is_empty u);
    Constr.mkSet
  | CPrimitives.PT_float64 ->
    assert (UVars.Instance.is_empty u);
    Constr.mkSet
  | CPrimitives.PT_string ->
    assert (UVars.Instance.is_empty u);
    Constr.mkSet
  | CPrimitives.PT_array ->
    begin match UVars.Instance.to_array u with
    | [||], [|u|] ->
      let ty = Constr.mkType (Univ.Universe.make u) in
      Constr.mkProd(Context.anonR, ty , ty)
    | _ -> anomaly Pp.(str"universe instance for array type should have length 1")
    end

let type_of_int env =
  match (Environ.retroknowledge env).Retroknowledge.retro_int63 with
  | Some c -> UnsafeMonomorphic.mkConst c
  | None -> CErrors.user_err Pp.(str"The type int must be registered before this construction can be typechecked.")

let type_of_float env =
  match (Environ.retroknowledge env).Retroknowledge.retro_float64 with
  | Some c -> UnsafeMonomorphic.mkConst c
  | None -> CErrors.user_err Pp.(str"The type float must be registered before this construction can be typechecked.")

let type_of_string env =
  match (Environ.retroknowledge env).Retroknowledge.retro_string with
  | Some c -> UnsafeMonomorphic.mkConst c
  | None -> CErrors.user_err Pp.(str"The type string must be registered before this construction can be typechecked.")

let type_of_array env u =
  assert (UVars.Instance.length u = (0,1));
  match (Environ.retroknowledge env).Retroknowledge.retro_array with
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
    | ((Type u1 | QSort (_, u1)), Set) ->
        if is_impredicative_set env then
          (* Rule is (Type,Set,Set) in the Set-impredicative calculus *)
          rangsort
        else
          (* Rule is (Type_i,Set,Type_i) in the Set-predicative calculus *)
          Sorts.sort_of_univ (Universe.sup Universe.type0 u1)
    (* Product rule (Prop,Type_i,Type_i) *)
    | (Set,  Type u2)  -> Sorts.sort_of_univ (Universe.sup Universe.type0 u2)
    | (Set,  QSort (q, u2))  ->
      Sorts.qsort q (Universe.sup Universe.type0 u2)
    (* Product rule (Prop,Type_i,Type_i) *)
    | (Prop, (Type _ | QSort _))  -> rangsort
    (* Product rule (Type_i,Type_i,Type_i) *)
    | ((Type u1 | QSort (_, u1)), Type u2) -> Sorts.sort_of_univ (Universe.sup u1 u2)
    | ((Type u1 | QSort (_, u1)), (QSort (q, u2))) ->
      Sorts.qsort q (Universe.sup u1 u2)

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
  let ans = match k with
    | VMcast ->
      Vconv.vm_conv CUMUL env ct expected_type
    | DEFAULTcast ->
      default_conv CUMUL env ct expected_type
    | NATIVEcast ->
      let sigma = Genlambda.empty_evars env in
      Nativeconv.native_conv CUMUL sigma env ct expected_type
  in
  match ans with
  | Result.Ok () -> ()
  | Result.Error () ->
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

let make_param_univs env indu spec args argtys =
  Array.to_list @@ Array.mapi (fun i argt ~default ->
      match (snd (Reduction.dest_arity env argt)) with
      | SProp | exception Reduction.NotArity ->
        Type_errors.error_cant_apply_bad_type env
          (i+1, mkSort default, argt)
          (make_judge (mkIndU indu) (Inductive.type_of_inductive (spec, snd indu)))
          (make_judgev args argtys)
      | Prop -> TemplateProp
      | Set -> TemplateUniv Universe.type0
      | Type u -> TemplateUniv u
      | QSort (q,u) ->
        assert (Environ.Internal.is_above_prop env q);
        TemplateAboveProp (q,u))
    argtys

let type_of_inductive_knowing_parameters env (ind,u as indu) args argst =
  let (mib,_mip) as spec = lookup_mind_specif env ind in
  let () = assert (Option.has_some mib.mind_template) in
  let () = check_hyps_inclusion env (GlobRef.IndRef ind) mib.mind_hyps in
  let param_univs = make_param_univs env indu spec args argst in
  let t, cst = Inductive.type_of_inductive_knowing_parameters (spec,u) param_univs in
  let () = check_constraints cst env in
  t

let type_of_inductive env (ind,u) =
  let (mib,mip) = lookup_mind_specif env ind in
  check_hyps_inclusion env (GlobRef.IndRef ind) mib.mind_hyps;
  let t,cst = Inductive.constrained_type_of_inductive ((mib,mip),u) in
  check_constraints cst env;
  t

(* Constructors. *)

let type_of_constructor_knowing_parameters env (c, u as cu) args argst =
  let ind = inductive_of_constructor c in
  let (mib, _ as spec) = lookup_mind_specif env ind in
  let () = assert (Option.has_some mib.mind_template) in
  let () = check_hyps_inclusion env (GlobRef.ConstructRef c) mib.mind_hyps in
  let param_univs = make_param_univs env (ind, u) spec args argst in
  let t, cst = Inductive.type_of_constructor_knowing_parameters cu spec param_univs in
  let () = check_constraints cst env in
  t

let type_of_constructor env (c,_u as cu) =
  let (mib, _ as specif) = lookup_mind_specif env (inductive_of_constructor c) in
  let () = check_hyps_inclusion env (GlobRef.ConstructRef c) mib.mind_hyps in
  let t,cst = constrained_type_of_constructor cu specif in
  let () = check_constraints cst env in
  t

(* Case. *)

exception NotConvertibleBranch of int * rel_context * types * types

let check_branch_types env (_mib, mip) ci u pms c _ct lft (pctx, p) =
  let open Context.Rel.Declaration in
  let rec instantiate ctx args subst = match ctx, args with
  | [], [] -> subst
  | LocalAssum _ :: ctx, a :: args ->
    let subst = Esubst.subs_cons (Vars.make_substituend a) subst in
    instantiate ctx args subst
  | LocalDef (_, a, _) :: ctx, args ->
    let a = Vars.esubst Vars.lift_substituend subst a in
    let subst = Esubst.subs_cons (Vars.make_substituend a) subst in
    instantiate ctx args subst
  | _ -> assert false
  in
  let iter i (brctx, brt, constrty) =
    let brenv = push_rel_context brctx env in
    let nargs = List.length brctx in
    let pms = Array.map (fun c -> lift nargs c) pms in
    let cargs = Context.Rel.instance mkRel 0 brctx in
    let cstr = mkApp (mkConstructU ((ci.ci_ind, i + 1), u), Array.append pms cargs) in
    let (_, retargs) = find_rectype brenv constrty in
    let indices = List.lastn mip.mind_nrealargs retargs in
    let subst = instantiate (List.rev pctx) (indices @ [cstr]) (Esubst.subs_shft (nargs, Esubst.subs_id 0)) in
    let expbrt = Vars.esubst Vars.lift_substituend subst p in
    match conv_leq brenv brt expbrt with
    | Result.Ok () -> ()
    | Result.Error () -> raise (NotConvertibleBranch (i, brctx, brt, expbrt))
  in
  try Array.iteri iter lft
  with NotConvertibleBranch (i, brctx, brt, expbrt) ->
    let brt = it_mkLambda_or_LetIn brt brctx in
    let expbrt = it_mkLambda_or_LetIn expbrt brctx in
    error_ill_formed_branch env c ((ci.ci_ind, i + 1), u) brt expbrt

let should_invert_case env r ci =
  check_relevance env r Sorts.Relevant &&
  let mib,mip = lookup_mind_specif env ci.ci_ind in
  (* mind_relevance cannot be a pseudo sort poly variable so don't use check_relevance *)
  Sorts.relevance_equal mip.mind_relevance Sorts.Irrelevant &&
  (* NB: it's possible to have 2 ctors or arguments to 1 ctor by unsetting univ checks
     but we don't do special reduction in such cases

     XXX Someday consider more carefully what happens with letin params and arguments
     (currently they're squashed, see indtyping)
 *)
  match Array.length mip.mind_nf_lc with
  | 0 -> true
  | 1 ->
    List.length (fst mip.mind_nf_lc.(0)) = List.length mib.mind_params_ctxt
  | _ -> false

let type_case_scrutinee env (mib, _mip) (u', largs) u pms (pctx, p) c =
  let (params, realargs) = List.chop mib.mind_nparams largs in
  (* Check that the type of the scrutinee is <= the expected argument type *)
  let iter p1 p2 = match Conversion.conv ~l2r:true env p1 p2 with
  | Result.Ok () -> ()
  | Result.Error () -> raise NotConvertible
  in
  let () = try Array.iter2 iter (Array.of_list params) pms
    with NotConvertible -> raise Type_errors.(TypeError (env,IllFormedCaseParams))
  in
  (* We use l2r:true for compat with old versions which used CONV with arguments
     flipped. It is relevant for performance eg in bedrock / Kami. *)
  let qcst, ucst = match mib.mind_variance with
  | None -> UVars.enforce_eq_instances u u' Sorts.QUConstraints.empty
  | Some variance -> UVars.enforce_leq_variance_instances variance u' u Sorts.QUConstraints.empty
  in
  let () = check_qconstraints qcst env in
  let () = check_constraints ucst env in
  let subst = Vars.subst_of_rel_context_instance_list pctx (realargs @ [c]) in
  Vars.substl subst p

let type_of_case env (mib, mip as specif) ci u pms (pctx, pnas, p, rp, pt) iv c ct lf lft =
  let ((ind, u'), largs) =
    try find_rectype env ct
    with Not_found -> error_case_not_inductive env (make_judge c ct) in
  (* Various well-formedness conditions *)
  let () = if Inductive.is_private specif then error_case_on_private_ind env ind in
  let sp = match destSort (Reduction.whd_all (push_rel_context pctx env) pt) with
  | sp -> sp
  | exception DestKO ->
    error_elim_arity env (ind, u') c None
  in
  let () =
    let expected = Sorts.relevance_of_sort sp in
    if check_relevance env rp expected then ()
    else
      error_bad_case_relevance env expected (ci, u, pms, ((pnas, p), rp), iv, c, lf)
  in
  let () = check_case_info env (ind, u') ci in
  let () =
    let is_inversion = match iv with
      | NoInvert -> false
      | CaseInvert _ -> true (* contents already checked *)
    in
    if not (is_inversion = should_invert_case env rp ci)
    then error_bad_invert env
  in
  let () = if not (is_allowed_elimination (specif,u) sp) then begin
    let kinds = Some sp in
    error_elim_arity env (ind, u') c kinds
  end
  in
  (* Check that the scrutinee has the right type *)
  let rslty = type_case_scrutinee env (mib, mip) (u', largs) u pms (pctx, p) c in
  (* We return the "higher" inductive universe instance from the predicate,
     the branches must be typeable using these universes. *)
  let () = check_branch_types env (mib, mip) ci u pms c ct lft (pctx, p) in
  rslty

let type_of_projection env p c ct =
  let pr, pty = lookup_projection p env in
  let (ind,u), args =
    try find_rectype env ct
    with Not_found -> error_case_not_inductive env (make_judge c ct)
  in
  assert(Ind.CanOrd.equal (Projection.inductive p) ind);
  let pr = UVars.subst_instance_relevance u pr in
  let ty = Vars.subst_instance_constr u pty in
  pr, substl (c :: CList.rev args) ty


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
  | VarRef id -> Environ.named_type id env, UVars.AbstractContext.empty
  | ConstRef c ->
    let cb = Environ.lookup_constant c env in
    let univs = Declareops.constant_polymorphic_context cb in
    cb.Declarations.const_type, univs
  | IndRef ind ->
    let (mib,_ as specif) = Inductive.lookup_mind_specif env ind in
    let univs = Declareops.inductive_polymorphic_context mib in
    let inst = UVars.make_abstract_instance univs in
    Inductive.type_of_inductive (specif, inst), univs
  | ConstructRef cstr ->
    let (mib,_ as specif) =
      Inductive.lookup_mind_specif env (inductive_of_constructor cstr)
    in
    let univs = Declareops.inductive_polymorphic_context mib in
    let inst = UVars.make_abstract_instance univs in
    Inductive.type_of_constructor (cstr,inst) specif, univs

(************************************************************************)
(************************************************************************)

let check_assum_annot env s x t =
  let r = x.binder_relevance in
  let r' = Sorts.relevance_of_sort s in
  if check_relevance env r' r
  then ()
  else error_bad_binder_relevance env r' (RelDecl.LocalAssum (x, t))


let check_let_annot env s x c t =
  let r = x.binder_relevance in
  let r' = Sorts.relevance_of_sort s in
  if check_relevance env r' r
  then ()
  else error_bad_binder_relevance env r' (RelDecl.LocalDef (x, c, t))

let push_rec_types (lna,typarray,_) env =
  let ctxt = Array.map2_i (fun i na t -> RelDecl.LocalAssum (na, lift i t)) lna typarray in
  Array.fold_left (fun e assum -> push_rel assum e) env ctxt

(* The typing machine. *)
let rec execute tbl env cstr =
  if Int.equal (HConstr.refcount cstr) 1 then execute_aux tbl env cstr
  else begin match HConstr.Tbl.find_opt tbl cstr with
    | Some v -> v
    | None ->
      let v = execute_aux tbl env cstr in
      HConstr.Tbl.add tbl cstr v;
      v
  end

and execute_aux tbl env cstr =
  let open Context.Rel.Declaration in
  let self = HConstr.self in
  match HConstr.kind cstr with
    (* Atomic terms *)
    | Sort s ->
      let () = match s with
      | SProp -> if not (Environ.sprop_allowed env) then error_disallowed_sprop env
      | QSort _ | Prop | Set | Type _ -> ()
      in
      type_of_sort s

    | Rel n ->
      type_of_relative env n

    | Var id ->
      type_of_variable env id

    | Const c ->
      type_of_constant env c

    | Proj (p, r, c) ->
      let ct = execute tbl env c in
      let r', ty = type_of_projection env p (self c) ct in
      assert (check_relevance env r r');
      ty

    (* Lambda calculus operators *)
    | App (f,args) ->
      let argst = execute_array tbl env args in
      let args = snd @@ destApp (self cstr) in
        let ft =
          match HConstr.kind f with
          | Ind ind when Environ.template_polymorphic_pind ind env ->
            type_of_inductive_knowing_parameters env ind args argst
          | Construct ((ind, _), _ as cstr) when Environ.template_polymorphic_ind ind env ->
            type_of_constructor_knowing_parameters env cstr args argst
          | _ ->
            (* No template polymorphism *)
            execute tbl env f
        in
        type_of_apply env (self f) ft args argst

    | Lambda (name,c1,c2) ->
      let s = execute_is_type tbl env c1 in
      let () = check_assum_annot env s name (self c1) in
      let env1 = push_rel (LocalAssum (name,self c1)) env in
      let c2t = execute tbl env1 c2 in
      type_of_abstraction env name (self c1) c2t

    | Prod (name,c1,c2) ->
      let vars = execute_is_type tbl env c1 in
      let () = check_assum_annot env vars name (self c1) in
      let env1 = push_rel (LocalAssum (name,self c1)) env in
      let vars' = execute_is_type tbl env1 c2 in
      type_of_product env name vars vars'

    | LetIn (name,c1,c2,c3) ->
      let c1t = execute tbl env c1 in
      let c2s = execute_is_type tbl env c2 in
      let c1 = self c1 in
      let c2 = self c2 in
      let () = check_let_annot env c2s name c1 c2 in
      let () = check_cast env c1 c1t DEFAULTcast c2 in
      let env1 = push_rel (LocalDef (name,c1,c2)) env in
      let c3t = execute tbl env1 c3 in
      subst1 c1 c3t

    | Cast (c,k,t) ->
      let ct = execute tbl env c in
      let _ts : Sorts.t = execute_is_type tbl env t in
      let () = check_cast env (self c) ct k (self t) in
      self t

    (* Inductive types *)
    | Ind ind ->
      type_of_inductive env ind

    | Construct c ->
      type_of_constructor env c

    | Case (ci, u, pms, (p,_), iv, c, lf) ->
        let ct = execute tbl env c in
        let () = match iv with
          | NoInvert -> ()
          | CaseInvert {indices} ->
            let args = Array.append pms indices in
            let ct' =
              let mk = HConstr.of_kind_nohashcons in
              mk @@ App (mk @@ Ind (ci.ci_ind,u), args)
            in
            let _ : Sorts.t = execute_is_type tbl env ct' in
            match conv_leq env ct (self ct') with
            | Result.Ok () -> ()
            | Result.Error () -> error_bad_invert env (* TODO: more informative message *)

        in
        let mib, mip = Inductive.lookup_mind_specif env ci.ci_ind in
        let pmst = execute_array tbl env pms in
        let pms = Array.map self pms in
        let cst, params = match mib.mind_template with
        | None ->
          let cst = Inductive.instantiate_inductive_constraints mib u in
          cst, mib.mind_params_ctxt
        | Some _ ->
          let args = make_param_univs env (ci.ci_ind, u) (mib, mip) pms pmst in
          let (cst, params, _) = instantiate_template_universes (mib, mip) args in
          cst, params
        in
        let () = check_constraints cst env in
        let paramsubst =
          try type_of_parameters env params u pms pmst
          with ArgumentsMismatch -> error_elim_arity env (ci.ci_ind, u) (self c) None
        in
        let (pctx, pt) =
          let (nas, p) = p in
          let realdecls, _ = List.chop mip.mind_nrealdecls mip.mind_arity_ctxt in
          let self =
            let args = Context.Rel.instance mkRel 0 mip.mind_arity_ctxt in
            let inst = UVars.Instance.(abstract_instance (length u)) in
            mkApp (mkIndU (ci.ci_ind, inst), args)
          in
          let realdecls = LocalAssum (Context.make_annot Anonymous mip.mind_relevance, self) :: realdecls in
          let realdecls =
            try instantiate_context env u paramsubst nas realdecls
            with ArgumentsMismatch -> error_elim_arity env (ci.ci_ind, u) (HConstr.self c) None
          in
          let p_env = Environ.push_rel_context realdecls env in
          let pt = execute tbl p_env p in
          (realdecls, pt)
        in
        let () =
          let nbranches = Array.length mip.mind_nf_lc in
          if not (Int.equal (Array.length lf) nbranches) then
            error_number_branches env (make_judge (self c) ct) nbranches
        in
        let build_one_branch i (nas, br) =
          let (ctx, cty) = mip.mind_nf_lc.(i) in
          let ctx, _ = List.chop mip.mind_consnrealdecls.(i) ctx in
          let ctx =
            try instantiate_context env u paramsubst nas ctx
            with ArgumentsMismatch ->
              (* Despite the name, the toplevel message is reasonable *)
              error_elim_arity env (ci.ci_ind, u) (self c) None
          in
          let br_env = Environ.push_rel_context ctx env in
          let brt = execute tbl br_env br in
          let cty = esubst u (Esubst.subs_liftn mip.mind_consnrealdecls.(i) paramsubst) cty in
          (ctx, brt, cty)
        in
        let lft = Array.mapi build_one_branch lf in
        (* easier than mapping self over various shapes of arrays *)
        let (ci, u, pms, (p,rp), iv, c, lf) = destCase (self cstr) in
        type_of_case env (mib, mip) ci u pms (pctx, fst p, snd p, rp, pt) iv c ct lf lft

    | Fix ((_,i),recdef) ->
      let fix_ty = execute_recdef tbl env recdef i in
      check_fix env (destFix @@ self cstr);
      fix_ty

    | CoFix (i,recdef) ->
      let fix_ty = execute_recdef tbl env recdef i in
      check_cofix env (destCoFix @@ self cstr);
      fix_ty

    (* Primitive types *)
    | Int _ -> type_of_int env
    | Float _ -> type_of_float env
    | String _ -> type_of_string env
    | Array(u,t,def,ty) ->
      (* ty : Type@{u} and all of t,def : ty *)
      let ulev = match UVars.Instance.to_array u with
        | [||], [|u|] -> u
        | _ -> assert false
      in
      let tyty = execute tbl env ty in
      let ty = self ty in
      check_cast env ty tyty DEFAULTcast (mkType (Universe.make ulev));
      let def_ty = execute tbl env def in
      check_cast env (self def) def_ty DEFAULTcast ty;
      let ta = type_of_array env u in
      let () = Array.iter (fun x ->
          let xt = execute tbl env x in
          check_cast env (self x) xt DEFAULTcast ty)
          t
      in
      mkApp(ta, [|ty|])

    (* Partial proofs: unsupported by the kernel *)
    | Meta _ ->
        anomaly (Pp.str "the kernel does not support metavariables.")

    | Evar _ ->
        anomaly (Pp.str "the kernel does not support existential variables.")

and execute_is_type tbl env constr =
  let t = execute tbl env constr in
  check_type env (HConstr.self constr) t

and execute_recdef tbl env (names,lar,vdef) i =
  let lart = execute_array tbl env lar in
  let lar = Array.map HConstr.self lar in
  let () = Array.iteri (fun i na -> check_assumption env na lar.(i) lart.(i)) names in
  let env1 = push_rec_types (names,lar,vdef) env in (* vdef is ignored *)
  let vdeft = execute_array tbl env1 vdef in
  let vdef = Array.map HConstr.self vdef in
  let () = check_fixpoint env1 names lar vdef vdeft in
  lar.(i)

and execute_array tbl env cs =
  Array.map (fun c -> execute tbl env c) cs

let execute env c =
  NewProfile.profile "Typeops.execute" (fun () -> execute (HConstr.Tbl.create ()) env c) ()

(* Derived functions *)

let check_declared_qualities env qualities =
  let module S = Sorts.QVar.Set in
  let unknown = S.diff qualities (Environ.qualities env) in
  if S.is_empty unknown then ()
  else error_undeclared_qualities env unknown

let check_wellformed_universes env c =
  let qualities, univs = sort_and_universes_of_constr c in
  check_declared_qualities env qualities;
  match UGraph.check_declared_universes (universes env) univs
  with
  | Ok () -> ()
  | Error u -> error_undeclared_universes env u

let check_wellformed_universes env c =
  NewProfile.profile "check-wf-univs" (fun () -> check_wellformed_universes env c) ()

let infer_hconstr env hconstr =
  let constr = HConstr.self hconstr in
  let () = check_wellformed_universes env constr in
  let t = execute env hconstr in
  make_judge constr t

let infer env c =
  let c = HConstr.of_constr env c in
  infer_hconstr env c

let assumption_of_judgment env {uj_val=c; uj_type=t} =
  infer_assumption env c t

let infer_type env constr =
  let () = check_wellformed_universes env constr in
  let hconstr = HConstr.of_constr env constr in
  let constr = HConstr.self hconstr in
  let t = execute env hconstr in
  let s = check_type env constr t in
  {utj_val = constr; utj_type = s}

(* Typing of several terms. *)

let check_context env rels =
  let open Context.Rel.Declaration in
  Context.Rel.fold_outside (fun d (env,rels) ->
    match d with
      | LocalAssum (x,ty) ->
        let jty = infer_type env ty in
        let () = check_assum_annot env jty.utj_type x jty.utj_val in
        push_rel d env, LocalAssum (x,jty.utj_val) :: rels
      | LocalDef (x,bd,ty) ->
        let j1 = infer env bd in
        let jty = infer_type env ty in
        let () = match conv_leq env j1.uj_type ty with
        | Result.Ok () -> ()
        | Result.Error () -> error_actual_type env j1 ty
        in
        let () = check_let_annot env jty.utj_type x j1.uj_val jty.utj_val in
        push_rel d env, LocalDef (x,j1.uj_val,jty.utj_val) :: rels)
    rels ~init:(env,[])

let check_cast env cj k tj =
  check_cast env cj.uj_val cj.uj_type k tj.utj_val

(* Building type of primitive operators and type *)

let type_of_prim_const env _u c =
  let int_ty () = type_of_int env in
  match c with
  | CPrimitives.Arraymaxlength ->
    int_ty ()
  | CPrimitives.Stringmaxlength ->
    int_ty ()

let type_of_prim env u t =
  let module UM = UnsafeMonomorphic in
  let int_ty () = type_of_int env in
  let float_ty () = type_of_float env in
  let string_ty () = type_of_string env in
  let array_ty u a = mkApp(type_of_array env u, [|a|]) in
  let bool_ty () =
    match (Environ.retroknowledge env).Retroknowledge.retro_bool with
    | Some ((ind,_),_) -> UM.mkInd ind
    | None -> CErrors.user_err Pp.(str"The type bool must be registered before this primitive.")
  in
  let compare_ty () =
    match (Environ.retroknowledge env).Retroknowledge.retro_cmp with
    | Some ((ind,_),_,_) -> UM.mkInd ind
    | None -> CErrors.user_err Pp.(str"The type compare must be registered before this primitive.")
  in
  let f_compare_ty () =
    match (Environ.retroknowledge env).Retroknowledge.retro_f_cmp with
    | Some ((ind,_),_,_,_) -> UM.mkInd ind
    | None -> CErrors.user_err Pp.(str"The type float_comparison must be registered before this primitive.")
  in
  let f_class_ty () =
    match (Environ.retroknowledge env).Retroknowledge.retro_f_class with
    | Some ((ind,_),_,_,_,_,_,_,_,_) -> UM.mkInd ind
    | None -> CErrors.user_err Pp.(str"The type float_class must be registered before this primitive.")
  in
  let pair_ty fst_ty snd_ty =
    match (Environ.retroknowledge env).Retroknowledge.retro_pair with
    | Some (ind,_) -> Constr.mkApp(UM.mkInd ind, [|fst_ty;snd_ty|])
    | None -> CErrors.user_err Pp.(str"The type pair must be registered before this primitive.")
  in
  let carry_ty int_ty =
    match (Environ.retroknowledge env).Retroknowledge.retro_carry with
    | Some ((ind,_),_) -> Constr.mkApp(UM.mkInd ind, [|int_ty|])
    | None -> CErrors.user_err Pp.(str"The type carry must be registered before this primitive.")
  in
  let open CPrimitives in
  let tr_prim_type (tr_type : ind_or_type -> constr) (type a) (ty : a prim_type) (t : a) = match ty with
    | PT_int63 -> int_ty t
    | PT_float64 -> float_ty t
    | PT_string -> string_ty t
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
  assert (UVars.AbstractContext.size (univs t) = UVars.Instance.length u);
  Vars.subst_instance_constr u
    (Term.it_mkProd_or_LetIn (nary_op 0 ret_ty args_ty) params)

let type_of_prim_or_type env u = let open CPrimitives in
  function
  | OT_type t -> type_of_prim_type env u t
  | OT_op op -> type_of_prim env u op
  | OT_const c -> type_of_prim_const env u c
