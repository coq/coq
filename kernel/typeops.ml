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

type ('constr,'types) bad_relevance =
| BadRelevanceBinder of Sorts.relevance * ('constr,'types) Context.Rel.Declaration.pt
| BadRelevanceCase of Sorts.relevance * 'constr

let warn_bad_relevance_name = "bad-relevance"

let bad_relevance_warning =
  CWarnings.create_warning ~name:warn_bad_relevance_name ~default:CWarnings.AsError ()

let bad_relevance_msg = CWarnings.create_msg bad_relevance_warning ()

let default_print_bad_relevance = function
  | BadRelevanceCase _ -> Pp.str "Bad relevance in case annotation."
  | BadRelevanceBinder (_, na) ->
    Pp.(str "Bad relevance for binder " ++ Name.print (RelDecl.get_name na) ++ str ".")

(* used eg in the checker *)
let () = CWarnings.register_printer bad_relevance_msg
    (fun (_env,b) -> default_print_bad_relevance b)

let warn_bad_relevance_case ?loc env rlv case =
  match CWarnings.warning_status bad_relevance_warning with
| CWarnings.Disabled | CWarnings.Enabled ->
  CWarnings.warn bad_relevance_msg ?loc (env, BadRelevanceCase (rlv, mkCase case))
| CWarnings.AsError ->
  error_bad_case_relevance env rlv case

let warn_bad_relevance_binder ?loc env rlv bnd =
  match CWarnings.warning_status bad_relevance_warning with
| CWarnings.Disabled | CWarnings.Enabled ->
  CWarnings.warn bad_relevance_msg ?loc (env, BadRelevanceBinder (rlv, bnd))
| CWarnings.AsError ->
  error_bad_binder_relevance env rlv bnd

let check_assumption env x t ty =
  let r = x.binder_relevance in
  let r' = infer_assumption env t ty in
  let x =
    if Sorts.relevance_equal r r' then x
    else
      let () = warn_bad_relevance_binder env r' (RelDecl.LocalAssum (x, t)) in
      {x with binder_relevance = r'}
  in
  x

let check_binding_relevance na1 na2 =
  (* Since we know statically the relevance here, we are stricter *)
  assert (Sorts.relevance_equal (binder_relevance na1) (binder_relevance na2))

let esubst u s c =
  Vars.esubst Vars.lift_substituend s (subst_instance_constr u c)

exception ArgumentsMismatch

let instantiate_context u subst nas ctx =
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
    let () = check_binding_relevance na nas.(i) in
    LocalAssum (nas.(i), ty) :: ctx
  | LocalDef (na, ty, bdy) :: ctx ->
    let ctx = instantiate (pred i) ctx in
    let subst = Esubst.subs_liftn i subst in
    let na = instantiate_relevance na in
    let ty = esubst u subst ty in
    let bdy = esubst u subst bdy in
    let () = check_binding_relevance na nas.(i) in
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
  let infos = create_clos_infos RedFlags.all env in
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
        | () -> apply_rec (i+1) (mk_clos (CClosure.usubs_cons (inject arg) e) c2)
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
    | () -> apply_rec (i + 1) (Esubst.subs_cons (Vars.make_substituend arg) subst) ctx
    | exception NotConvertible ->
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
  | CPrimitives.PT_array ->
    begin match UVars.Instance.to_array u with
    | [||], [|u|] ->
      let ty = Constr.mkType (Univ.Universe.make u) in
      Constr.mkProd(Context.anonR, ty , ty)
    | _ -> anomaly Pp.(str"universe instance for array type should have length 1")
    end

let type_of_int env =
  match env.retroknowledge.Retroknowledge.retro_int63 with
  | Some c -> UnsafeMonomorphic.mkConst c
  | None -> CErrors.user_err Pp.(str"The type int must be registered before this construction can be typechecked.")

let type_of_float env =
  match env.retroknowledge.Retroknowledge.retro_float64 with
  | Some c -> UnsafeMonomorphic.mkConst c
  | None -> CErrors.user_err Pp.(str"The type float must be registered before this construction can be typechecked.")

let type_of_array env u =
  assert (UVars.Instance.length u = (0,1));
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
  try
    match k with
    | VMcast ->
      Vconv.vm_conv CUMUL env ct expected_type
    | DEFAULTcast ->
      default_conv CUMUL env ct expected_type
    | NATIVEcast ->
      let sigma = Genlambda.empty_evars env in
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

let make_param_univs env indu spec args argtys =
  Array.to_list @@ Array.mapi (fun i argt ~expected ->
      match (snd (Reduction.dest_arity env argt)) with
      | SProp | exception Reduction.NotArity ->
        Type_errors.error_cant_apply_bad_type env
          (i+1, mkType (Universe.make expected), argt)
          (make_judge (mkIndU indu) (Inductive.type_of_inductive (spec, snd indu)))
          (make_judgev args argtys)
      | Prop -> TemplateProp
      | Set -> TemplateUniv Universe.type0
      | Type u -> TemplateUniv u
      | QSort _ -> assert false)
    argtys

let type_of_inductive_knowing_parameters env (ind,u as indu) args argst =
  let (mib,_mip) as spec = lookup_mind_specif env ind in
  check_hyps_inclusion env (GlobRef.IndRef ind) mib.mind_hyps;
  let t,cst = Inductive.constrained_type_of_inductive_knowing_parameters
      (spec,u) (make_param_univs env indu spec args argst)
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
    try conv_leq brenv brt expbrt
    with NotConvertible -> raise (NotConvertibleBranch (i, brctx, brt, expbrt))
  in
  try Array.iteri iter lft
  with NotConvertibleBranch (i, brctx, brt, expbrt) ->
    let brt = it_mkLambda_or_LetIn brt brctx in
    let expbrt = it_mkLambda_or_LetIn expbrt brctx in
    error_ill_formed_branch env c ((ci.ci_ind, i + 1), u) brt expbrt

let should_invert_case env r ci =
  Sorts.relevance_equal r Sorts.Relevant &&
  let mib,mip = lookup_mind_specif env ci.ci_ind in
  Sorts.relevance_equal mip.mind_relevance Sorts.Irrelevant &&
  (* NB: it's possible to have 2 ctors or arguments to 1 ctor by unsetting univ checks
     but we don't do special reduction in such cases

     XXX Someday consider more carefully what happens with letin params and arguments
     (currently they're squashed, see indtyping)
 *)
  Array.length mip.mind_nf_lc = 1 &&
  List.length (fst mip.mind_nf_lc.(0)) = List.length mib.mind_params_ctxt

let type_case_scrutinee env (mib, _mip) (u', largs) u pms (pctx, p) c =
  let (params, realargs) = List.chop mib.mind_nparams largs in
  (* Check that the type of the scrutinee is <= the expected argument type *)
  let () = try Array.iter2 (fun p1 p2 -> Conversion.conv ~l2r:true env p1 p2) (Array.of_list params) pms
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
  let rp =
    let expected = Sorts.relevance_of_sort sp in
    if Sorts.relevance_equal rp expected then rp
    else
      let () = warn_bad_relevance_case env expected (ci, u, pms, ((pnas, p), rp), iv, c, lf) in
      expected
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
  rp, rslty

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
  if Sorts.relevance_equal r' r
  then x
  else
    let () = warn_bad_relevance_binder env r' (RelDecl.LocalAssum (x, t)) in
    {x with binder_relevance = r'}

let check_let_annot env s x c t =
  let r = x.binder_relevance in
  let r' = Sorts.relevance_of_sort s in
  if Sorts.relevance_equal r' r
  then x
  else
    let () = warn_bad_relevance_binder env r' (RelDecl.LocalDef (x, c, t)) in
    {x with binder_relevance = r'}

(* The typing machine. *)
    (* ATTENTION : faudra faire le typage du contexte des Const,
    Ind et Constructsi un jour cela devient des constructions
    arbitraires et non plus des variables *)
let rec execute env cstr =
  let open Context.Rel.Declaration in
  match kind cstr with
    (* Atomic terms *)
    | Sort s ->
      let () = match s with
      | SProp -> if not (Environ.sprop_allowed env) then error_disallowed_sprop env
      | QSort _ | Prop | Set | Type _ -> ()
      in
      cstr, type_of_sort s

    | Rel n ->
      cstr, type_of_relative env n

    | Var id ->
      cstr, type_of_variable env id

    | Const c ->
      cstr, type_of_constant env c

    | Proj (p, r, c) ->
      let c', ct = execute env c in
      let r', ty = type_of_projection env p c' ct in
      assert (Sorts.relevance_equal r r');
      let cstr = if c == c' then cstr else mkProj (p,r,c') in
      cstr, ty

    (* Lambda calculus operators *)
    | App (f,args) ->
      let args', argst = execute_array env args in
        let f', ft =
          match kind f with
          | Ind ind when Environ.template_polymorphic_pind ind env ->
            f, type_of_inductive_knowing_parameters env ind args' argst
          | _ ->
            (* No template polymorphism *)
            execute env f
        in
        let cstr = if f == f' && args == args' then cstr else mkApp (f',args') in
        cstr, type_of_apply env f' ft args' argst

    | Lambda (name,c1,c2) ->
      let c1', s = execute_is_type env c1 in
      let name' = check_assum_annot env s name c1' in
      let env1 = push_rel (LocalAssum (name',c1')) env in
      let c2', c2t = execute env1 c2 in
      let cstr = if name == name' && c1 == c1' && c2 == c2' then cstr else mkLambda(name',c1',c2') in
      cstr, type_of_abstraction env name' c1 c2t

    | Prod (name,c1,c2) ->
      let c1', vars = execute_is_type env c1 in
      let name' = check_assum_annot env vars name c1' in
      let env1 = push_rel (LocalAssum (name',c1')) env in
      let c2', vars' = execute_is_type env1 c2 in
      let cstr = if name == name' && c1 == c1' && c2 == c2' then cstr else mkProd(name',c1',c2') in
      cstr, type_of_product env name' vars vars'

    | LetIn (name,c1,c2,c3) ->
      let c1', c1t = execute env c1 in
      let c2', c2s = execute_is_type env c2 in
      let name' = check_let_annot env c2s name c1' c2' in
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

    | Case (ci, u, pms, (p,rp), iv, c, lf) ->
        let c', ct = execute env c in
        let iv' = match iv with
          | NoInvert -> NoInvert
          | CaseInvert {indices} ->
            let args = Array.append pms indices in
            let ct' = mkApp (mkIndU (ci.ci_ind,u), args) in
            let (ct', _) : constr * Sorts.t = execute_is_type env ct' in
            let () = conv_leq env ct ct' in
            let _, args' = decompose_app ct' in
            if args == args' then iv
            else CaseInvert {indices=Array.sub args' (Array.length pms) (Array.length indices)}
        in
        let mib, mip = Inductive.lookup_mind_specif env ci.ci_ind in
        let cst = Inductive.instantiate_inductive_constraints mib u in
        let () = check_constraints cst env in
        let pms', pmst = execute_array env pms in
        let paramsubst =
          try type_of_parameters env mib.mind_params_ctxt u pms' pmst
          with ArgumentsMismatch -> error_elim_arity env (ci.ci_ind, u) c' None
        in
        let (pctx, p', pt) =
          let (nas, p) = p in
          let realdecls, _ = List.chop mip.mind_nrealdecls mip.mind_arity_ctxt in
          let self =
            let args = Context.Rel.instance mkRel 0 mip.mind_arity_ctxt in
            let inst = UVars.Instance.(abstract_instance (length u)) in
            mkApp (mkIndU (ci.ci_ind, inst), args)
          in
          let realdecls = LocalAssum (Context.make_annot Anonymous mip.mind_relevance, self) :: realdecls in
          let realdecls =
            try instantiate_context u paramsubst nas realdecls
            with ArgumentsMismatch -> error_elim_arity env (ci.ci_ind, u) c' None
          in
          let p_env = Environ.push_rel_context realdecls env in
          let p', pt = execute p_env p in
          (realdecls, p', pt)
        in
        let () =
          let nbranches = Array.length mip.mind_nf_lc in
          if not (Int.equal (Array.length lf) nbranches) then
            error_number_branches env (make_judge c ct) nbranches
        in
        let lft = Array.make (Array.length lf) ([], mkProp, mkProp) in
        let build_one_branch i (nas, br as b) =
          let (ctx, cty) = mip.mind_nf_lc.(i) in
          let ctx, _ = List.chop mip.mind_consnrealdecls.(i) ctx in
          let ctx =
            try instantiate_context u paramsubst nas ctx
            with ArgumentsMismatch ->
              (* Despite the name, the toplevel message is reasonable *)
              error_elim_arity env (ci.ci_ind, u) c' None
          in
          let br_env = Environ.push_rel_context ctx env in
          let br', brt = execute br_env br in
          let cty = esubst u (Esubst.subs_liftn mip.mind_consnrealdecls.(i) paramsubst) cty in
          let () = lft.(i) <- (ctx, brt, cty) in
          if br == br' then b else (nas, br')
        in
        let lf' = Array.Smart.map_i build_one_branch lf in
        let rp', t = type_of_case env (mib, mip) ci u pms' (pctx, fst p, p', rp, pt) iv' c' ct lf' lft in
        let eqbr (_, br1) (_, br2) = br1 == br2 in
        let cstr = if rp == rp' && pms == pms' && c == c' && snd p == p' && iv == iv' && Array.equal eqbr lf lf' then cstr
          else mkCase (ci, u, pms', ((fst p, p'), rp'), iv', c', lf')
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
      let ulev = match UVars.Instance.to_array u with
        | [||], [|u|] -> u
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

let execute env c =
  NewProfile.profile "Typeops.infer" (fun () -> execute env c) ()

(* Derived functions *)

let check_declared_qualities env qualities =
  let module S = Sorts.QVar.Set in
  let unknown = S.diff qualities env.env_qualities in
  if S.is_empty unknown then ()
  else error_undeclared_qualities env unknown

let check_wellformed_universes env c =
  let qualities, univs = sort_and_universes_of_constr c in
  check_declared_qualities env qualities;
  try UGraph.check_declared_universes (universes env) univs
  with UGraph.UndeclaredLevel u ->
    error_undeclared_universe env u

let check_wellformed_universes env c =
  NewProfile.profile "check-wf-univs" (fun () -> check_wellformed_universes env c) ()

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
        let x = check_assum_annot env jty.utj_type x jty.utj_val in
        push_rel d env, LocalAssum (x,jty.utj_val) :: rels
      | LocalDef (x,bd,ty) ->
        let j1 = infer env bd in
        let jty = infer_type env ty in
        conv_leq env j1.uj_type ty;
        let x = check_let_annot env jty.utj_type x j1.uj_val jty.utj_val in
        push_rel d env, LocalDef (x,j1.uj_val,jty.utj_val) :: rels)
    rels ~init:(env,[])

let judge_of_prop = make_judge mkProp type1
let judge_of_set = make_judge mkSet type1
let judge_of_type u = make_judge (mkType u) (type_of_type u)

let judge_of_relative env k = make_judge (mkRel k) (type_of_relative env k)

let judge_of_variable env x = make_judge (mkVar x) (type_of_variable env x)

let judge_of_constant env cst = make_judge (mkConstU cst) (type_of_constant env cst)

let judge_of_projection env p cj =
  let r, ty = type_of_projection env p cj.uj_val cj.uj_type in
  make_judge (mkProj (p,r,cj.uj_val)) ty

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
  let module UM = UnsafeMonomorphic in
  let int_ty () = type_of_int env in
  let float_ty () = type_of_float env in
  let array_ty u a = mkApp(type_of_array env u, [|a|]) in
  let bool_ty () =
    match env.retroknowledge.Retroknowledge.retro_bool with
    | Some ((ind,_),_) -> UM.mkInd ind
    | None -> CErrors.user_err Pp.(str"The type bool must be registered before this primitive.")
  in
  let compare_ty () =
    match env.retroknowledge.Retroknowledge.retro_cmp with
    | Some ((ind,_),_,_) -> UM.mkInd ind
    | None -> CErrors.user_err Pp.(str"The type compare must be registered before this primitive.")
  in
  let f_compare_ty () =
    match env.retroknowledge.Retroknowledge.retro_f_cmp with
    | Some ((ind,_),_,_,_) -> UM.mkInd ind
    | None -> CErrors.user_err Pp.(str"The type float_comparison must be registered before this primitive.")
  in
  let f_class_ty () =
    match env.retroknowledge.Retroknowledge.retro_f_class with
    | Some ((ind,_),_,_,_,_,_,_,_,_) -> UM.mkInd ind
    | None -> CErrors.user_err Pp.(str"The type float_class must be registered before this primitive.")
  in
  let pair_ty fst_ty snd_ty =
    match env.retroknowledge.Retroknowledge.retro_pair with
    | Some (ind,_) -> Constr.mkApp(UM.mkInd ind, [|fst_ty;snd_ty|])
    | None -> CErrors.user_err Pp.(str"The type pair must be registered before this primitive.")
  in
  let carry_ty int_ty =
    match env.retroknowledge.Retroknowledge.retro_carry with
    | Some ((ind,_),_) -> Constr.mkApp(UM.mkInd ind, [|int_ty|])
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
  assert (UVars.AbstractContext.size (univs t) = UVars.Instance.length u);
  Vars.subst_instance_constr u
    (Term.it_mkProd_or_LetIn (nary_op 0 ret_ty args_ty) params)

let type_of_prim_or_type env u = let open CPrimitives in
  function
  | OT_type t -> type_of_prim_type env u t
  | OT_op op -> type_of_prim env u op
  | OT_const c -> type_of_prim_const env u c
