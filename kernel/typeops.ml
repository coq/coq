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
open Stages
open SVars
open Annot
open State
open Constraints
open Staging
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

let conv_leq l2r env x y = default_conv CUMUL ~l2r env x y

let conv_leq_vecti env v1 v2 =
  Array.fold_left2_i
    (fun i cstrnts t1 t2 ->
      try union cstrnts (conv_leq false env t1 t2)
      with NotConvertible -> raise (NotConvertibleVect i))
    (empty ())
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

let stage_vars_in_relative env n =
  try env |> lookup_rel n |> RelDecl.get_value |> Option.map count_annots
  with Not_found ->
    error_unbound_rel env n

(* Type of variables *)
let type_of_variable env id =
  try named_type id env
  with Not_found ->
    error_unbound_var env id

let stage_vars_in_variable env id =
  try env |> named_body id |> Option.map count_annots
  with Not_found ->
    error_unbound_var env id

(* Management of context of variables. *)

(* Checks if a context of variables can be instantiated by the
   variables of the current env.
   Order does not have to be checked assuming that all names are distinct *)
let check_hyps_inclusion env ?evars c sign =
  let conv env a b = conv env ?evars a b in
  Context.Named.fold_outside
    (fun d1 cstrnts ->
      let open Context.Named.Declaration in
      let id = NamedDecl.get_id d1 in
      try
        let d2 = lookup_named id env in
        let cstrnts' = union cstrnts (conv env (get_type d2) (get_type d1)) in
        (match d2,d1 with
        | LocalAssum _, LocalAssum _ -> cstrnts'
        | LocalAssum _, LocalDef _ ->
            (* This is wrong, because we don't know if the body is
               needed or not for typechecking: *) cstrnts'
        | LocalDef _, LocalAssum _ -> raise NotConvertible
        | LocalDef (_,b2,_), LocalDef (_,b1,_) -> conv env b2 b1);
      with Not_found | NotConvertible | Option.Heterogeneous ->
        error_reference_variables env id c)
    sign
    ~init:(empty ())

(* Instantiation of terms on real arguments. *)

(* Make a type polymorphic if an arity *)

(* Type of constants *)


let type_of_constant env (kn,_u as cst) =
  let cb = lookup_constant kn env in
  let cstrnts = check_hyps_inclusion env (GlobRef.ConstRef kn) cb.const_hyps in
  let ty, cu = constant_type env cst in
  let () = check_constraints cu env in
    ty, cstrnts

let type_of_constant_in env (kn,_u as cst) =
  let cb = lookup_constant kn env in
  let cstrnts = check_hyps_inclusion env (GlobRef.ConstRef kn) cb.const_hyps in
  constant_type_in env cst, cstrnts

let stage_vars_in_constant env (kn, _) =
  let cb = lookup_constant kn env in
  match cb.const_body with
  | Def c -> Some (count_annots @@ Mod_subst.force_constr c)
  | _ -> None

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
    if Int.equal i len then term_of_fconstr typ, empty ()
    else
      let typ, stk = whd_stack infos tab typ [] in
      (** The return stack is known to be empty *)
      let () = assert (check_empty_stack stk) in
      match fterm_of typ with
      | FProd (_, c1, c2, e) ->
        let arg = argsv.(i) in
        let argt = argstv.(i) in
        let c1 = term_of_fconstr c1 in
        begin match conv_leq false env argt c1 with
        | cstrnts ->
          let ty, cstrnts' = apply_rec (i+1) (mk_clos (Esubst.subs_cons ([| inject arg |], e)) c2) in
          ty, union cstrnts cstrnts'
        | exception NotConvertible ->
          error_cant_apply_bad_type env
            (i+1,c1,argt)
            (make_judge func funt)
            (make_judgev argsv argstv),
          empty ()
        end
      | _ ->
        error_cant_apply_not_functional env
          (make_judge func funt)
          (make_judgev argsv argstv),
        empty ()
  in
  apply_rec 0 (inject funt)

(* Type of primitive constructs *)
let type_of_prim_type _env = function
  | CPrimitives.PT_int63 -> Constr.mkSet
  | CPrimitives.PT_float64 -> Constr.mkSet

let type_of_int env =
  match env.retroknowledge.Retroknowledge.retro_int63 with
  | Some c -> mkConst c
  | None -> CErrors.user_err Pp.(str"The type int must be registered before this construction can be typechecked.")

let type_of_float env =
  match env.retroknowledge.Retroknowledge.retro_float64 with
  | Some c -> mkConst c
  | None -> raise
        (Invalid_argument "Typeops.type_of_float: float64 not_defined")

let type_of_prim env t =
  let int_ty () = type_of_int env in
  let float_ty () = type_of_float env in
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
  let tr_prim_type = function
    | PT_int63 -> int_ty ()
    | PT_float64 -> float_ty () in
  let tr_ind (type t) (i : t prim_ind) (a : t) = match i, a with
    | PIT_bool, () -> bool_ty ()
    | PIT_carry, t -> carry_ty (tr_prim_type t)
    | PIT_pair, (t1, t2) -> pair_ty (tr_prim_type t1) (tr_prim_type t2)
    | PIT_cmp, () -> compare_ty ()
    | PIT_f_cmp, () -> f_compare_ty ()
    | PIT_f_class, () -> f_class_ty () in
  let tr_type = function
    | PITT_ind (i, a) -> tr_ind i a
    | PITT_type t -> tr_prim_type t in
  let rec nary_op = function
    | [] -> assert false
    | [ret_ty] -> tr_type ret_ty
    | arg_ty :: r ->
       let arg_ty = tr_type arg_ty in
       Constr.mkProd(Context.nameR (Id.of_string "x"), arg_ty, nary_op r) in
  nary_op (types t)

let type_of_prim_or_type env = let open CPrimitives in
  function
  | OT_type t -> type_of_prim_type env t
  | OT_op op -> type_of_prim env op

let judge_of_int env i =
  make_judge (Constr.mkInt i) (type_of_int env)

let judge_of_float env f =
  make_judge (Constr.mkFloat f) (type_of_float env)

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

let type_of_inductive_knowing_parameters env (ind,u) args =
  let (mib,_mip) as spec = lookup_mind_specif env ind in
  let cstrnts = check_hyps_inclusion env (GlobRef.IndRef ind) mib.mind_hyps in
  let t,cst = Inductive.constrained_type_of_inductive_knowing_parameters
      (spec,u) (Inductive.make_param_univs env args)
  in
  check_constraints cst env;
  t, cstrnts

let type_of_inductive env (ind,u) =
  let (mib,mip) = lookup_mind_specif env ind in
  let cstrnts = check_hyps_inclusion env (GlobRef.IndRef ind) mib.mind_hyps in
  let t,cst = Inductive.constrained_type_of_inductive ((mib,mip),u) in
  check_constraints cst env;
  t, cstrnts

(* Constructors. *)

let type_of_constructor env ?ans (c,_u as cu) =
  let cstrnts =
    let ((kn,_),_) = c in
    let mib = lookup_mind kn env in
    check_hyps_inclusion env (GlobRef.ConstructRef c) mib.mind_hyps
  in
  let specif = lookup_mind_specif env (inductive_of_constructor c) in
  let t,cst = constrained_type_of_constructor ?ans cu specif in
  let () = check_constraints cst env in
  t, cstrnts

(* Case. *)

let check_branch_types env (ind,u) c ct lft explft =
  try conv_leq_vecti env lft explft
  with
      NotConvertibleVect i ->
        error_ill_formed_branch env c ((ind,i+1),u) lft.(i) explft.(i)
    | Invalid_argument _ ->
        error_number_branches env (make_judge c ct) (Array.length explft)

let type_of_case env stg ci p pt c ct _lf lft =
  let ((kn, i), _ as pind), largs, r =
    try find_rectype env ct
    with Not_found -> error_case_not_inductive env (make_judge c ct) in
  let _, sp = try dest_arity env pt
    with NotArity -> error_elim_arity env pind c (make_judge p pt) None in
  let rp = Sorts.relevance_of_sort sp in
  let ci = if ci.ci_relevance == rp then ci
    else (warn_bad_relevance_ci (); {ci with ci_relevance=rp})
  in
  let () = check_case_info env pind rp ci in
  let numvars = (lookup_mind kn env).mind_ntypes in
  let ans, stg = next_annots (Some numvars) stg in
  let s = List.nth (Option.get ans) i in (* indices need to correspond; see [Inductive.ind_subst] *)
  let bty, rslty, cstrnts_rsl =
    type_case_branches ?ans env (pind, largs) (make_judge p pt) c s in
  let cstrnts_branch = check_branch_types env pind c ct lft bty in
  let cstrnts = union cstrnts_rsl cstrnts_branch in
  stg, ci, rslty, add_constraint_from_ind env Variant cstrnts (fst pind) r (hat s)

let type_of_projection env p c ct =
  let pty = lookup_projection p env in
  let (ind,u), args, _ =
    try find_rectype env ct
    with Not_found -> error_case_not_inductive env (make_judge c ct)
  in
  assert(eq_ind (Projection.inductive p) ind);
  let ty = Vars.subst_instance_constr u pty in
  substl (c :: CList.rev args) ty


(* Fixpoints. *)

(* Gets the stage variables that must be set to the recursive stage and infinity, respectively *)
let get_vstar_vneq stg lar vdef =
  let lar_annots = List.map collect_annots (Array.to_list lar) in
  let vdef_annots = List.map collect_annots (Array.to_list vdef) in
  let all_annots = SVars.union_list (lar_annots @ vdef_annots) in
  let vstar = get_pos_vars stg in
  let vstars = List.map (inter vstar) lar_annots in
  let vneq = diff all_annots vstar in
  vstars, vneq

(* Letting lar'' := lar' with stage annotations at star positions shifted up,
  check Γ (names' : lar') ⊢ vdeft ≤ lar''. *)
let check_fixpoint env (names, lar', vdef, vdeft) lar'' =
  let env1 = push_rec_types (names, lar', vdef) env in (* vdef is ignored *)
  let lt = Array.length vdeft in
  assert (Int.equal (Array.length lar'') lt);
  try
    conv_leq_vecti env1 vdeft (Array.map (fun ty -> lift lt ty) lar'')
  with NotConvertibleVect i ->
    error_ill_typed_rec_body env1 i names (make_judgev vdef vdeft) lar''

(* Letting ΠΔ'.U' := lar', ΠΔ''.U'' := lar'',
  check Γ ⊢ Δ' ≤ Δ''; Γ ⊢ U' ≤ U'' for inductive, and
  check Γ ⊢ Δ'' ≤ Δ'; Γ ⊢ U'' ≤ U' for coinductive *)
let check_fixpoint_type env lar' lar'' recursivity =
  let unzip_prod_assums arr =
    let decls, body = List.split @@ Array.to_list @@
      Array.map Term.decompose_prod_assum arr in
    let tys = List.map Rel.Declaration.get_type @@ List.concat decls in
    Array.of_list tys, Array.of_list body in
  let delta', u' = unzip_prod_assums lar' in
  let delta'', u'' = unzip_prod_assums lar'' in
  let cstrnt_delta = match recursivity with
    | Finite -> conv_leq_vecti env delta' delta''
    | CoFinite -> conv_leq_vecti env delta'' delta'
    | _ -> assert false in
  let cstrnt_u = match recursivity with
    | Finite -> conv_leq_vecti env u' u''
    | CoFinite -> conv_leq_vecti env u'' u'
    | _ -> assert false in
  union cstrnt_delta cstrnt_u

(* Global references *)

let type_of_global_in_context env r =
  let open Names.GlobRef in
  match r with
  | VarRef id -> Environ.named_type id env, Univ.AUContext.empty
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
let rec execute env stg cstrnt cstr =
  let open Context.Rel.Declaration in
  match kind cstr with
    (* Atomic terms *)
    | Sort s ->
      (match s with
       | SProp -> if not (Environ.sprop_allowed env) then error_disallowed_sprop env
       | _ -> ());
      stg, cstrnt, cstr, type_of_sort s

    | Rel (n, _) ->
      let numvars = stage_vars_in_relative env n in
      let annots, stg = next_annots numvars stg in
      stg, cstrnt, mkRelA n annots, type_of_relative env n

    | Var (id, _) ->
      let numvars = stage_vars_in_variable env id in
      let s, stg = next stg in
      let t = annotate_glob s (type_of_variable env id) in
      let annots, stg = next_annots numvars stg in
      stg, cstrnt, mkVarA id annots, t

    | Const (c, _) ->
      let numvars = stage_vars_in_constant env c in
      let s, stg = next stg in
      let t, cstrnt' = type_of_constant env c in
      let t = annotate_glob s t in
      let annots, stg = next_annots numvars stg in
      stg, union cstrnt cstrnt', mkConstUA c annots, t

    | Proj (p, c) ->
      let stg, cstrnt, c', ct = execute env stg cstrnt c in
      let cstr = if c == c' then cstr else mkProj (p,c') in
      stg, cstrnt, cstr, type_of_projection env p c' ct

    (* Lambda calculus operators *)
    | App (f,args) ->
      let stga, cstrnta, args', argst = execute_array env stg cstrnt args in
      let stgf, cstrntf, f', ft = match kind f with
      | Ind (ind, s) when Environ.template_polymorphic_pind ind env ->
        let s', stg' = next ~s stga in
        let t, cstrntf = type_of_inductive_knowing_parameters env ind argst in
        stg', union cstrnta cstrntf, mkIndUS ind s', t
      | _ -> (* No template polymorphism *)
        execute env stga cstrnta f
      in
      let t, cstrntapp = type_of_apply env f' ft args' argst in
      let cstrnt = union cstrntf cstrntapp in
      let cstr = if f == f' && args == args' then cstr else mkApp (f',args') in
      stgf, cstrnt, cstr, t

    | Lambda (name,c1,c2) ->
      let stg1, cstrnt1, c1', s = execute_is_type env stg cstrnt c1 in
      let name' = check_binder_annot s name in
      let env1 = push_rel (LocalAssum (name',c1')) env in
      let stg2, cstrnt2, c2', c2t = execute env1 stg1 cstrnt1 c2 in
      let cstr = if name == name' && c1 == c1' && c2 == c2' then cstr else mkLambda(name', erase c1',c2') in
      stg2, cstrnt2, cstr, type_of_abstraction env name' c1' c2t

    | Prod (name,c1,c2) ->
      let stg1, cstrnt1, c1', vars = execute_is_type env stg cstrnt c1 in
      let name' = check_binder_annot vars name in
      let env1 = push_rel (LocalAssum (name',c1')) env in
      let stg2, cstrnt2, c2', vars' = execute_is_type env1 stg1 cstrnt1 c2 in
      let cstr = if name == name' && c1 == c1' && c2 == c2' then cstr else mkProd(name',c1',c2') in
      stg2, cstrnt2, cstr, type_of_product env name' vars vars'

    | LetIn (name,c1,c2,c3) ->
      let stg1, cstrnt1, c1', c1t = execute env stg cstrnt c1 in
      let stg2, cstrnt2, c2', c2s = execute_is_type env stg1 cstrnt1 c2 in
      let name' = check_binder_annot c2s name in
      let cstrnt' = check_cast env c1' c1t DEFAULTcast c2' in
      let env1 = push_rel (LocalDef (name',c1',c2')) env in
      let stg3, cstrnt3, c3', c3t = execute env1 stg2 (union cstrnt2 cstrnt') c3 in
      let cstr = if name == name' && c1 == c1' && c2 == c2' && c3 == c3' then cstr
        else mkLetIn(name',c1',erase c2',c3')
      in
      stg3, cstrnt3, cstr, subst1 c1 c3t

    | Cast (c,k,t) ->
      let stgc, cstrntc, c', ct = execute env stg cstrnt c in
      let stgt, cstrntt, t', _ts = execute_is_type env stgc cstrntc t in
      let cstrnt' = check_cast env c' ct k t' in
      let cstr = if c == c' && t == t' then cstr else mkCast(c',k,erase t') in
      stgt, union cstrntt cstrnt', cstr, t'

    (* Inductive types *)
    | Ind (ind, s) ->
      let s', stg' = next ~s stg in
      let t, cstrnt' = type_of_inductive env ind in
      stg', union cstrnt cstrnt', mkIndUS ind s', t

    | Construct (((kn, _), _), _ as c) ->
      let numvars = (lookup_mind kn env).mind_ntypes in
      let ans, stg = next_annots (Some numvars) stg in
      let t, cstrnt' = type_of_constructor env ?ans c in
      stg, union cstrnt cstrnt', cstr, t

    | Case (ci,p,c,lf) ->
      let stgc, cstrntc, c', ct = execute env stg cstrnt c in
      let stgp, cstrntp, p', pt = execute env stgc cstrntc p in
      let stglf, cstrntlf, lf', lft = execute_array env stgp cstrntp lf in
      let stg, ci', t, cstrntci = type_of_case env stglf ci p' pt c' ct lf' lft in
      let cstr = if ci == ci' && c == c' && p == p' && lf == lf' then cstr
        else mkCase (ci', erase p', c', lf')
      in
      stg, union cstrntlf cstrntci, cstr, t

    | Fix fix -> execute_fix env stg cstrnt fix

    | CoFix cofix -> execute_cofix env stg cstrnt cofix

    (* Primitive types *)
    | Int _ -> stg, empty (), cstr, type_of_int env
    | Float _ -> stg, empty (), cstr, type_of_float env

    (* Partial proofs: unsupported by the kernel *)
    | Meta _ ->
        anomaly (Pp.str "the kernel does not support metavariables.")

    | Evar _ ->
        anomaly (Pp.str "the kernel does not support existential variables.")

and execute_is_type env stg cstrnt constr =
  let stg, cstrnt, c, t = execute env stg cstrnt constr in
    stg, cstrnt, c, check_type env constr t

(* Usual inference: Γ ⊢ lar' : lart; Γ (names' : lar') ⊢ vdef : vdeft *)
and execute_recdef env stg cstrnt (names, lar, vdef) =
  let stg_lar, cstrnt_lar, lar', lart = execute_array env stg cstrnt lar in
  let names' = Array.Smart.map_i (fun i na -> check_assumption env na lar'.(i) lart.(i)) names in
  let env1 = push_rec_types (names', lar', vdef) env in (* vdef is ignored *)
  let stg_vdef, cstrnt_vdef, vdef', vdeft = execute_array env1 stg_lar cstrnt_lar vdef in
  stg_vdef, cstrnt_vdef, (names', lar', vdef', vdeft)

(* Try RecCheck; if failure, try removing some stage variables from vstar *)
and execute_rec_check env stg cstrnt cstr (_, lar', _, _ as recdeft) vars recursivity =
  let rec try_rec_check stg (alphas, vstars, vneq) =
    let vstar = SVars.union_list vstars in
    let lar'' = Array.map (annotate_succ vstar) lar' in
    let cstrnt_fix = check_fixpoint env recdeft lar'' in
    let cstrnt_fix_ty = check_fixpoint_type env lar' lar'' recursivity in
    let cstrnt' = union_list [cstrnt; cstrnt_fix; cstrnt_fix_ty] in

    let rec_check_all cstrnts (alpha, vstar) = union cstrnts (rec_check alpha vstar vneq cstrnts) in
    let flags = Environ.typing_flags env in
    if flags.check_sized then
      try stg, List.fold_left rec_check_all cstrnt' (List.combine alphas vstars)
      with RecCheckFailed (cstrnt'', si_inf, si) ->
        let rm = inter (inter si_inf si) (diff vstar (SVars.of_list alphas)) in
        if is_empty rm then begin
          if flags.check_guarded then stg, cstrnt else
            error_unsatisfied_stage_constraints env cstrnt'' cstr si_inf si
        end else
          let vstars = List.map (fun vstar -> diff vstar rm) vstars in
          let vneq = SVars.union vneq rm in
          let stg = remove_pos_vars rm stg in
          try_rec_check stg (alphas, vstars, vneq)
    else stg, cstrnt' in
  try_rec_check stg vars

and execute_fix env stg cstrnt ((vn, i), (names, lar, vdef)) =
  let stg = State.push stg in
  let _ = execute_array env stg cstrnt lar in (* check termination of lar so we can reduce *)

  let stg', cstrnt', (names', lar', vdef', _ as recdeft) =
    let lar_star = set_stars env (get_rec_inds env vn lar) lar in
    execute_recdef env stg cstrnt (names, lar_star, vdef) in

  let stg_check, cstrnt_check =
    let alphas = get_rec_vars env vn lar' in
    let vstars, vneq = get_vstar_vneq stg' lar' vdef' in
    let cstr = mkFix ((vn, i), (names', lar', vdef')) in
    execute_rec_check env stg' cstrnt' cstr recdeft (alphas, vstars, vneq) Finite in

  let fix =
    let lar_star = Array.Smart.map (erase_star (get_pos_vars stg_check)) lar' in
    ((vn, i), (names', lar_star, vdef')) in

  check_fix env fix; State.pop stg_check, cstrnt_check, mkFix fix, lar'.(i)

and execute_cofix env stg cstrnt (i, (names, lar, vdef)) =
  let stg = State.push stg in
  let _ = execute_array env stg cstrnt lar in (* check termination of lar so we can reduce *)

  let stg', cstrnt', (names', lar', vdef', _ as recdeft) =
    let lar_star = set_stars env (get_corec_inds env lar) lar in
    execute_recdef env stg cstrnt (names, lar_star, vdef) in

  let stg_check, cstrnt_check =
    let alphas = get_corec_vars env lar' in
    let vstars, vneq = get_vstar_vneq stg' lar' vdef' in
    let cstr = mkCoFix (i, (names', lar', vdef')) in
    execute_rec_check env stg' cstrnt' cstr recdeft (alphas, vstars, vneq) CoFinite in

  let cofix =
    let lar_star = Array.Smart.map (erase_star (get_pos_vars stg_check)) lar' in
    (i, (names', lar_star, vdef')) in

  check_cofix env cofix; State.pop stg_check, cstrnt_check, mkCoFix cofix, lar'.(i)

and execute_array env stg cstrnt cs =
  let tys = Array.make (Array.length cs) mkProp in
  let ((stg, cstrnt), cs) = Array.Smart.fold_left_map_i
    (fun i (stg, cstrnt1) c ->
      let stg', cstrnt2, c, ty = execute env stg cstrnt c in
      tys.(i) <- ty;
      (stg', union cstrnt1 cstrnt2), c)
    (stg, empty ()) cs in
  stg, cstrnt, cs, tys

(* Derived functions *)

let check_wellformed_universes env c =
  let univs = universes_of_constr c in
  try UGraph.check_declared_universes (universes env) univs
  with UGraph.UndeclaredLevel u ->
    error_undeclared_universe env u

let infer env constr =
  let () = check_wellformed_universes env constr in
  let stg, _, constr_sized, t_sized = execute env State.init (empty ()) constr in
  let constr = erase_infty constr_sized in
  let t = erase_glob (get_pos_vars stg) t_sized in
  make_judge constr t

let infer =
  if Flags.profile then
    let infer_key = CProfile.declare_profile "Fast_infer" in
      CProfile.profile2 infer_key (fun b c -> infer b c)
  else (fun b c -> infer b c)

let infer_fix env fix =
  (** NB: This doesn't work. The Rel context might have Evar and Meta.
  let open Rel.Declaration in
  let infer_rel _ rd (env, stg, cstrnt) =
    match rd with
    | LocalAssum (na, ty) ->
      let stg, cstrnt, ty, _ = execute env stg cstrnt ty in
      push_rel (LocalAssum (na, ty)) env, stg, cstrnt
    | LocalDef (na, c, _) ->
      let stg, cstrnt, c, ty = execute env stg cstrnt c in
      push_rel (LocalDef (na, c, ty)) env, stg, cstrnt
    in
  let env' = reset_with_named_context (named_context_val env) env in
  let env, stg, cstrnt = fold_rel_context infer_rel env ~init:(env', State.init, empty ()) in
  ignore @@ execute_fix env stg cstrnt fix
  **)
  ignore @@ execute_fix env State.init (empty ()) fix

let assumption_of_judgment env {uj_val=c; uj_type=t} =
  infer_assumption env c t

let type_judgment env {uj_val=c; uj_type=t} =
  let s = check_type env c t in
  {utj_val = c; utj_type = s }

let infer_type env constr =
  let () = check_wellformed_universes env constr in
  let stg, _, constr_sized, t = execute env State.init (empty ()) constr in
  let constr = erase_glob (get_pos_vars stg) constr_sized in
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
        let _ = conv_leq false env j1.uj_type ty in
        let x = check_binder_annot jty.utj_type x in
        push_rel d env, LocalDef (x,j1.uj_val,jty.utj_val) :: rels)
    rels ~init:(env,[])

let judge_of_prop = make_judge mkProp type1
let judge_of_set = make_judge mkSet type1
let judge_of_type u = make_judge (mkType u) (type_of_type u)

let judge_of_relative env k = make_judge (mkRel k) (type_of_relative env k)

let judge_of_variable env x = make_judge (mkVar x) (type_of_variable env x)

let judge_of_constant env cst =
  let t, _ = type_of_constant env cst in
  make_judge (mkConstU cst) t

let judge_of_projection env p cj =
  make_judge (mkProj (p,cj.uj_val)) (type_of_projection env p cj.uj_val cj.uj_type)

let dest_judgev v =
  Array.map j_val v, Array.map j_type v

let judge_of_apply env funj argjv =
  let args, argtys = dest_judgev argjv in
  let t, _ = type_of_apply env funj.uj_val funj.uj_type args argtys in
  make_judge (mkApp (funj.uj_val, args)) t

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
  let _ = check_cast env cj.uj_val cj.uj_type k tj.utj_val in
  let c = match k with | REVERTcast -> cj.uj_val | _ -> mkCast (cj.uj_val, k, tj.utj_val) in
  make_judge c tj.utj_val

let judge_of_inductive env indu =
  let t, _ = type_of_inductive env indu in
  make_judge (mkIndU indu) t

let judge_of_constructor env cu =
  let t, _ = type_of_constructor env cu in
  make_judge (mkConstructU cu) t

let judge_of_case env ci pj cj lfj =
  let lf, lft = dest_judgev lfj in
  let _, ci, t, _ = type_of_case env init ci pj.uj_val pj.uj_type cj.uj_val cj.uj_type lf lft in
  make_judge (mkCase (ci, (*nf_betaiota*) pj.uj_val, cj.uj_val, lft)) t

(* Building type of primitive operators and type *)

let check_primitive_type env op_t t =
  let inft = type_of_prim_or_type env op_t in
  try default_conv ~l2r:false CUMUL env inft t
  with NotConvertible -> error_incorrect_primitive env (make_judge op_t inft) t
