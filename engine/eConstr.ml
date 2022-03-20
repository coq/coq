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
open Constr
open Context

module ESorts = struct
  include Evd.MiniEConstr.ESorts

  let equal sigma s1 s2 =
    Sorts.equal (kind sigma s1) (kind sigma s2)
end

module EInstance = struct
  include Evd.MiniEConstr.EInstance

  let equal sigma i1 i2 =
    Univ.Instance.equal (kind sigma i1) (kind sigma i2)
end

include (Evd.MiniEConstr : module type of Evd.MiniEConstr
         with module ESorts := ESorts
          and module EInstance := EInstance)

type types = t
type constr = t
type existential = t pexistential
type case_return = t pcase_return
type case_branch = t pcase_branch
type case_invert = t pcase_invert
type case = (t, t, EInstance.t) pcase
type fixpoint = (t, t) pfixpoint
type cofixpoint = (t, t) pcofixpoint
type unsafe_judgment = (constr, types) Environ.punsafe_judgment
type unsafe_type_judgment = types Environ.punsafe_type_judgment
type named_declaration = (constr, types) Context.Named.Declaration.pt
type rel_declaration = (constr, types) Context.Rel.Declaration.pt
type named_context = (constr, types) Context.Named.pt
type rel_context = (constr, types) Context.Rel.pt

type 'a puniverses = 'a * EInstance.t

let in_punivs a = (a, EInstance.empty)

let mkSProp = of_kind (Sort (ESorts.make Sorts.sprop))
let mkProp = of_kind (Sort (ESorts.make Sorts.prop))
let mkSet = of_kind (Sort (ESorts.make Sorts.set))
let mkType u = of_kind (Sort (ESorts.make (Sorts.sort_of_univ u)))
let mkRel n = of_kind (Rel n)
let mkVar id = of_kind (Var id)
let mkMeta n = of_kind (Meta n)
let mkEvar e = of_kind (Evar e)
let mkSort s = of_kind (Sort (ESorts.make s))
let mkCast (b, k, t) = of_kind (Cast (b, k, t))
let mkProd (na, t, u) = of_kind (Prod (na, t, u))
let mkLambda (na, t, c) = of_kind (Lambda (na, t, c))
let mkLetIn (na, b, t, c) = of_kind (LetIn (na, b, t, c))
let mkApp (f, arg) = of_kind (App (f, arg))
let mkConstU pc = of_kind (Const pc)
let mkConst c = of_kind (Const (in_punivs c))
let mkIndU pi = of_kind (Ind pi)
let mkInd i = of_kind (Ind (in_punivs i))
let mkConstructU pc = of_kind (Construct pc)
let mkConstruct c = of_kind (Construct (in_punivs c))
let mkConstructUi ((ind,u),i) = of_kind (Construct ((ind,i),u))
let mkCase (ci, u, pms, c, iv, r, p) = of_kind (Case (ci, u, pms, c, iv, r, p))
let mkFix f = of_kind (Fix f)
let mkCoFix f = of_kind (CoFix f)
let mkProj (p, c) = of_kind (Proj (p, c))
let mkArrow t1 r t2 = of_kind (Prod (make_annot Anonymous r, t1, t2))
let mkArrowR t1 t2 = mkArrow t1 Sorts.Relevant t2
let mkInt i = of_kind (Int i)
let mkFloat f = of_kind (Float f)
let mkArray (u,t,def,ty) = of_kind (Array (u,t,def,ty))

let mkRef (gr,u) = let open GlobRef in match gr with
  | ConstRef c -> mkConstU (c,u)
  | IndRef ind -> mkIndU (ind,u)
  | ConstructRef c -> mkConstructU (c,u)
  | VarRef x -> mkVar x

let type1 = mkSort Sorts.type1

let applist (f, arg) = mkApp (f, Array.of_list arg)
let applistc f arg = mkApp (f, Array.of_list arg)

let isRel sigma c = match kind sigma c with Rel _ -> true | _ -> false
let isVar sigma c = match kind sigma c with Var _ -> true | _ -> false
let isInd sigma c = match kind sigma c with Ind _ -> true | _ -> false
let isEvar sigma c = match kind sigma c with Evar _ -> true | _ -> false
let isMeta sigma c = match kind sigma c with Meta _ -> true | _ -> false
let isSort sigma c = match kind sigma c with Sort _ -> true | _ -> false
let isCast sigma c = match kind sigma c with Cast _ -> true | _ -> false
let isApp sigma c = match kind sigma c with App _ -> true | _ -> false
let isLambda sigma c = match kind sigma c with Lambda _ -> true | _ -> false
let isLetIn sigma c = match kind sigma c with LetIn _ -> true | _ -> false
let isProd sigma c = match kind sigma c with Prod _ -> true | _ -> false
let isConst sigma c = match kind sigma c with Const _ -> true | _ -> false
let isConstruct sigma c = match kind sigma c with Construct _ -> true | _ -> false
let isFix sigma c = match kind sigma c with Fix _ -> true | _ -> false
let isCoFix sigma c = match kind sigma c with CoFix _ -> true | _ -> false
let isCase sigma c = match kind sigma c with Case _ -> true | _ -> false
let isProj sigma c = match kind sigma c with Proj _ -> true | _ -> false

let rec isType sigma c = match kind sigma c with
  | Sort s -> (match ESorts.kind sigma s with
      | Sorts.Type _ -> true
      | _ -> false )
  | Cast (c,_,_) -> isType sigma c
  | _ -> false

let isVarId sigma id c =
  match kind sigma c with Var id' -> Id.equal id id' | _ -> false
let isRelN sigma n c =
  match kind sigma c with Rel n' -> Int.equal n n' | _ -> false

let isRef sigma c = match kind sigma c with
  | Const _ | Ind _ | Construct _ | Var _ -> true
  | _ -> false

let isRefX sigma x c =
  let open GlobRef in
  match x, kind sigma c with
  | ConstRef c, Const (c', _) -> Constant.CanOrd.equal c c'
  | IndRef i, Ind (i', _) -> Ind.CanOrd.equal i i'
  | ConstructRef i, Construct (i', _) -> Construct.CanOrd.equal i i'
  | VarRef id, Var id' -> Id.equal id id'
  | _ -> false


let destRel sigma c = match kind sigma c with
| Rel p -> p
| _ -> raise DestKO

let destVar sigma c = match kind sigma c with
| Var p -> p
| _ -> raise DestKO

let destInd sigma c = match kind sigma c with
| Ind p -> p
| _ -> raise DestKO

let destEvar sigma c = match kind sigma c with
| Evar p -> p
| _ -> raise DestKO

let destMeta sigma c = match kind sigma c with
| Meta p -> p
| _ -> raise DestKO

let destSort sigma c = match kind sigma c with
| Sort p -> p
| _ -> raise DestKO

let destCast sigma c = match kind sigma c with
| Cast (c, k, t) -> (c, k, t)
| _ -> raise DestKO

let destApp sigma c = match kind sigma c with
| App (f, a) -> (f, a)
| _ -> raise DestKO

let destLambda sigma c = match kind sigma c with
| Lambda (na, t, c) -> (na, t, c)
| _ -> raise DestKO

let destLetIn sigma c = match kind sigma c with
| LetIn (na, b, t, c) -> (na, b, t, c)
| _ -> raise DestKO

let destProd sigma c = match kind sigma c with
| Prod (na, t, c) -> (na, t, c)
| _ -> raise DestKO

let destConst sigma c = match kind sigma c with
| Const p -> p
| _ -> raise DestKO

let destConstruct sigma c = match kind sigma c with
| Construct p -> p
| _ -> raise DestKO

let destFix sigma c = match kind sigma c with
| Fix p -> p
| _ -> raise DestKO

let destCoFix sigma c = match kind sigma c with
| CoFix p -> p
| _ -> raise DestKO

let destCase sigma c = match kind sigma c with
| Case (ci, u, pms, t, iv, c, p) -> (ci, u, pms, t, iv, c, p)
| _ -> raise DestKO

let destProj sigma c = match kind sigma c with
| Proj (p, c) -> (p, c)
| _ -> raise DestKO

let destRef sigma c = let open GlobRef in match kind sigma c with
  | Var x -> VarRef x, EInstance.empty
  | Const (c,u) -> ConstRef c, u
  | Ind (ind,u) -> IndRef ind, u
  | Construct (c,u) -> ConstructRef c, u
  | _ -> raise DestKO

let decompose_app sigma c =
  match kind sigma c with
    | App (f,cl) -> (f, Array.to_list cl)
    | _ -> (c,[])

let decompose_lam sigma c =
  let rec lamdec_rec l c = match kind sigma c with
    | Lambda (x,t,c) -> lamdec_rec ((x,t)::l) c
    | Cast (c,_,_)     -> lamdec_rec l c
    | _                -> l,c
  in
  lamdec_rec [] c

let decompose_lam_assum sigma c =
  let open Rel.Declaration in
  let rec lamdec_rec l c =
    match kind sigma c with
    | Lambda (x,t,c)  -> lamdec_rec (Context.Rel.add (LocalAssum (x,t)) l) c
    | LetIn (x,b,t,c) -> lamdec_rec (Context.Rel.add (LocalDef (x,b,t)) l) c
    | Cast (c,_,_)    -> lamdec_rec l c
    | _               -> l,c
  in
  lamdec_rec Context.Rel.empty c

let decompose_lam_n_assum sigma n c =
  let open Rel.Declaration in
  if n < 0 then
    anomaly Pp.(str "decompose_lam_n_assum: integer parameter must be positive.");
  let rec lamdec_rec l n c =
    if Int.equal n 0 then l,c
    else
      match kind sigma c with
      | Lambda (x,t,c)  -> lamdec_rec (Context.Rel.add (LocalAssum (x,t)) l) (n-1) c
      | LetIn (x,b,t,c) -> lamdec_rec (Context.Rel.add (LocalDef (x,b,t)) l) n c
      | Cast (c,_,_)    -> lamdec_rec l n c
      | c -> anomaly Pp.(str "decompose_lam_n_assum: not enough abstractions.")
  in
  lamdec_rec Context.Rel.empty n c

let decompose_lam_n_decls sigma n =
  let open Rel.Declaration in
  if n < 0 then
    anomaly Pp.(str "decompose_lam_n_decls: integer parameter must be positive.");
  let rec lamdec_rec l n c =
    if Int.equal n 0 then l,c
    else
      match kind sigma c with
      | Lambda (x,t,c)  -> lamdec_rec (Context.Rel.add (LocalAssum (x,t)) l) (n-1) c
      | LetIn (x,b,t,c) -> lamdec_rec (Context.Rel.add (LocalDef (x,b,t)) l) (n-1) c
      | Cast (c,_,_)    -> lamdec_rec l n c
      | c -> anomaly Pp.(str "decompose_lam_n_decls: not enough abstractions.")
  in
  lamdec_rec Context.Rel.empty n

let lamn n env b =
  let rec lamrec = function
    | (0, env, b)        -> b
    | (n, ((v,t)::l), b) -> lamrec (n-1,  l, mkLambda (v,t,b))
    | _ -> assert false
  in
  lamrec (n,env,b)

let compose_lam l b = lamn (List.length l) l b

let rec to_lambda sigma n prod =
  if Int.equal n 0 then
    prod
  else
    match kind sigma prod with
      | Prod (na,ty,bd) -> mkLambda (na,ty,to_lambda sigma (n-1) bd)
      | Cast (c,_,_) -> to_lambda sigma n c
      | _   -> anomaly Pp.(str "Not enough products.")

let decompose_prod sigma c =
  let rec proddec_rec l c = match kind sigma c with
    | Prod (x,t,c) -> proddec_rec ((x,t)::l) c
    | Cast (c,_,_) -> proddec_rec l c
    | _            -> l,c
  in
  proddec_rec [] c

let decompose_prod_assum sigma c =
  let open Rel.Declaration in
  let rec proddec_rec l c =
    match kind sigma c with
    | Prod (x,t,c)    -> proddec_rec (Context.Rel.add (LocalAssum (x,t)) l) c
    | LetIn (x,b,t,c) -> proddec_rec (Context.Rel.add (LocalDef (x,b,t)) l) c
    | Cast (c,_,_)    -> proddec_rec l c
    | _               -> l,c
  in
  proddec_rec Context.Rel.empty c

let decompose_prod_n_assum sigma n c =
  let open Rel.Declaration in
  if n < 0 then
    anomaly Pp.(str "decompose_prod_n_assum: integer parameter must be positive.");
  let rec prodec_rec l n c =
    if Int.equal n 0 then l,c
    else
      match kind sigma c with
      | Prod (x,t,c)    -> prodec_rec (Context.Rel.add (LocalAssum (x,t)) l) (n-1) c
      | LetIn (x,b,t,c) -> prodec_rec (Context.Rel.add (LocalDef (x,b,t)) l) (n-1) c
      | Cast (c,_,_)    -> prodec_rec l n c
      | c -> anomaly Pp.(str "decompose_prod_n_assum: not enough declarations.")
  in
  prodec_rec Context.Rel.empty n c

let existential_type = Evd.existential_type

let lift n c = of_constr (Vars.lift n (unsafe_to_constr c))

let of_branches : Constr.case_branch array -> case_branch array =
  match Evd.MiniEConstr.unsafe_eq with
  | Refl -> fun x -> x

let unsafe_to_branches : case_branch array -> Constr.case_branch array =
  match Evd.MiniEConstr.unsafe_eq with
  | Refl -> fun x -> x

let of_return : Constr.case_return -> case_return =
  match Evd.MiniEConstr.unsafe_eq with
  | Refl -> fun x -> x

let unsafe_to_return : case_return -> Constr.case_return =
  match Evd.MiniEConstr.unsafe_eq with
  | Refl -> fun x -> x

let map_branches f br =
  let f c = unsafe_to_constr (f (of_constr c)) in
  of_branches (Constr.map_branches f (unsafe_to_branches br))
let map_return_predicate f p =
  let f c = unsafe_to_constr (f (of_constr c)) in
  of_return (Constr.map_return_predicate f (unsafe_to_return p))

let map sigma f c =
  let f c = unsafe_to_constr (f (of_constr c)) in
  of_constr (Constr.map f (unsafe_to_constr (whd_evar sigma c)))

let map_with_binders sigma g f l c =
  let f l c = unsafe_to_constr (f l (of_constr c)) in
  of_constr (Constr.map_with_binders g f l (unsafe_to_constr (whd_evar sigma c)))

let iter sigma f c =
  let f c = f (of_constr c) in
  Constr.iter f (unsafe_to_constr (whd_evar sigma c))

let expand_case env _sigma (ci, u, pms, p, iv, c, bl) =
  let u = EInstance.unsafe_to_instance u in
  let pms = unsafe_to_constr_array pms in
  let p = unsafe_to_return p in
  let iv = unsafe_to_case_invert iv in
  let c = unsafe_to_constr c in
  let bl = unsafe_to_branches bl in
  let (ci, p, iv, c, bl) = Inductive.expand_case env (ci, u, pms, p, iv, c, bl) in
  let p = of_constr p in
  let c = of_constr c in
  let iv = of_case_invert iv in
  let bl = of_constr_array bl in
  (ci, p, iv, c, bl)

let annotate_case env sigma (ci, u, pms, p, iv, c, bl as case) =
  let (_, p, _, _, bl) = expand_case env sigma case in
  let p =
    (* Too bad we need to fetch this data in the environment, should be in the
      case_info instead. *)
    let (_, mip) = Inductive.lookup_mind_specif env ci.ci_ind in
    decompose_lam_n_decls sigma (mip.Declarations.mind_nrealdecls + 1) p
  in
  let mk_br c n = decompose_lam_n_decls sigma n c in
  let bl = Array.map2 mk_br bl ci.ci_cstr_ndecls in
  (ci, u, pms, p, iv, c, bl)

let expand_branch env _sigma u pms (ind, i) (nas, _br) =
  let open Declarations in
  let u = EInstance.unsafe_to_instance u in
  let pms = unsafe_to_constr_array pms in
  let (mib, mip) = Inductive.lookup_mind_specif env ind in
  let paramdecl = Vars.subst_instance_context u mib.mind_params_ctxt in
  let paramsubst = Vars.subst_of_rel_context_instance paramdecl pms in
  let (ctx, _) = mip.mind_nf_lc.(i - 1) in
  let (ctx, _) = List.chop mip.mind_consnrealdecls.(i - 1) ctx in
  let ans = Inductive.instantiate_context u paramsubst nas ctx in
  let ans : rel_context = match Evd.MiniEConstr.unsafe_eq with Refl -> ans in
  ans

let contract_case env _sigma (ci, p, iv, c, bl) =
  let p = unsafe_to_constr p in
  let iv = unsafe_to_case_invert iv in
  let c = unsafe_to_constr c in
  let bl = unsafe_to_constr_array bl in
  let (ci, u, pms, p, iv, c, bl) = Inductive.contract_case env (ci, p, iv, c, bl) in
  let u = EInstance.make u in
  let pms = of_constr_array pms in
  let p = of_return p in
  let iv = of_case_invert iv in
  let c = of_constr c in
  let bl = of_branches bl in
  (ci, u, pms, p, iv, c, bl)

let iter_with_full_binders env sigma g f n c =
  let open Context.Rel.Declaration in
  match kind sigma c with
  | (Rel _ | Meta _ | Var _   | Sort _ | Const _ | Ind _
    | Construct _ | Int _ | Float _) -> ()
  | Cast (c,_,t) -> f n c; f n t
  | Prod (na,t,c) -> f n t; f (g (LocalAssum (na, t)) n) c
  | Lambda (na,t,c) -> f n t; f (g (LocalAssum (na, t)) n) c
  | LetIn (na,b,t,c) -> f n b; f n t; f (g (LocalDef (na, b, t)) n) c
  | App (c,l) -> f n c; Array.Fun1.iter f n l
  | Evar (_,l) -> List.iter (fun c -> f n c) l
  | Case (ci,u,pms,p,iv,c,bl) ->
    let (ci, _, pms, p, iv, c, bl) = annotate_case env sigma (ci, u, pms, p, iv, c, bl) in
    let f_ctx (ctx, c) = f (List.fold_right g ctx n) c in
    Array.Fun1.iter f n pms; f_ctx p; iter_invert (f n) iv; f n c; Array.iter f_ctx bl
  | Proj (p,c) -> f n c
  | Fix (_,(lna,tl,bl)) ->
    Array.iter (f n) tl;
    let n' = Array.fold_left2_i (fun i n na t -> g (LocalAssum (na, lift i t)) n) n lna tl in
    Array.iter (f n') bl
  | CoFix (_,(lna,tl,bl)) ->
    Array.iter (f n) tl;
    let n' = Array.fold_left2_i (fun i n na t -> g (LocalAssum (na,lift i t)) n) n lna tl in
    Array.iter (f n') bl
  | Array (_u,t,def,ty) -> Array.Fun1.iter f n t; f n def; f n ty

let iter_with_binders sigma g f n c =
  let f l c = f l (of_constr c) in
  Constr.iter_with_binders g f n (unsafe_to_constr (whd_evar sigma c))

let fold sigma f acc c =
  let f acc c = f acc (of_constr c) in
  Constr.fold f acc (unsafe_to_constr (whd_evar sigma c))

let fold_with_binders sigma g f acc e c =
  let f e acc c = f e acc (of_constr c) in
  Constr.fold_constr_with_binders g f acc e (unsafe_to_constr (whd_evar sigma c))

let compare_gen k eq_inst eq_sort eq_constr nargs c1 c2 =
  (c1 == c2) || Constr.compare_head_gen_with k k eq_inst eq_sort eq_constr nargs c1 c2

let eq_constr sigma c1 c2 =
  let kind c = kind sigma c in
  let eq_inst _ i1 i2 = EInstance.equal sigma i1 i2 in
  let eq_sorts s1 s2 = ESorts.equal sigma s1 s2 in
  let rec eq_constr nargs c1 c2 =
    compare_gen kind eq_inst eq_sorts eq_constr nargs c1 c2
  in
  eq_constr 0 c1 c2

let eq_constr_nounivs sigma c1 c2 =
  let kind c = kind sigma c in
  let rec eq_constr nargs c1 c2 =
    compare_gen kind (fun _ _ _ -> true) (fun _ _ -> true) eq_constr nargs c1 c2
  in
  eq_constr 0 c1 c2

let compare_constr sigma cmp c1 c2 =
  let kind c = kind sigma c in
  let eq_inst _ i1 i2 = EInstance.equal sigma i1 i2 in
  let eq_sorts s1 s2 = ESorts.equal sigma s1 s2 in
  let cmp nargs c1 c2 = cmp c1 c2 in
  compare_gen kind eq_inst eq_sorts cmp 0 c1 c2

let compare_cumulative_instances cv_pb nargs_ok variances u u' cstrs =
  let open UnivProblem in
  if not nargs_ok then enforce_eq_instances_univs false u u' cstrs
  else
    let make u = Sorts.sort_of_univ @@ Univ.Universe.make u in
    CArray.fold_left3
      (fun cstrs v u u' ->
         let open Univ.Variance in
         match v with
         | Irrelevant -> Set.add (UWeak (u,u')) cstrs
         | Covariant ->
           (match cv_pb with
            | Reduction.CONV -> Set.add (UEq (make u, make u')) cstrs
            | Reduction.CUMUL -> Set.add (ULe (make u, make u')) cstrs)
         | Invariant ->
           Set.add (UEq (make u, make u')) cstrs)
      cstrs variances (Univ.Instance.to_array u) (Univ.Instance.to_array u')

let cmp_inductives cv_pb (mind,ind as spec) nargs u1 u2 cstrs =
  let open UnivProblem in
  match mind.Declarations.mind_variance with
  | None -> enforce_eq_instances_univs false u1 u2 cstrs
  | Some variances ->
    let num_param_arity = Reduction.inductive_cumulativity_arguments spec in
    compare_cumulative_instances cv_pb (Int.equal num_param_arity nargs) variances u1 u2 cstrs

let cmp_constructors (mind, ind, cns as spec) nargs u1 u2 cstrs =
  let open UnivProblem in
  match mind.Declarations.mind_variance with
  | None -> enforce_eq_instances_univs false u1 u2 cstrs
  | Some _ ->
    let num_cnstr_args = Reduction.constructor_cumulativity_arguments spec in
    if not (Int.equal num_cnstr_args nargs)
    then enforce_eq_instances_univs false u1 u2 cstrs
    else
      Array.fold_left2 (fun cstrs u1 u2 -> UnivProblem.(Set.add (UWeak (u1,u2)) cstrs))
        cstrs (Univ.Instance.to_array u1) (Univ.Instance.to_array u2)

let eq_universes env sigma cstrs cv_pb refargs l l' =
  if EInstance.is_empty l then (assert (EInstance.is_empty l'); true)
  else
    let l = EInstance.kind sigma l
    and l' = EInstance.kind sigma l' in
    let open GlobRef in
    let open UnivProblem in
    match refargs with
    | Some (ConstRef c, 1) when Environ.is_array_type env c ->
      cstrs := compare_cumulative_instances cv_pb true [|Univ.Variance.Irrelevant|] l l' !cstrs;
      true
    | None | Some (ConstRef _, _) ->
      cstrs := enforce_eq_instances_univs true l l' !cstrs; true
    | Some (VarRef _, _) -> assert false (* variables don't have instances *)
    | Some (IndRef ind, nargs) ->
      let mind = Environ.lookup_mind (fst ind) env in
      cstrs := cmp_inductives cv_pb (mind,snd ind) nargs l l' !cstrs;
      true
    | Some (ConstructRef ((mi,ind),ctor), nargs) ->
      let mind = Environ.lookup_mind mi env in
      cstrs := cmp_constructors (mind,ind,ctor) nargs l l' !cstrs;
      true

let test_constr_universes env sigma leq ?(nargs=0) m n =
  let open UnivProblem in
  let kind c = kind sigma c in
  if m == n then Some Set.empty
  else
    let cstrs = ref Set.empty in
    let cv_pb = if leq then Reduction.CUMUL else Reduction.CONV in
    let eq_universes refargs l l' = eq_universes env sigma cstrs Reduction.CONV refargs l l'
    and leq_universes refargs l l' = eq_universes env sigma cstrs cv_pb refargs l l' in
    let eq_sorts s1 s2 =
      let s1 = ESorts.kind sigma s1 in
      let s2 = ESorts.kind sigma s2 in
      if Sorts.equal s1 s2 then true
      else (cstrs := Set.add
              (UEq (s1, s2)) !cstrs;
            true)
    in
    let leq_sorts s1 s2 =
      let s1 = ESorts.kind sigma s1 in
      let s2 = ESorts.kind sigma s2 in
      if Sorts.equal s1 s2 then true
      else
        (cstrs := Set.add
           (ULe (s1, s2)) !cstrs;
         true)
    in
    let rec eq_constr' nargs m n = compare_gen kind eq_universes eq_sorts eq_constr' nargs m n in
    let res =
      if leq then
        let rec compare_leq nargs m n =
          Constr.compare_head_gen_leq_with kind kind leq_universes leq_sorts
            eq_constr' leq_constr' nargs m n
        and leq_constr' nargs m n = m == n || compare_leq nargs m n in
        compare_leq nargs m n
      else
        Constr.compare_head_gen_with kind kind eq_universes eq_sorts eq_constr' nargs m n
    in
    if res then Some !cstrs else None

let eq_constr_universes env sigma ?nargs m n =
  test_constr_universes env sigma false ?nargs m n
let leq_constr_universes env sigma ?nargs m n =
  test_constr_universes env sigma true ?nargs m n

let compare_head_gen_proj env sigma equ eqs eqc' nargs m n =
  let kind c = kind sigma c in
  match kind m, kind n with
  | Proj (p, c), App (f, args)
  | App (f, args), Proj (p, c) ->
      (match kind f with
      | Const (p', u) when Environ.QConstant.equal env (Projection.constant p) p' ->
          let npars = Projection.npars p in
          if Array.length args == npars + 1 then
            eqc' 0 c args.(npars)
          else false
      | _ -> false)
  | _ -> Constr.compare_head_gen_with kind kind equ eqs eqc' nargs m n

let eq_constr_universes_proj env sigma m n =
  let open UnivProblem in
  if m == n then Some Set.empty
  else
    let cstrs = ref Set.empty in
    let eq_universes ref l l' = eq_universes env sigma cstrs Reduction.CONV ref l l' in
    let eq_sorts s1 s2 =
      let s1 = ESorts.kind sigma s1 in
      let s2 = ESorts.kind sigma s2 in
      if Sorts.equal s1 s2 then true
      else
        (cstrs := Set.add
           (UEq (s1, s2)) !cstrs;
         true)
    in
    let rec eq_constr' nargs m n =
      m == n || compare_head_gen_proj env sigma eq_universes eq_sorts eq_constr' nargs m n
    in
    let res = eq_constr' 0 m n in
    if res then Some !cstrs else None

let universes_of_constr sigma c =
  let open Univ in
  let rec aux s c =
    match kind sigma c with
    | Const (c, u) ->
      Level.Set.fold Level.Set.add (Instance.levels (EInstance.kind sigma u)) s
    | Ind ((mind,_), u) | Construct (((mind,_),_), u) ->
      Level.Set.fold Level.Set.add (Instance.levels (EInstance.kind sigma u)) s
    | Sort u ->
      let sort = ESorts.kind sigma u in
      if Sorts.is_small sort then s
      else
        Level.Set.fold Level.Set.add (Sorts.levels sort) s
    | Evar (k, args) ->
      let concl = Evd.evar_concl (Evd.find sigma k) in
      fold sigma aux (aux s concl) c
    | Array (u,_,_,_) ->
      let s = Level.Set.fold Level.Set.add (Instance.levels (EInstance.kind sigma u)) s in
      fold sigma aux s c
    | Case (_,u,_,_,_,_,_) ->
      let s = Level.Set.fold Level.Set.add (Instance.levels (EInstance.kind sigma u)) s in
      fold sigma aux s c
    | _ -> fold sigma aux s c
  in aux Level.Set.empty c

open Context
open Environ

let cast_list : type a b. (a,b) eq -> a list -> b list =
  fun Refl x -> x

let cast_list_snd : type a b. (a,b) eq -> ('c * a) list -> ('c * b) list =
  fun Refl x -> x

let cast_vect : type a b. (a,b) eq -> a array -> b array =
  fun Refl x -> x

let cast_rel_decl :
  type a b. (a,b) eq -> (a, a) Rel.Declaration.pt -> (b, b) Rel.Declaration.pt =
  fun Refl x -> x

let cast_rel_context :
  type a b. (a,b) eq -> (a, a) Rel.pt -> (b, b) Rel.pt =
  fun Refl x -> x

let cast_rec_decl :
  type a b. (a,b) eq -> (a, a) Constr.prec_declaration -> (b, b) Constr.prec_declaration =
  fun Refl x -> x

let cast_named_decl :
  type a b. (a,b) eq -> (a, a) Named.Declaration.pt -> (b, b) Named.Declaration.pt =
  fun Refl x -> x

let cast_named_context :
  type a b. (a,b) eq -> (a, a) Named.pt -> (b, b) Named.pt =
  fun Refl x -> x


module Vars =
struct
exception LocalOccur
let to_constr = unsafe_to_constr
let to_rel_decl = unsafe_to_rel_decl

type instance = t array
type instance_list = t list
type substl = t list

(** Operations that commute with evar-normalization *)
let lift = lift
let liftn n m c = of_constr (Vars.liftn n m (to_constr c))

let substnl subst n c = of_constr (Vars.substnl (cast_list unsafe_eq subst) n (to_constr c))
let substl subst c = of_constr (Vars.substl (cast_list unsafe_eq subst) (to_constr c))
let subst1 c r = of_constr (Vars.subst1 (to_constr c) (to_constr r))

let substnl_decl subst n d = of_rel_decl (Vars.substnl_decl (cast_list unsafe_eq subst) n (to_rel_decl d))
let substl_decl subst d = of_rel_decl (Vars.substl_decl (cast_list unsafe_eq subst) (to_rel_decl d))
let subst1_decl c d = of_rel_decl (Vars.subst1_decl (to_constr c) (to_rel_decl d))

let replace_vars subst c =
  of_constr (Vars.replace_vars (cast_list_snd unsafe_eq subst) (to_constr c))
let substn_vars n subst c = of_constr (Vars.substn_vars n subst (to_constr c))
let subst_vars subst c = of_constr (Vars.subst_vars subst (to_constr c))
let subst_var subst c = of_constr (Vars.subst_var subst (to_constr c))

let subst_univs_level_constr subst c =
  of_constr (Vars.subst_univs_level_constr subst (to_constr c))

let subst_instance_context subst ctx =
  cast_rel_context (sym unsafe_eq) (Vars.subst_instance_context subst (cast_rel_context unsafe_eq ctx))

let subst_instance_constr subst c =
  of_constr (Vars.subst_instance_constr subst (to_constr c))

(** Operations that dot NOT commute with evar-normalization *)
let noccurn sigma n term =
  let rec occur_rec n c = match kind sigma c with
    | Rel m -> if Int.equal m n then raise LocalOccur
    | _ -> iter_with_binders sigma succ occur_rec n c
  in
  try occur_rec n term; true with LocalOccur -> false

let noccur_between sigma n m term =
  let rec occur_rec n c = match kind sigma c with
    | Rel p -> if n<=p && p<n+m then raise LocalOccur
    | _        -> iter_with_binders sigma succ occur_rec n c
  in
  try occur_rec n term; true with LocalOccur -> false

let closedn sigma n c =
  let rec closed_rec n c = match kind sigma c with
    | Rel m -> if m>n then raise LocalOccur
    | _ -> iter_with_binders sigma succ closed_rec n c
  in
  try closed_rec n c; true with LocalOccur -> false

let closed0 sigma c = closedn sigma 0 c

let subst_of_rel_context_instance ctx subst =
  cast_list (sym unsafe_eq)
    (Vars.subst_of_rel_context_instance (cast_rel_context unsafe_eq ctx) (cast_vect unsafe_eq subst))
let subst_of_rel_context_instance_list ctx subst =
  cast_list (sym unsafe_eq)
    (Vars.subst_of_rel_context_instance_list (cast_rel_context unsafe_eq ctx) (cast_list unsafe_eq subst))

let liftn_rel_context n k ctx =
  cast_rel_context (sym unsafe_eq)
    (Vars.liftn_rel_context n k (cast_rel_context unsafe_eq ctx))

let lift_rel_context n ctx =
  cast_rel_context (sym unsafe_eq)
    (Vars.lift_rel_context n (cast_rel_context unsafe_eq ctx))

let substnl_rel_context subst n ctx =
  cast_rel_context (sym unsafe_eq)
    (Vars.substnl_rel_context (cast_list unsafe_eq subst) n (cast_rel_context unsafe_eq ctx))

let substl_rel_context subst ctx =
  cast_rel_context (sym unsafe_eq)
    (Vars.substl_rel_context (cast_list unsafe_eq subst) (cast_rel_context unsafe_eq ctx))

let smash_rel_context ctx =
  cast_rel_context (sym unsafe_eq)
      (Vars.smash_rel_context (cast_rel_context unsafe_eq ctx))

let esubst : (int -> 'a -> t) -> 'a Esubst.subs -> t -> t =
match unsafe_eq with
| Refl -> Vars.esubst

type substituend = Vars.substituend
let make_substituend c = Vars.make_substituend (unsafe_to_constr c)
let lift_substituend n s = of_constr (Vars.lift_substituend n s)


end

let rec isArity sigma c =
  match kind sigma c with
  | Prod (_,_,c)    -> isArity sigma c
  | LetIn (_,b,_,c) -> isArity sigma (Vars.subst1 b c)
  | Cast (c,_,_)      -> isArity sigma c
  | Sort _          -> true
  | _               -> false

type arity = rel_context * ESorts.t

let destArity sigma =
  let open Context.Rel.Declaration in
  let rec prodec_rec l c =
    match kind sigma c with
    | Prod (x,t,c)    -> prodec_rec (LocalAssum (x,t) :: l) c
    | LetIn (x,b,t,c) -> prodec_rec (LocalDef (x,b,t) :: l) c
    | Cast (c,_,_)      -> prodec_rec l c
    | Sort s          -> l,s
    | _               -> anomaly ~label:"destArity" (Pp.str "not an arity.")
  in
  prodec_rec []

let mkProd_or_LetIn decl c =
  let open Context.Rel.Declaration in
  match decl with
  | LocalAssum (na,t) -> mkProd (na, t, c)
  | LocalDef (na,b,t) -> mkLetIn (na, b, t, c)

let mkLambda_or_LetIn decl c =
  let open Context.Rel.Declaration in
  match decl with
  | LocalAssum (na,t) -> mkLambda (na, t, c)
  | LocalDef (na,b,t) -> mkLetIn (na, b, t, c)

let mkNamedProd id typ c = mkProd (map_annot Name.mk_name id, typ, Vars.subst_var id.binder_name c)
let mkNamedLambda id typ c = mkLambda (map_annot Name.mk_name id, typ, Vars.subst_var id.binder_name c)
let mkNamedLetIn id c1 t c2 = mkLetIn (map_annot Name.mk_name id, c1, t, Vars.subst_var id.binder_name c2)

let mkNamedProd_or_LetIn decl c =
  let open Context.Named.Declaration in
  match decl with
    | LocalAssum (id,t) -> mkNamedProd id t c
    | LocalDef (id,b,t) -> mkNamedLetIn id b t c

let mkNamedLambda_or_LetIn decl c =
  let open Context.Named.Declaration in
  match decl with
    | LocalAssum (id,t) -> mkNamedLambda id t c
    | LocalDef (id,b,t) -> mkNamedLetIn id b t c

let it_mkProd_or_LetIn t ctx = List.fold_left (fun c d -> mkProd_or_LetIn d c) t ctx
let it_mkLambda_or_LetIn t ctx = List.fold_left (fun c d -> mkLambda_or_LetIn d c) t ctx

let push_rel d e = push_rel (cast_rel_decl unsafe_eq d) e
let push_rel_context d e = push_rel_context (cast_rel_context unsafe_eq d) e
let push_rec_types d e = push_rec_types (cast_rec_decl unsafe_eq d) e
let push_named d e = push_named (cast_named_decl unsafe_eq d) e
let push_named_context d e = push_named_context (cast_named_context unsafe_eq d) e
let push_named_context_val d e = push_named_context_val (cast_named_decl unsafe_eq d) e

let rel_context e = cast_rel_context (sym unsafe_eq) (rel_context e)
let named_context e = cast_named_context (sym unsafe_eq) (named_context e)

let val_of_named_context e = val_of_named_context (cast_named_context unsafe_eq e)
let named_context_of_val e = cast_named_context (sym unsafe_eq) (named_context_of_val e)

let of_existential : Constr.existential -> existential =
  let gen : type a b. (a,b) eq -> 'c * b list -> 'c * a list = fun Refl x -> x in
  gen unsafe_eq

let lookup_rel i e = cast_rel_decl (sym unsafe_eq) (lookup_rel i e)
let lookup_named n e = cast_named_decl (sym unsafe_eq) (lookup_named n e)
let lookup_named_val n e = cast_named_decl (sym unsafe_eq) (lookup_named_ctxt n e)

let map_rel_context_in_env f env sign =
  let rec aux env acc = function
    | d::sign ->
        aux (push_rel d env) (Context.Rel.Declaration.map_constr (f env) d :: acc) sign
    | [] ->
        acc
  in
  aux env [] (List.rev sign)

let match_named_context_val :
  named_context_val -> (named_declaration * lazy_val * named_context_val) option =
  match unsafe_eq with
  | Refl -> match_named_context_val

let identity_subst_val : named_context_val -> t list =
  match unsafe_eq with Refl -> fun ctx -> ctx.env_named_var

let fresh_global ?loc ?rigid ?names env sigma reference =
  let (evd,t) = Evd.fresh_global ?loc ?rigid ?names env sigma reference in
  evd, t

let is_global = isRefX

(** Kind of type *)

type kind_of_type =
  | SortType   of ESorts.t
  | CastType   of types * t
  | ProdType   of Name.t Context.binder_annot * t * t
  | LetInType  of Name.t Context.binder_annot * t * t * t
  | AtomicType of t * t array

let kind_of_type sigma t = match kind sigma t with
  | Sort s -> SortType s
  | Cast (c,_,t) -> CastType (c, t)
  | Prod (na,t,c) -> ProdType (na, t, c)
  | LetIn (na,b,t,c) -> LetInType (na, b, t, c)
  | App (c,l) -> AtomicType (c, l)
  | (Rel _ | Meta _ | Var _ | Evar _ | Const _
  | Proj _ | Case _ | Fix _ | CoFix _ | Ind _)
    -> AtomicType (t,[||])
  | (Lambda _ | Construct _ | Int _ | Float _ | Array _) -> failwith "Not a type"

module Unsafe =
struct
let to_sorts = ESorts.unsafe_to_sorts
let to_instance = EInstance.unsafe_to_instance
let to_constr = unsafe_to_constr
let to_constr_array = unsafe_to_constr_array
let to_rel_decl = unsafe_to_rel_decl
let to_named_decl = unsafe_to_named_decl
let to_named_context =
  let gen : type a b. (a, b) eq -> (a,a) Context.Named.pt -> (b,b) Context.Named.pt
    = fun Refl x -> x
  in
  gen unsafe_eq
let to_rel_context =
  let gen : type a b. (a, b) eq -> (a,a) Context.Rel.pt -> (b,b) Context.Rel.pt
    = fun Refl x -> x
  in
  gen unsafe_eq
let to_case_invert = unsafe_to_case_invert

let eq = unsafe_eq
end
