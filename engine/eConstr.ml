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

let mkProp = of_kind (Sort (ESorts.make Sorts.prop))
let mkSet = of_kind (Sort (ESorts.make Sorts.set))
let mkType u = of_kind (Sort (ESorts.make (Sorts.Type u)))
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
let mkCase (ci, c, r, p) = of_kind (Case (ci, c, r, p))
let mkFix f = of_kind (Fix f)
let mkCoFix f = of_kind (CoFix f)
let mkProj (p, c) = of_kind (Proj (p, c))
let mkArrow t1 t2 = of_kind (Prod (Anonymous, t1, t2))
let mkInt i = of_kind (Int i)

let mkRef (gr,u) = let open GlobRef in match gr with
  | ConstRef c -> mkConstU (c,u)
  | IndRef ind -> mkIndU (ind,u)
  | ConstructRef c -> mkConstructU (c,u)
  | VarRef x -> mkVar x

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
| Case (ci, t, c, p) -> (ci, t, c, p)
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
    | Cast (c,_,_)      -> lamdec_rec l c
    | _               -> l,c
  in
  lamdec_rec Context.Rel.empty c

let decompose_lam_n_assum sigma n c =
  let open Rel.Declaration in
  if n < 0 then
    user_err Pp.(str "decompose_lam_n_assum: integer parameter must be positive");
  let rec lamdec_rec l n c =
    if Int.equal n 0 then l,c
    else
      match kind sigma c with
      | Lambda (x,t,c)  -> lamdec_rec (Context.Rel.add (LocalAssum (x,t)) l) (n-1) c
      | LetIn (x,b,t,c) -> lamdec_rec (Context.Rel.add (LocalDef (x,b,t)) l) n c
      | Cast (c,_,_)      -> lamdec_rec l n c
      | c -> user_err Pp.(str "decompose_lam_n_assum: not enough abstractions")
  in
  lamdec_rec Context.Rel.empty n c

let decompose_lam_n_decls sigma n =
  let open Rel.Declaration in
  if n < 0 then
    user_err Pp.(str "decompose_lam_n_decls: integer parameter must be positive");
  let rec lamdec_rec l n c =
    if Int.equal n 0 then l,c
    else
      match kind sigma c with
      | Lambda (x,t,c)  -> lamdec_rec (Context.Rel.add (LocalAssum (x,t)) l) (n-1) c
      | LetIn (x,b,t,c) -> lamdec_rec (Context.Rel.add (LocalDef (x,b,t)) l) (n-1) c
      | Cast (c,_,_)      -> lamdec_rec l n c
      | c -> user_err Pp.(str "decompose_lam_n_decls: not enough abstractions")
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
      | _   -> user_err ~hdr:"to_lambda" (Pp.mt ())

let decompose_prod sigma c =
  let rec proddec_rec l c = match kind sigma c with
    | Prod (x,t,c) -> proddec_rec ((x,t)::l) c
    | Cast (c,_,_)     -> proddec_rec l c
    | _                -> l,c
  in
  proddec_rec [] c

let decompose_prod_assum sigma c =
  let open Rel.Declaration in
  let rec proddec_rec l c =
    match kind sigma c with
    | Prod (x,t,c)  -> proddec_rec (Context.Rel.add (LocalAssum (x,t)) l) c
    | LetIn (x,b,t,c) -> proddec_rec (Context.Rel.add (LocalDef (x,b,t)) l) c
    | Cast (c,_,_)      -> proddec_rec l c
    | _               -> l,c
  in
  proddec_rec Context.Rel.empty c

let decompose_prod_n_assum sigma n c =
  let open Rel.Declaration in
  if n < 0 then
    user_err Pp.(str "decompose_prod_n_assum: integer parameter must be positive");
  let rec prodec_rec l n c =
    if Int.equal n 0 then l,c
    else
      match kind sigma c with
      | Prod (x,t,c)    -> prodec_rec (Context.Rel.add (LocalAssum (x,t)) l) (n-1) c
      | LetIn (x,b,t,c) -> prodec_rec (Context.Rel.add (LocalDef (x,b,t)) l) (n-1) c
      | Cast (c,_,_)      -> prodec_rec l n c
      | c -> user_err Pp.(str "decompose_prod_n_assum: not enough assumptions")
  in
  prodec_rec Context.Rel.empty n c

let existential_type = Evd.existential_type

let lift n c = of_constr (Vars.lift n (unsafe_to_constr c))

let map_under_context f n c =
  let f c = unsafe_to_constr (f (of_constr c)) in
  of_constr (Constr.map_under_context f n (unsafe_to_constr c))
let map_branches f ci br =
  let f c = unsafe_to_constr (f (of_constr c)) in
  of_constr_array (Constr.map_branches f ci (unsafe_to_constr_array br))
let map_return_predicate f ci p =
  let f c = unsafe_to_constr (f (of_constr c)) in
  of_constr (Constr.map_return_predicate f ci (unsafe_to_constr p))

let map_user_view sigma f c =
  let f c = unsafe_to_constr (f (of_constr c)) in
  of_constr (Constr.map_user_view f (unsafe_to_constr (whd_evar sigma c)))

let map sigma f c =
  let f c = unsafe_to_constr (f (of_constr c)) in
  of_constr (Constr.map f (unsafe_to_constr (whd_evar sigma c)))

let map_with_binders sigma g f l c =
  let f l c = unsafe_to_constr (f l (of_constr c)) in
  of_constr (Constr.map_with_binders g f l (unsafe_to_constr (whd_evar sigma c)))

let iter sigma f c =
  let f c = f (of_constr c) in
  Constr.iter f (unsafe_to_constr (whd_evar sigma c))

let iter_with_full_binders sigma g f n c =
  let open Context.Rel.Declaration in
  match kind sigma c with
  | (Rel _ | Meta _ | Var _   | Sort _ | Const _ | Ind _
    | Construct _ | Int _) -> ()
  | Cast (c,_,t) -> f n c; f n t
  | Prod (na,t,c) -> f n t; f (g (LocalAssum (na, t)) n) c
  | Lambda (na,t,c) -> f n t; f (g (LocalAssum (na, t)) n) c
  | LetIn (na,b,t,c) -> f n b; f n t; f (g (LocalDef (na, b, t)) n) c
  | App (c,l) -> f n c; Array.Fun1.iter f n l
  | Evar (_,l) -> Array.Fun1.iter f n l
  | Case (_,p,c,bl) -> f n p; f n c; Array.Fun1.iter f n bl
  | Proj (p,c) -> f n c
  | Fix (_,(lna,tl,bl)) ->
    Array.iter (f n) tl;
    let n' = Array.fold_left2_i (fun i n na t -> g (LocalAssum (na, lift i t)) n) n lna tl in
    Array.iter (f n') bl
  | CoFix (_,(lna,tl,bl)) ->
    Array.iter (f n) tl;
    let n' = Array.fold_left2_i (fun i n na t -> g (LocalAssum (na,lift i t)) n) n lna tl in
    Array.iter (f n') bl

let iter_with_binders sigma g f n c =
  let f l c = f l (of_constr c) in
  Constr.iter_with_binders g f n (unsafe_to_constr (whd_evar sigma c))

let fold sigma f acc c =
  let f acc c = f acc (of_constr c) in
  Constr.fold f acc (unsafe_to_constr (whd_evar sigma c))

let compare_gen k eq_inst eq_sort eq_constr nargs c1 c2 =
  (c1 == c2) || Constr.compare_head_gen_with k k eq_inst eq_sort eq_constr nargs c1 c2

let eq_constr sigma c1 c2 =
  let kind c = kind sigma c in
  let eq_inst _ _ i1 i2 = EInstance.equal sigma i1 i2 in
  let eq_sorts s1 s2 = ESorts.equal sigma s1 s2 in
  let rec eq_constr nargs c1 c2 =
    compare_gen kind eq_inst eq_sorts eq_constr nargs c1 c2
  in
  eq_constr 0 c1 c2

let eq_constr_nounivs sigma c1 c2 =
  let kind c = kind sigma c in
  let rec eq_constr nargs c1 c2 =
    compare_gen kind (fun _ _ _ _ -> true) (fun _ _ -> true) eq_constr nargs c1 c2
  in
  eq_constr 0 c1 c2

let compare_constr sigma cmp c1 c2 =
  let kind c = kind sigma c in
  let eq_inst _ _ i1 i2 = EInstance.equal sigma i1 i2 in
  let eq_sorts s1 s2 = ESorts.equal sigma s1 s2 in
  let cmp nargs c1 c2 = cmp c1 c2 in
  compare_gen kind eq_inst eq_sorts cmp 0 c1 c2

let compare_cumulative_instances cv_pb nargs_ok variances u u' cstrs =
  let open UnivProblem in
  if not nargs_ok then enforce_eq_instances_univs false u u' cstrs
  else
    CArray.fold_left3
      (fun cstrs v u u' ->
         let open Univ.Variance in
         match v with
         | Irrelevant -> Set.add (UWeak (u,u')) cstrs
         | Covariant ->
           let u = Univ.Universe.make u in
           let u' = Univ.Universe.make u' in
           (match cv_pb with
            | Reduction.CONV -> Set.add (UEq (u,u')) cstrs
            | Reduction.CUMUL -> Set.add (ULe (u,u')) cstrs)
         | Invariant ->
           let u = Univ.Universe.make u in
           let u' = Univ.Universe.make u' in
           Set.add (UEq (u,u')) cstrs)
      cstrs variances (Univ.Instance.to_array u) (Univ.Instance.to_array u')

let cmp_inductives cv_pb (mind,ind as spec) nargs u1 u2 cstrs =
  let open UnivProblem in
  match mind.Declarations.mind_universes with
  | Declarations.Monomorphic_ind _ ->
    assert (Univ.Instance.length u1 = 0 && Univ.Instance.length u2 = 0);
    cstrs
  | Declarations.Polymorphic_ind _ ->
     enforce_eq_instances_univs false u1 u2 cstrs
  | Declarations.Cumulative_ind cumi ->
    let num_param_arity = Reduction.inductive_cumulativity_arguments spec in
    let variances = Univ.ACumulativityInfo.variance cumi in
    compare_cumulative_instances cv_pb (Int.equal num_param_arity nargs) variances u1 u2 cstrs

let cmp_constructors (mind, ind, cns as spec) nargs u1 u2 cstrs =
  let open UnivProblem in
  match mind.Declarations.mind_universes with
  | Declarations.Monomorphic_ind _ ->
    cstrs
  | Declarations.Polymorphic_ind _ ->
    enforce_eq_instances_univs false u1 u2 cstrs
  | Declarations.Cumulative_ind cumi ->
    let num_cnstr_args = Reduction.constructor_cumulativity_arguments spec in
    if not (Int.equal num_cnstr_args nargs)
    then enforce_eq_instances_univs false u1 u2 cstrs
    else
      Array.fold_left2 (fun cstrs u1 u2 -> UnivProblem.(Set.add (UWeak (u1,u2)) cstrs))
        cstrs (Univ.Instance.to_array u1) (Univ.Instance.to_array u2)

let eq_universes env sigma cstrs cv_pb ref nargs l l' =
  if EInstance.is_empty l then (assert (EInstance.is_empty l'); true)
  else
    let l = EInstance.kind sigma l
    and l' = EInstance.kind sigma l' in
    let open GlobRef in
    let open UnivProblem in
    match ref with
    | VarRef _ -> assert false (* variables don't have instances *)
    | ConstRef _ ->
      cstrs := enforce_eq_instances_univs true l l' !cstrs; true
    | IndRef ind ->
      let mind = Environ.lookup_mind (fst ind) env in
      cstrs := cmp_inductives cv_pb (mind,snd ind) nargs l l' !cstrs;
      true
    | ConstructRef ((mi,ind),ctor) ->
      let mind = Environ.lookup_mind mi env in
      cstrs := cmp_constructors (mind,ind,ctor) nargs l l' !cstrs;
      true

let test_constr_universes env sigma leq m n =
  let open UnivProblem in
  let kind c = kind sigma c in
  if m == n then Some Set.empty
  else
    let cstrs = ref Set.empty in
    let cv_pb = if leq then Reduction.CUMUL else Reduction.CONV in
    let eq_universes ref nargs l l' = eq_universes env sigma cstrs Reduction.CONV ref nargs l l'
    and leq_universes ref nargs l l' = eq_universes env sigma cstrs cv_pb ref nargs l l' in
    let eq_sorts s1 s2 =
      let s1 = ESorts.kind sigma s1 in
      let s2 = ESorts.kind sigma s2 in
      if Sorts.equal s1 s2 then true
      else (cstrs := Set.add
              (UEq (Sorts.univ_of_sort s1,Sorts.univ_of_sort s2)) !cstrs;
	    true)
    in
    let leq_sorts s1 s2 = 
      let s1 = ESorts.kind sigma s1 in
      let s2 = ESorts.kind sigma s2 in
      if Sorts.equal s1 s2 then true
      else 
        (cstrs := Set.add
           (ULe (Sorts.univ_of_sort s1,Sorts.univ_of_sort s2)) !cstrs;
	 true)
    in
    let rec eq_constr' nargs m n = compare_gen kind eq_universes eq_sorts eq_constr' nargs m n in
    let res =
      if leq then
        let rec compare_leq nargs m n =
          Constr.compare_head_gen_leq_with kind kind leq_universes leq_sorts
            eq_constr' leq_constr' nargs m n
        and leq_constr' nargs m n = m == n || compare_leq nargs m n in
        compare_leq 0 m n
      else
        Constr.compare_head_gen_with kind kind eq_universes eq_sorts eq_constr' 0 m n
    in
    if res then Some !cstrs else None

let eq_constr_universes env sigma m n =
  test_constr_universes env sigma false m n
let leq_constr_universes env sigma m n =
  test_constr_universes env sigma true m n

let compare_head_gen_proj env sigma equ eqs eqc' nargs m n =
  let kind c = kind sigma c in
  match kind m, kind n with
  | Proj (p, c), App (f, args)
  | App (f, args), Proj (p, c) -> 
      (match kind f with
      | Const (p', u) when Constant.equal (Projection.constant p) p' -> 
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
           (UEq (Sorts.univ_of_sort s1, Sorts.univ_of_sort s2)) !cstrs;
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
          LSet.fold LSet.add (Instance.levels (EInstance.kind sigma u)) s
    | Ind ((mind,_), u) | Construct (((mind,_),_), u) ->
          LSet.fold LSet.add (Instance.levels (EInstance.kind sigma u)) s
    | Sort u ->
       let sort = ESorts.kind sigma u in
       if Sorts.is_small sort then s
       else
         let u = Sorts.univ_of_sort sort in
         LSet.fold LSet.add (Universe.levels u) s
    | Evar (k, args) ->
       let concl = Evd.evar_concl (Evd.find sigma k) in
       fold sigma aux (aux s concl) c
    | _ -> fold sigma aux s c
  in aux LSet.empty c

open Context
open Environ

let cast_list : type a b. (a,b) eq -> a list -> b list =
  fun Refl x -> x

let cast_list_snd : type a b. (a,b) eq -> ('c * a) list -> ('c * b) list =
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
    (Vars.subst_of_rel_context_instance (cast_rel_context unsafe_eq ctx) (cast_list unsafe_eq subst))

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

let mkNamedProd id typ c = mkProd (Name id, typ, Vars.subst_var id c)
let mkNamedLambda id typ c = mkLambda (Name id, typ, Vars.subst_var id c)
let mkNamedLetIn id c1 t c2 = mkLetIn (Name id, c1, t, Vars.subst_var id c2)

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
  let gen : type a b. (a,b) eq -> 'c * b array -> 'c * a array = fun Refl x -> x in
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

let fresh_global ?loc ?rigid ?names env sigma reference =
  let (evd,t) = Evd.fresh_global ?loc ?rigid ?names env sigma reference in
  evd, t

let is_global sigma gr c =
  Globnames.is_global gr (to_constr sigma c)

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
let eq = unsafe_eq
end
