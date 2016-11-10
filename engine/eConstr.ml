(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open CSig
open CErrors
open Util
open Names
open Term
open Context
open Evd

module API :
sig
type t
val kind : Evd.evar_map -> t -> (t, t) Constr.kind_of_term
val kind_upto : Evd.evar_map -> constr -> (constr, types) Constr.kind_of_term
val of_kind : (t, t) Constr.kind_of_term -> t
val of_constr : Constr.t -> t
val unsafe_to_constr : t -> Constr.t
val unsafe_eq : (t, Constr.t) eq
end =
struct

type t = Constr.t

let safe_evar_value sigma ev =
  try Some (Evd.existential_value sigma ev)
  with NotInstantiatedEvar | Not_found -> None

let rec kind sigma c =
  let c0 = Constr.kind c in
  match c0 with
  | Evar (evk, args) ->
    (match safe_evar_value sigma (evk, args) with
        Some c -> kind sigma c
      | None -> c0)
  | Sort (Type u) ->
    let u' = Evd.normalize_universe sigma u in
    if u' == u then c0 else Sort (Type u')
  | Const (c', u) when not (Univ.Instance.is_empty u) ->
    let u' = Evd.normalize_universe_instance sigma u in
    if u' == u then c0 else Const (c', u')
  | Ind (i, u) when not (Univ.Instance.is_empty u) ->
    let u' = Evd.normalize_universe_instance sigma u in
    if u' == u then c0 else Ind (i, u')
  | Construct (co, u) when not (Univ.Instance.is_empty u) ->
    let u' = Evd.normalize_universe_instance sigma u in
    if u' == u then c0 else Construct (co, u')
  | App (c, args) when isEvar c ->
    (** Enforce smart constructor invariant on applications *)
    let ev = destEvar c in
    begin match safe_evar_value sigma ev with
    | None -> c0
    | Some c -> kind sigma (mkApp (c, args))
    end
  | _ -> c0

let kind_upto = kind
let of_kind = Constr.of_kind
let of_constr c = c
let unsafe_to_constr c = c
let unsafe_eq = Refl

end

include API

type types = t
type constr = t
type existential = t pexistential
type fixpoint = (t, t) pfixpoint
type cofixpoint = (t, t) pcofixpoint
type unsafe_judgment = (constr, types) Environ.punsafe_judgment
type unsafe_type_judgment = types Environ.punsafe_type_judgment

let mkProp = of_kind (Sort Sorts.prop)
let mkSet = of_kind (Sort Sorts.set)
let mkType u = of_kind (Sort (Sorts.Type u))
let mkRel n = of_kind (Rel n)
let mkVar id = of_kind (Var id)
let mkMeta n = of_kind (Meta n)
let mkEvar e = of_kind (Evar e)
let mkSort s = of_kind (Sort s)
let mkCast (b, k, t) = of_kind (Cast (b, k, t))
let mkProd (na, t, u) = of_kind (Prod (na, t, u))
let mkLambda (na, t, c) = of_kind (Lambda (na, t, c))
let mkLetIn (na, b, t, c) = of_kind (LetIn (na, b, t, c))
let mkApp (f, arg) = of_kind (App (f, arg))
let mkConstU pc = of_kind (Const pc)
let mkIndU pi = of_kind (Ind pi)
let mkConstructU pc = of_kind (Construct pc)
let mkCase (ci, c, r, p) = of_kind (Case (ci, c, r, p))
let mkFix f = of_kind (Fix f)
let mkCoFix f = of_kind (CoFix f)
let mkProj (p, c) = of_kind (Proj (p, c))

let applist (f, arg) = mkApp (f, Array.of_list arg)

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
let isVarId sigma id c =
  match kind sigma c with Var id' -> Id.equal id id' | _ -> false

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

let decompose_app sigma c =
  match kind sigma c with
    | App (f,cl) -> (f, Array.to_list cl)
    | _ -> (c,[])

let local_assum (na, t) =
  let open Rel.Declaration in
  LocalAssum (na, unsafe_to_constr t)

let local_def (na, b, t) =
  let open Rel.Declaration in
  LocalDef (na, unsafe_to_constr b, unsafe_to_constr t)

let decompose_lam sigma c =
  let rec lamdec_rec l c = match kind sigma c with
    | Lambda (x,t,c) -> lamdec_rec ((x,t)::l) c
    | Cast (c,_,_)     -> lamdec_rec l c
    | _                -> l,c
  in
  lamdec_rec [] c

let decompose_lam_assum sigma c =
  let rec lamdec_rec l c =
    match kind sigma c with
    | Lambda (x,t,c)  -> lamdec_rec (Context.Rel.add (local_assum (x,t)) l) c
    | LetIn (x,b,t,c) -> lamdec_rec (Context.Rel.add (local_def (x,b,t)) l) c
    | Cast (c,_,_)      -> lamdec_rec l c
    | _               -> l,c
  in
  lamdec_rec Context.Rel.empty c

let decompose_lam_n_assum sigma n c =
  if n < 0 then
    error "decompose_lam_n_assum: integer parameter must be positive";
  let rec lamdec_rec l n c =
    if Int.equal n 0 then l,c
    else
      match kind sigma c with
      | Lambda (x,t,c)  -> lamdec_rec (Context.Rel.add (local_assum (x,t)) l) (n-1) c
      | LetIn (x,b,t,c) -> lamdec_rec (Context.Rel.add (local_def (x,b,t)) l) n c
      | Cast (c,_,_)      -> lamdec_rec l n c
      | c -> error "decompose_lam_n_assum: not enough abstractions"
  in
  lamdec_rec Context.Rel.empty n c

let decompose_lam_n_decls sigma n =
  if n < 0 then
    error "decompose_lam_n_decls: integer parameter must be positive";
  let rec lamdec_rec l n c =
    if Int.equal n 0 then l,c
    else
      match kind sigma c with
      | Lambda (x,t,c)  -> lamdec_rec (Context.Rel.add (local_assum (x,t)) l) (n-1) c
      | LetIn (x,b,t,c) -> lamdec_rec (Context.Rel.add (local_def (x,b,t)) l) (n-1) c
      | Cast (c,_,_)      -> lamdec_rec l n c
      | c -> error "decompose_lam_n_decls: not enough abstractions"
  in
  lamdec_rec Context.Rel.empty n

let decompose_prod sigma c =
  let rec proddec_rec l c = match kind sigma c with
    | Prod (x,t,c) -> proddec_rec ((x,t)::l) c
    | Cast (c,_,_)     -> proddec_rec l c
    | _                -> l,c
  in
  proddec_rec [] c

let decompose_prod_assum sigma c =
  let rec proddec_rec l c =
    match kind sigma c with
    | Prod (x,t,c)  -> proddec_rec (Context.Rel.add (local_assum (x,t)) l) c
    | LetIn (x,b,t,c) -> proddec_rec (Context.Rel.add (local_def (x,b,t)) l) c
    | Cast (c,_,_)      -> proddec_rec l c
    | _               -> l,c
  in
  proddec_rec Context.Rel.empty c

let decompose_prod_n_assum sigma n c =
  if n < 0 then
    error "decompose_prod_n_assum: integer parameter must be positive";
  let rec prodec_rec l n c =
    if Int.equal n 0 then l,c
    else
      match kind sigma c with
      | Prod (x,t,c)    -> prodec_rec (Context.Rel.add (local_assum (x,t)) l) (n-1) c
      | LetIn (x,b,t,c) -> prodec_rec (Context.Rel.add (local_def (x,b,t)) l) (n-1) c
      | Cast (c,_,_)      -> prodec_rec l n c
      | c -> error "decompose_prod_n_assum: not enough assumptions"
  in
  prodec_rec Context.Rel.empty n c

let existential_type sigma (evk, args) =
  of_constr (existential_type sigma (evk, Array.map unsafe_to_constr args))

let map sigma f c = match kind sigma c with
  | (Rel _ | Meta _ | Var _   | Sort _ | Const _ | Ind _
    | Construct _) -> c
  | Cast (b,k,t) ->
      let b' = f b in
      let t' = f t in
      if b'==b && t' == t then c
      else mkCast (b', k, t')
  | Prod (na,t,b) ->
      let b' = f b in
      let t' = f t in
      if b'==b && t' == t then c
      else mkProd (na, t', b')
  | Lambda (na,t,b) ->
      let b' = f b in
      let t' = f t in
      if b'==b && t' == t then c
      else mkLambda (na, t', b')
  | LetIn (na,b,t,k) ->
      let b' = f b in
      let t' = f t in
      let k' = f k in
      if b'==b && t' == t && k'==k then c
      else mkLetIn (na, b', t', k')
  | App (b,l) ->
      let b' = f b in
      let l' = Array.smartmap f l in
      if b'==b && l'==l then c
      else mkApp (b', l')
  | Proj (p,t) ->
      let t' = f t in
      if t' == t then c
      else mkProj (p, t')
  | Evar (e,l) ->
      let l' = Array.smartmap f l in
      if l'==l then c
      else mkEvar (e, l')
  | Case (ci,p,b,bl) ->
      let b' = f b in
      let p' = f p in
      let bl' = Array.smartmap f bl in
      if b'==b && p'==p && bl'==bl then c
      else mkCase (ci, p', b', bl')
  | Fix (ln,(lna,tl,bl)) ->
      let tl' = Array.smartmap f tl in
      let bl' = Array.smartmap f bl in
      if tl'==tl && bl'==bl then c
      else mkFix (ln,(lna,tl',bl'))
  | CoFix(ln,(lna,tl,bl)) ->
      let tl' = Array.smartmap f tl in
      let bl' = Array.smartmap f bl in
      if tl'==tl && bl'==bl then c
      else mkCoFix (ln,(lna,tl',bl'))

let map_with_binders sigma g f l c0 = match kind sigma c0 with
  | (Rel _ | Meta _ | Var _   | Sort _ | Const _ | Ind _
    | Construct _) -> c0
  | Cast (c, k, t) ->
    let c' = f l c in
    let t' = f l t in
    if c' == c && t' == t then c0
    else mkCast (c', k, t')
  | Prod (na, t, c) ->
    let t' = f l t in
    let c' = f (g l) c in
    if t' == t && c' == c then c0
    else mkProd (na, t', c')
  | Lambda (na, t, c) ->
    let t' = f l t in
    let c' = f (g l) c in
    if t' == t && c' == c then c0
    else mkLambda (na, t', c')
  | LetIn (na, b, t, c) ->
    let b' = f l b in
    let t' = f l t in
    let c' = f (g l) c in
    if b' == b && t' == t && c' == c then c0
    else mkLetIn (na, b', t', c')
  | App (c, al) ->
    let c' = f l c in
    let al' = CArray.Fun1.smartmap f l al in
    if c' == c && al' == al then c0
    else mkApp (c', al')
  | Proj (p, t) ->
    let t' = f l t in
    if t' == t then c0
    else mkProj (p, t')
  | Evar (e, al) ->
    let al' = CArray.Fun1.smartmap f l al in
    if al' == al then c0
    else mkEvar (e, al')
  | Case (ci, p, c, bl) ->
    let p' = f l p in
    let c' = f l c in
    let bl' = CArray.Fun1.smartmap f l bl in
    if p' == p && c' == c && bl' == bl then c0
    else mkCase (ci, p', c', bl')
  | Fix (ln, (lna, tl, bl)) ->
    let tl' = CArray.Fun1.smartmap f l tl in
    let l' = iterate g (Array.length tl) l in
    let bl' = CArray.Fun1.smartmap f l' bl in
    if tl' == tl && bl' == bl then c0
    else mkFix (ln,(lna,tl',bl'))
  | CoFix(ln,(lna,tl,bl)) ->
    let tl' = CArray.Fun1.smartmap f l tl in
    let l' = iterate g (Array.length tl) l in
    let bl' = CArray.Fun1.smartmap f l' bl in
    mkCoFix (ln,(lna,tl',bl'))

let iter sigma f c = match kind sigma c with
  | (Rel _ | Meta _ | Var _   | Sort _ | Const _ | Ind _
    | Construct _) -> ()
  | Cast (c,_,t) -> f c; f t
  | Prod (_,t,c) -> f t; f c
  | Lambda (_,t,c) -> f t; f c
  | LetIn (_,b,t,c) -> f b; f t; f c
  | App (c,l) -> f c; Array.iter f l
  | Proj (p,c) -> f c
  | Evar (_,l) -> Array.iter f l
  | Case (_,p,c,bl) -> f p; f c; Array.iter f bl
  | Fix (_,(_,tl,bl)) -> Array.iter f tl; Array.iter f bl
  | CoFix (_,(_,tl,bl)) -> Array.iter f tl; Array.iter f bl

let iter_with_full_binders sigma g f n c = match kind sigma c with
  | (Rel _ | Meta _ | Var _   | Sort _ | Const _ | Ind _
    | Construct _) -> ()
  | Cast (c,_,t) -> f n c; f n t
  | Prod (na,t,c) -> f n t; f (g (local_assum (na, t)) n) c
  | Lambda (na,t,c) -> f n t; f (g (local_assum (na, t)) n) c
  | LetIn (na,b,t,c) -> f n b; f n t; f (g (local_def (na, b, t)) n) c
  | App (c,l) -> f n c; CArray.Fun1.iter f n l
  | Evar (_,l) -> CArray.Fun1.iter f n l
  | Case (_,p,c,bl) -> f n p; f n c; CArray.Fun1.iter f n bl
  | Proj (p,c) -> f n c
  | Fix (_,(lna,tl,bl)) ->
    Array.iter (f n) tl;
    let n' = Array.fold_left2 (fun n na t -> g (local_assum (na,t)) n) n lna tl in
    Array.iter (f n') bl
  | CoFix (_,(lna,tl,bl)) ->
    Array.iter (f n) tl;
    let n' = Array.fold_left2 (fun n na t -> g (local_assum (na,t)) n) n lna tl in
    Array.iter (f n') bl

let iter_with_binders sigma g f n c =
  iter_with_full_binders sigma (fun _ acc -> g acc) f n c

let fold sigma f acc c = match kind sigma c with
  | (Rel _ | Meta _ | Var _   | Sort _ | Const _ | Ind _
    | Construct _) -> acc
  | Cast (c,_,t) -> f (f acc c) t
  | Prod (_,t,c) -> f (f acc t) c
  | Lambda (_,t,c) -> f (f acc t) c
  | LetIn (_,b,t,c) -> f (f (f acc b) t) c
  | App (c,l) -> Array.fold_left f (f acc c) l
  | Proj (p,c) -> f acc c
  | Evar (_,l) -> Array.fold_left f acc l
  | Case (_,p,c,bl) -> Array.fold_left f (f (f acc p) c) bl
  | Fix (_,(lna,tl,bl)) ->
    Array.fold_left2 (fun acc t b -> f (f acc t) b) acc tl bl
  | CoFix (_,(lna,tl,bl)) ->
    Array.fold_left2 (fun acc t b -> f (f acc t) b) acc tl bl

let to_constr sigma t =
  let rec map c = Constr.map map (Constr.of_kind (kind_upto sigma c)) in
  map (unsafe_to_constr t)

let compare_gen k eq_inst eq_sort eq_constr c1 c2 =
  (c1 == c2) || Constr.compare_head_gen_with k k eq_inst eq_sort eq_constr c1 c2

let eq_constr sigma c1 c2 =
  let kind c = kind_upto sigma c in
  let rec eq_constr c1 c2 =
    compare_gen kind (fun _ -> Univ.Instance.equal) Sorts.equal eq_constr c1 c2
  in
  eq_constr (unsafe_to_constr c1) (unsafe_to_constr c2)

let eq_constr_nounivs sigma c1 c2 =
  let kind c = kind_upto sigma c in
  let rec eq_constr c1 c2 =
    compare_gen kind (fun _ _ _ -> true) (fun _ _ -> true) eq_constr c1 c2
  in
  eq_constr (unsafe_to_constr c1) (unsafe_to_constr c2)

(** TODO: factorize with universes.ml *)
let test_constr_universes sigma leq m n =
  let open Universes in
  let kind c = kind_upto sigma c in
  if m == n then Some Constraints.empty
  else 
    let cstrs = ref Constraints.empty in
    let eq_universes strict l l' = 
      cstrs := enforce_eq_instances_univs strict l l' !cstrs; true in
    let eq_sorts s1 s2 = 
      if Sorts.equal s1 s2 then true
      else (cstrs := Constraints.add 
	      (Sorts.univ_of_sort s1,UEq,Sorts.univ_of_sort s2) !cstrs; 
	    true)
    in
    let leq_sorts s1 s2 = 
      if Sorts.equal s1 s2 then true
      else 
	(cstrs := Constraints.add 
	   (Sorts.univ_of_sort s1,ULe,Sorts.univ_of_sort s2) !cstrs; 
	 true)
    in
    let rec eq_constr' m n = compare_gen kind eq_universes eq_sorts eq_constr' m n in
    let res =
      if leq then
        let rec compare_leq m n =
          Constr.compare_head_gen_leq_with kind kind eq_universes leq_sorts eq_constr' leq_constr' m n
        and leq_constr' m n = m == n || compare_leq m n in
        compare_leq m n
      else
        Constr.compare_head_gen_with kind kind eq_universes eq_sorts eq_constr' m n
    in
    if res then Some !cstrs else None

let eq_constr_universes sigma m n =
  test_constr_universes sigma false (unsafe_to_constr m) (unsafe_to_constr n)
let leq_constr_universes sigma m n =
  test_constr_universes sigma true (unsafe_to_constr m) (unsafe_to_constr n)

let compare_head_gen_proj env sigma equ eqs eqc' m n =
  let kind c = kind_upto sigma c in
  match kind_upto sigma m, kind_upto sigma n with
  | Proj (p, c), App (f, args)
  | App (f, args), Proj (p, c) -> 
      (match kind_upto sigma f with
      | Const (p', u) when Constant.equal (Projection.constant p) p' -> 
          let pb = Environ.lookup_projection p env in
          let npars = pb.Declarations.proj_npars in
	  if Array.length args == npars + 1 then
	    eqc' c args.(npars)
	  else false
      | _ -> false)
  | _ -> Constr.compare_head_gen_with kind kind equ eqs eqc' m n

let eq_constr_universes_proj env sigma m n =
  let open Universes in
  if m == n then Some Constraints.empty
  else 
    let cstrs = ref Constraints.empty in
    let eq_universes strict l l' = 
      cstrs := enforce_eq_instances_univs strict l l' !cstrs; true in
    let eq_sorts s1 s2 = 
      if Sorts.equal s1 s2 then true
      else
	(cstrs := Constraints.add 
	   (Sorts.univ_of_sort s1, UEq, Sorts.univ_of_sort s2) !cstrs;
	 true)
    in
    let rec eq_constr' m n = 
      m == n ||	compare_head_gen_proj env sigma eq_universes eq_sorts eq_constr' m n
    in
    let res = eq_constr' (unsafe_to_constr m) (unsafe_to_constr n) in
    if res then Some !cstrs else None

module Vars =
struct
exception LocalOccur
let to_constr = unsafe_to_constr

(** Operations that commute with evar-normalization *)
let lift n c = of_constr (Vars.lift n (to_constr c))
let liftn n m c = of_constr (Vars.liftn n m (to_constr c))

let substnl subst n c = of_constr (Vars.substnl (List.map to_constr subst) n (to_constr c))
let substl subst c = of_constr (Vars.substl (List.map to_constr subst) (to_constr c))
let subst1 c r = of_constr (Vars.subst1 (to_constr c) (to_constr r))

let replace_vars subst c =
  let map (id, c) = (id, to_constr c) in
  of_constr (Vars.replace_vars (List.map map subst) (to_constr c))
let substn_vars n subst c = of_constr (Vars.substn_vars n subst (to_constr c))
let subst_vars subst c = of_constr (Vars.subst_vars subst (to_constr c))
let subst_var subst c = of_constr (Vars.subst_var subst (to_constr c))

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

end

let rec isArity sigma c =
  match kind sigma c with
  | Prod (_,_,c)    -> isArity sigma c
  | LetIn (_,b,_,c) -> isArity sigma (Vars.subst1 b c)
  | Cast (c,_,_)      -> isArity sigma c
  | Sort _          -> true
  | _               -> false

let mkProd_or_LetIn decl c =
  let open Context.Rel.Declaration in
  match decl with
  | LocalAssum (na,t) -> mkProd (na, of_constr t, c)
  | LocalDef (na,b,t) -> mkLetIn (na, of_constr b, of_constr t, c)

let mkLambda_or_LetIn decl c =
  let open Context.Rel.Declaration in
  match decl with
  | LocalAssum (na,t) -> mkLambda (na, of_constr t, c)
  | LocalDef (na,b,t) -> mkLetIn (na, of_constr b, of_constr t, c)

let it_mkProd_or_LetIn t ctx = List.fold_left (fun c d -> mkProd_or_LetIn d c) t ctx
let it_mkLambda_or_LetIn t ctx = List.fold_left (fun c d -> mkLambda_or_LetIn d c) t ctx

module Unsafe =
struct
let to_constr = unsafe_to_constr
let eq = unsafe_eq
end
