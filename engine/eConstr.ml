(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open CErrors
open Util
open Names
open Term
open Context
open Evd

module API :
sig
module ESorts :
sig
type t
val make : Sorts.t -> t
val kind : Evd.evar_map -> t -> Sorts.t
val unsafe_to_sorts : t -> Sorts.t
end
module EInstance :
sig
type t
val make : Univ.Instance.t -> t
val kind : Evd.evar_map -> t -> Univ.Instance.t
val empty : t
val is_empty : t -> bool
val unsafe_to_instance : t -> Univ.Instance.t
end
type t
val kind : Evd.evar_map -> t -> (t, t, ESorts.t, EInstance.t) Constr.kind_of_term
val kind_upto : Evd.evar_map -> constr -> (constr, types, Sorts.t, Univ.Instance.t) Constr.kind_of_term
val kind_of_type : Evd.evar_map -> t -> (t, t) kind_of_type
val whd_evar : Evd.evar_map -> t -> t
val of_kind : (t, t, ESorts.t, EInstance.t) Constr.kind_of_term -> t
val of_constr : Constr.t -> t
val to_constr : evar_map -> t -> Constr.t
val unsafe_to_constr : t -> Constr.t
val unsafe_eq : (t, Constr.t) eq
val of_named_decl : (Constr.t, Constr.types) Context.Named.Declaration.pt -> (t, t) Context.Named.Declaration.pt
val unsafe_to_named_decl : (t, t) Context.Named.Declaration.pt -> (Constr.t, Constr.types) Context.Named.Declaration.pt
val unsafe_to_rel_decl : (t, t) Context.Rel.Declaration.pt -> (Constr.t, Constr.types) Context.Rel.Declaration.pt
val of_rel_decl : (Constr.t, Constr.types) Context.Rel.Declaration.pt -> (t, t) Context.Rel.Declaration.pt
end =
struct

module ESorts =
struct
  type t = Sorts.t
  let make s = s
  let kind sigma = function
  | Type u -> sort_of_univ (Evd.normalize_universe sigma u)
  | s -> s
  let unsafe_to_sorts s = s
end

module EInstance =
struct
  type t = Univ.Instance.t
  let make i = i
  let kind sigma i =
    if Univ.Instance.is_empty i then i
    else Evd.normalize_universe_instance sigma i
  let empty = Univ.Instance.empty
  let is_empty = Univ.Instance.is_empty
  let unsafe_to_instance t = t
end

type t = Constr.t

let safe_evar_value sigma ev =
  try Some (Evd.existential_value sigma ev)
  with NotInstantiatedEvar | Not_found -> None

let rec whd_evar sigma c =
  match Constr.kind c with
  | Evar ev ->
    begin match safe_evar_value sigma ev with
    | Some c -> whd_evar sigma c
    | None -> c
    end
  | App (f, args) when isEvar f ->
    (** Enforce smart constructor invariant on applications *)
    let ev = destEvar f in
    begin match safe_evar_value sigma ev with
    | None -> c
    | Some f -> whd_evar sigma (mkApp (f, args))
    end
  | Cast (c0, k, t) when isEvar c0 ->
    (** Enforce smart constructor invariant on casts. *)
    let ev = destEvar c0 in
    begin match safe_evar_value sigma ev with
    | None -> c
    | Some c -> whd_evar sigma (mkCast (c, k, t))
    end
  | _ -> c

let kind sigma c = Constr.kind (whd_evar sigma c)
let kind_upto = kind
let kind_of_type sigma c = Term.kind_of_type (whd_evar sigma c)
let of_kind = Constr.of_kind
let of_constr c = c
let unsafe_to_constr c = c
let unsafe_eq = Refl

let rec to_constr sigma c = match Constr.kind c with
| Evar ev ->
  begin match safe_evar_value sigma ev with
  | Some c -> to_constr sigma c
  | None -> Constr.map (fun c -> to_constr sigma c) c
  end
| Sort (Type u) ->
  let u' = Evd.normalize_universe sigma u in
  if u' == u then c else mkSort (Sorts.sort_of_univ u')
| Const (c', u) when not (Univ.Instance.is_empty u) ->
  let u' = Evd.normalize_universe_instance sigma u in
  if u' == u then c else mkConstU (c', u')
| Ind (i, u) when not (Univ.Instance.is_empty u) ->
  let u' = Evd.normalize_universe_instance sigma u in
  if u' == u then c else mkIndU (i, u')
| Construct (co, u) when not (Univ.Instance.is_empty u) ->
  let u' = Evd.normalize_universe_instance sigma u in
  if u' == u then c else mkConstructU (co, u')
| _ -> Constr.map (fun c -> to_constr sigma c) c

let of_named_decl d = d
let unsafe_to_named_decl d = d
let of_rel_decl d = d
let unsafe_to_rel_decl d = d

end

include API

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
    error "decompose_lam_n_assum: integer parameter must be positive";
  let rec lamdec_rec l n c =
    if Int.equal n 0 then l,c
    else
      match kind sigma c with
      | Lambda (x,t,c)  -> lamdec_rec (Context.Rel.add (LocalAssum (x,t)) l) (n-1) c
      | LetIn (x,b,t,c) -> lamdec_rec (Context.Rel.add (LocalDef (x,b,t)) l) n c
      | Cast (c,_,_)      -> lamdec_rec l n c
      | c -> error "decompose_lam_n_assum: not enough abstractions"
  in
  lamdec_rec Context.Rel.empty n c

let decompose_lam_n_decls sigma n =
  let open Rel.Declaration in
  if n < 0 then
    error "decompose_lam_n_decls: integer parameter must be positive";
  let rec lamdec_rec l n c =
    if Int.equal n 0 then l,c
    else
      match kind sigma c with
      | Lambda (x,t,c)  -> lamdec_rec (Context.Rel.add (LocalAssum (x,t)) l) (n-1) c
      | LetIn (x,b,t,c) -> lamdec_rec (Context.Rel.add (LocalDef (x,b,t)) l) (n-1) c
      | Cast (c,_,_)      -> lamdec_rec l n c
      | c -> error "decompose_lam_n_decls: not enough abstractions"
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
    error "decompose_prod_n_assum: integer parameter must be positive";
  let rec prodec_rec l n c =
    if Int.equal n 0 then l,c
    else
      match kind sigma c with
      | Prod (x,t,c)    -> prodec_rec (Context.Rel.add (LocalAssum (x,t)) l) (n-1) c
      | LetIn (x,b,t,c) -> prodec_rec (Context.Rel.add (LocalDef (x,b,t)) l) (n-1) c
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

let iter_with_full_binders sigma g f n c =
  let open Context.Rel.Declaration in
  match kind sigma c with
  | (Rel _ | Meta _ | Var _   | Sort _ | Const _ | Ind _
    | Construct _) -> ()
  | Cast (c,_,t) -> f n c; f n t
  | Prod (na,t,c) -> f n t; f (g (LocalAssum (na, t)) n) c
  | Lambda (na,t,c) -> f n t; f (g (LocalAssum (na, t)) n) c
  | LetIn (na,b,t,c) -> f n b; f n t; f (g (LocalDef (na, b, t)) n) c
  | App (c,l) -> f n c; CArray.Fun1.iter f n l
  | Evar (_,l) -> CArray.Fun1.iter f n l
  | Case (_,p,c,bl) -> f n p; f n c; CArray.Fun1.iter f n bl
  | Proj (p,c) -> f n c
  | Fix (_,(lna,tl,bl)) ->
    Array.iter (f n) tl;
    let n' = Array.fold_left2 (fun n na t -> g (LocalAssum (na,t)) n) n lna tl in
    Array.iter (f n') bl
  | CoFix (_,(lna,tl,bl)) ->
    Array.iter (f n) tl;
    let n' = Array.fold_left2 (fun n na t -> g (LocalAssum (na,t)) n) n lna tl in
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

let compare_constr sigma cmp c1 c2 =
  let kind c = kind_upto sigma c in
  let cmp c1 c2 = cmp (of_constr c1) (of_constr c2) in
  compare_gen kind (fun _ -> Univ.Instance.equal) Sorts.equal cmp (unsafe_to_constr c1) (unsafe_to_constr c2)

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
  List.map of_constr (Vars.subst_of_rel_context_instance (List.map unsafe_to_rel_decl ctx) (List.map to_constr subst))

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

open Context
open Environ

let sym : type a b. (a, b) eq -> (b, a) eq = fun Refl -> Refl

let cast_rel_decl :
  type a b. (a,b) eq -> (a, a) Rel.Declaration.pt -> (b, b) Rel.Declaration.pt =
  fun Refl x -> x

let cast_rel_context :
  type a b. (a,b) eq -> (a, a) Rel.pt -> (b, b) Rel.pt =
  fun Refl x -> x

let cast_named_decl :
  type a b. (a,b) eq -> (a, a) Named.Declaration.pt -> (b, b) Named.Declaration.pt =
  fun Refl x -> x

let cast_named_context :
  type a b. (a,b) eq -> (a, a) Named.pt -> (b, b) Named.pt =
  fun Refl x -> x

let push_rel d e = push_rel (cast_rel_decl unsafe_eq d) e
let push_rel_context d e = push_rel_context (cast_rel_context unsafe_eq d) e
let push_named d e = push_named (cast_named_decl unsafe_eq d) e
let push_named_context d e = push_named_context (cast_named_context unsafe_eq d) e
let push_named_context_val d e = push_named_context_val (cast_named_decl unsafe_eq d) e

let rel_context e = cast_rel_context (sym unsafe_eq) (rel_context e)
let named_context e = cast_named_context (sym unsafe_eq) (named_context e)

let val_of_named_context e = val_of_named_context (cast_named_context unsafe_eq e)
let named_context_of_val e = cast_named_context (sym unsafe_eq) (named_context_of_val e)

let lookup_rel i e = cast_rel_decl (sym unsafe_eq) (lookup_rel i e)
let lookup_named n e = cast_named_decl (sym unsafe_eq) (lookup_named n e)
let lookup_named_val n e = cast_named_decl (sym unsafe_eq) (lookup_named_val n e)

let fresh_global ?loc ?rigid ?names env sigma reference =
  let Sigma.Sigma (t,sigma,p) =
    Sigma.fresh_global ?loc ?rigid ?names env sigma reference in
  Sigma.Sigma (of_constr t,sigma,p)

module Unsafe =
struct
let to_sorts = ESorts.unsafe_to_sorts
let to_instance = EInstance.unsafe_to_instance
let to_constr = unsafe_to_constr
let to_rel_decl = unsafe_to_rel_decl
let to_named_decl = unsafe_to_named_decl
let eq = unsafe_eq
end
