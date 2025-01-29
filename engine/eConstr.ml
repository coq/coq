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
open Constr
open Context

module NamedDecl = Context.Named.Declaration

module ERelevance = struct
  include Evd.MiniEConstr.ERelevance

  let equal sigma r1 r2 = Sorts.relevance_equal (kind sigma r1) (kind sigma r2)

  let is_irrelevant = Evd.is_relevance_irrelevant

  let relevant = make Relevant
  let irrelevant = make Irrelevant
end

module ESorts = struct
  include Evd.MiniEConstr.ESorts

  let equal sigma s1 s2 =
    Sorts.equal (kind sigma s1) (kind sigma s2)

  let is_small sigma s = Sorts.is_small (kind sigma s)
  let is_prop sigma s = Sorts.is_prop (kind sigma s)
  let is_sprop sigma s = Sorts.is_sprop (kind sigma s)
  let is_set sigma s = Sorts.is_set (kind sigma s)

  let prop = make Sorts.prop
  let sprop = make Sorts.sprop
  let set = make Sorts.set
  let type1 = make Sorts.type1

  let super sigma s =
    make (Sorts.super (kind sigma s))

  let relevance_of_sort s =
    let r = Sorts.relevance_of_sort (unsafe_to_sorts s) in
    ERelevance.make r

  let family sigma s = Sorts.family (kind sigma s)

  let quality sigma s = Sorts.quality (kind sigma s)

end

module EInstance = struct
  include Evd.MiniEConstr.EInstance

  let equal sigma i1 i2 =
    UVars.Instance.equal (kind sigma i1) (kind sigma i2)

  let length u = UVars.Instance.length (unsafe_to_instance u)
end

module Expand :
sig

type t
type kind = (t, t, ESorts.t, EInstance.t, ERelevance.t) Constr.kind_of_term
type handle
val make : Evd.econstr -> handle * t
val repr : Evd.evar_map -> handle -> t -> Evd.econstr
val liftn_handle : int -> handle -> handle
val kind : Evd.evar_map -> handle -> t -> handle * kind
val expand_instance : skip:bool -> Evd.undefined Evd.evar_info -> handle -> t SList.t -> t SList.t
val iter : Evd.evar_map -> (handle -> t -> unit) -> handle -> kind -> unit
val iter_with_binders : Evd.evar_map -> ('a -> 'a) -> ('a -> handle -> t -> unit) -> 'a -> handle -> kind -> unit

end
=
struct
  include Evd.Expand
  type t = Evd.econstr
  type kind = (t, t, ESorts.t, EInstance.t, ERelevance.t) Constr.kind_of_term

  let make c = (empty_handle, c)
  let repr = expand

  let iter sigma f h knd = match knd with
  | Evar (evk, args) ->
    let evi = Evd.find_undefined sigma evk in
    let args = expand_instance ~skip:false evi h args in
    (* Despite the type, the sparse list contains no default element *)
    SList.Skip.iter (f h) args
  | Rel _ | Meta _ | Var _   | Sort _ | Const _ | Ind _
  | Construct _ | Int _ | Float _ | String _ -> ()
  | Cast (c, _, t) -> f h c; f h t
  | Prod (_, t, c) -> f h t; f (liftn_handle 1 h) c
  | Lambda (_, t, c) -> f h t; f (liftn_handle 1 h) c
  | LetIn (_, b, t, c) -> f h b; f h t; f (liftn_handle 1 h) c
  | App (c, l) -> f h c; Array.Fun1.iter f h l
  | Case (_, _, pms, (p, _), iv, c, bl) ->
    Array.Fun1.iter f h pms;
    f (liftn_handle (Array.length (fst p)) h) (snd p);
    iter_invert (f h) iv;
    f h c;
    Array.Fun1.iter (fun h (ctx, b) -> f (liftn_handle (Array.length ctx) h) b) h bl
  | Proj (_p, _r, c) -> f h c
  | Fix (_, (_, tl, bl)) ->
    Array.Fun1.iter f h tl;
    Array.Fun1.iter f (liftn_handle (Array.length tl) h) bl
  | CoFix (_, (_, tl, bl)) ->
    Array.Fun1.iter f h tl;
    Array.Fun1.iter f (liftn_handle (Array.length tl) h) bl
  | Array(_u, t, def, ty) ->
    Array.iter (f h) t; f h def; f h ty

  let iter_with_binders sigma g f l h knd = match knd with
  | Evar (evk, args) ->
    let evi = Evd.find_undefined sigma evk in
    let args = expand_instance ~skip:false evi h args in
    (* Despite the type, the sparse list contains no default element *)
    SList.Skip.iter (f l h) args
  | Rel _ | Meta _ | Var _   | Sort _ | Const _ | Ind _
  | Construct _ | Int _ | Float _ | String _ -> ()
  | Cast (c, _, t) -> f l h c; f l h t
  | Prod (_, t, c) -> f l h t; f (g l) (liftn_handle 1 h) c
  | Lambda (_, t, c) -> f l h t; f (g l) (liftn_handle 1 h) c
  | LetIn (_, b, t, c) -> f l h b; f l h t; f (g l) (liftn_handle 1 h) c
  | App (c, args) -> f l h c; Array.iter (fun c -> f l h c) args
  | Case (_, _, pms, (p, _), iv, c, bl) ->
    Array.iter (fun c -> f l h c) pms;
    f (iterate g (Array.length (fst p)) l) (liftn_handle (Array.length (fst p)) h) (snd p);
    iter_invert (fun c -> f l h c) iv;
    f l h c;
    Array.iter (fun (ctx, b) -> f (iterate g (Array.length ctx) l) (liftn_handle (Array.length ctx) h) b) bl
  | Proj (_p, _r, c) -> f l h c
  | Fix (_, (_, tl, bl)) ->
    Array.iter (fun c -> f l h c) tl;
    Array.iter (f (iterate g (Array.length tl) l) (liftn_handle (Array.length tl) h)) bl
  | CoFix (_, (_, tl, bl)) ->
    Array.iter (fun c -> f l h c) tl;
    Array.iter (f (iterate g (Array.length tl) l) (liftn_handle (Array.length tl) h)) bl
  | Array(_u, t, def, ty) ->
    Array.iter (fun c -> f l h c) t; f l h def; f l h ty

end

include (Evd.MiniEConstr : module type of Evd.MiniEConstr
         with module ERelevance := ERelevance
          and module ESorts := ESorts
          and module EInstance := EInstance)

type types = t
type constr = t
type existential = t pexistential
type case_return = (t, ERelevance.t) pcase_return
type case_branch = (t, ERelevance.t) pcase_branch
type case_invert = t pcase_invert
type case = (t, t, EInstance.t, ERelevance.t) pcase
type rec_declaration = (t, t, ERelevance.t) prec_declaration
type fixpoint = (t, t, ERelevance.t) pfixpoint
type cofixpoint = (t, t, ERelevance.t) pcofixpoint
type unsafe_judgment = (constr, types) Environ.punsafe_judgment
type unsafe_type_judgment = (types, ESorts.t) Environ.punsafe_type_judgment
type named_declaration = (constr, types, ERelevance.t) Context.Named.Declaration.pt
type rel_declaration = (constr, types, ERelevance.t) Context.Rel.Declaration.pt
type compacted_declaration = (constr, types, ERelevance.t) Context.Compacted.Declaration.pt
type named_context = (constr, types, ERelevance.t) Context.Named.pt
type compacted_context = compacted_declaration list
type rel_context = (constr, types, ERelevance.t) Context.Rel.pt
type 'a binder_annot = ('a, ERelevance.t) Context.pbinder_annot

let annotR x = Context.make_annot x ERelevance.relevant
let nameR x = annotR (Name x)
let anonR = annotR Anonymous

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
let mkSort s = of_kind (Sort s)
let mkCast (b, k, t) = of_kind (Cast (b, k, t))
let mkProd (na, t, u) = of_kind (Prod (na, t, u))
let mkLambda (na, t, c) = of_kind (Lambda (na, t, c))
let mkLetIn (na, b, t, c) = of_kind (LetIn (na, b, t, c))
let mkApp (f, arg) = of_kind (App (f, arg))
let mkConstU pc = of_kind (Const pc)
let mkIndU pi = of_kind (Ind pi)
let mkConstructU pc = of_kind (Construct pc)
let mkConstructUi ((ind,u),i) = of_kind (Construct ((ind,i),u))
let mkCase (ci, u, pms, c, iv, r, p) = of_kind (Case (ci, u, pms, c, iv, r, p))
let mkFix f = of_kind (Fix f)
let mkCoFix f = of_kind (CoFix f)
let mkProj (p, r, c) = of_kind (Proj (p, r, c))
let mkArrow t1 r t2 = of_kind (Prod (make_annot Anonymous r, t1, t2))
let mkArrowR t1 t2 = mkArrow t1 ERelevance.relevant t2
let mkInt i = of_kind (Int i)
let mkFloat f = of_kind (Float f)
let mkString s = of_kind (String s)
let mkArray (u,t,def,ty) = of_kind (Array (u,t,def,ty))

let mkRef (gr,u) = let open GlobRef in match gr with
  | ConstRef c -> mkConstU (c,u)
  | IndRef ind -> mkIndU (ind,u)
  | ConstructRef c -> mkConstructU (c,u)
  | VarRef x -> mkVar x

let mkLEvar = Evd.MiniEConstr.mkLEvar

let type1 = mkSort ESorts.type1

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

let isRefX env sigma x c =
  let open GlobRef in
  match x, kind sigma c with
  | ConstRef c, Const (c', _) -> Environ.QConstant.equal env c c'
  | IndRef i, Ind (i', _) -> Environ.QInd.equal env i i'
  | ConstructRef i, Construct (i', _) -> Environ.QConstruct.equal env i i'
  | VarRef id, Var id' -> Id.equal id id'
  | _ -> false

let is_lib_ref env sigma x c =
  match Rocqlib.lib_ref_opt x with
  | Some x -> isRefX env sigma x c
  | None -> false

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
| Proj (p, r, c) -> (p, r, c)
| _ -> raise DestKO

let destRef sigma c = let open GlobRef in match kind sigma c with
  | Var x -> VarRef x, EInstance.empty
  | Const (c,u) -> ConstRef c, u
  | Ind (ind,u) -> IndRef ind, u
  | Construct (c,u) -> ConstructRef c, u
  | _ -> raise DestKO

let decompose_app sigma c =
  match kind sigma c with
  | App (f,cl) -> (f, cl)
  | _ -> (c,[||])

let decompose_app_list sigma c =
  match kind sigma c with
    | App (f,cl) -> (f, Array.to_list cl)
    | _ -> (c,[])

let decompose_lambda sigma c =
  let rec lamdec_rec l c = match kind sigma c with
    | Lambda (x,t,c) -> lamdec_rec ((x,t)::l) c
    | Cast (c,_,_)     -> lamdec_rec l c
    | _                -> l,c
  in
  lamdec_rec [] c

let decompose_lambda_decls sigma c =
  let open Rel.Declaration in
  let rec lamdec_rec l c =
    match kind sigma c with
    | Lambda (x,t,c)  -> lamdec_rec (Context.Rel.add (LocalAssum (x,t)) l) c
    | LetIn (x,b,t,c) -> lamdec_rec (Context.Rel.add (LocalDef (x,b,t)) l) c
    | Cast (c,_,_)    -> lamdec_rec l c
    | _               -> l,c
  in
  lamdec_rec Context.Rel.empty c

let decompose_lambda_n sigma n =
  if n < 0 then
    anomaly Pp.(str "decompose_lambda_n: integer parameter must be positive");
  let rec lamdec_rec l n c =
    if Int.equal n 0 then (l, c)
    else
      match kind sigma c with
      | Lambda (x, t, c) -> lamdec_rec ((x, t) :: l) (n - 1) c
      | Cast (c, _, _) -> lamdec_rec l n c
      | _ ->
        anomaly Pp.(str "decompose_lambda_n: not enough abstractions")
  in
  lamdec_rec [] n

let decompose_lambda_n_assum sigma n c =
  let open Rel.Declaration in
  if n < 0 then
    anomaly Pp.(str "decompose_lambda_n_assum: integer parameter must be positive.");
  let rec lamdec_rec l n c =
    if Int.equal n 0 then l,c
    else
      match kind sigma c with
      | Lambda (x,t,c)  -> lamdec_rec (Context.Rel.add (LocalAssum (x,t)) l) (n-1) c
      | LetIn (x,b,t,c) -> lamdec_rec (Context.Rel.add (LocalDef (x,b,t)) l) n c
      | Cast (c,_,_)    -> lamdec_rec l n c
      | c -> anomaly Pp.(str "decompose_lambda_n_assum: not enough abstractions.")
  in
  lamdec_rec Context.Rel.empty n c

let decompose_lambda_n_decls sigma n =
  let open Rel.Declaration in
  if n < 0 then
    anomaly Pp.(str "decompose_lambda_n_decls: integer parameter must be positive.");
  let rec lamdec_rec l n c =
    if Int.equal n 0 then l,c
    else
      match kind sigma c with
      | Lambda (x,t,c)  -> lamdec_rec (Context.Rel.add (LocalAssum (x,t)) l) (n-1) c
      | LetIn (x,b,t,c) -> lamdec_rec (Context.Rel.add (LocalDef (x,b,t)) l) (n-1) c
      | Cast (c,_,_)    -> lamdec_rec l n c
      | c -> anomaly Pp.(str "decompose_lambda_n_decls: not enough abstractions.")
  in
  lamdec_rec Context.Rel.empty n

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

let decompose_prod_n sigma n =
  if n < 0 then
    anomaly Pp.(str "decompose_prod_n: integer parameter must be positive");
  let rec proddec_rec l n c =
    if Int.equal n 0 then (l, c)
    else
      match kind sigma c with
      | Prod (x, t, c) -> proddec_rec ((x, t) :: l) (n - 1) c
      | Cast (c, _, _) -> proddec_rec l n c
      | _ ->
        anomaly Pp.(str "decompose_prod_n: not enough products")
  in
  proddec_rec [] n

let decompose_prod_decls sigma c =
  let open Rel.Declaration in
  let rec proddec_rec l c =
    match kind sigma c with
    | Prod (x,t,c)    -> proddec_rec (Context.Rel.add (LocalAssum (x,t)) l) c
    | LetIn (x,b,t,c) -> proddec_rec (Context.Rel.add (LocalDef (x,b,t)) l) c
    | Cast (c,_,_)    -> proddec_rec l c
    | _               -> l,c
  in
  proddec_rec Context.Rel.empty c

let decompose_prod_n_decls sigma n c =
  let open Rel.Declaration in
  if n < 0 then
    anomaly Pp.(str "decompose_prod_n_decls: integer parameter must be positive.");
  let rec prodec_rec l n c =
    if Int.equal n 0 then l,c
    else
      match kind sigma c with
      | Prod (x,t,c)    -> prodec_rec (Context.Rel.add (LocalAssum (x,t)) l) (n-1) c
      | LetIn (x,b,t,c) -> prodec_rec (Context.Rel.add (LocalDef (x,b,t)) l) (n-1) c
      | Cast (c,_,_)    -> prodec_rec l n c
      | c -> anomaly Pp.(str "decompose_prod_n_decls: not enough assumptions.")
  in
  prodec_rec Context.Rel.empty n c

let prod_decls sigma t = fst (decompose_prod_decls sigma t)

let existential_type = Evd.existential_type

let lift n c = of_constr (Vars.lift n (unsafe_to_constr c))

let of_branches : Constr.case_branch array -> case_branch array =
  match Evd.MiniEConstr.(unsafe_eq, unsafe_relevance_eq) with
  | Refl, Refl -> fun x -> x

let unsafe_to_branches : case_branch array -> Constr.case_branch array =
  match Evd.MiniEConstr.(unsafe_eq, unsafe_relevance_eq) with
  | Refl, Refl -> fun x -> x

let of_return : Constr.case_return -> case_return =
  match Evd.MiniEConstr.(unsafe_eq, unsafe_relevance_eq) with
  | Refl, Refl -> fun x -> x

let unsafe_to_return : case_return -> Constr.case_return =
  match Evd.MiniEConstr.(unsafe_eq, unsafe_relevance_eq) with
  | Refl, Refl -> fun x -> x

let of_binder_annot : 'a Constr.binder_annot -> 'a binder_annot =
  match Evd.MiniEConstr.unsafe_relevance_eq with
  | Refl -> fun x -> x

let to_binder_annot sigma (x:_ binder_annot) : _ Constr.binder_annot =
  let Refl = unsafe_relevance_eq in
  Context.map_annot_relevance (ERelevance.kind sigma) x

let to_rel_decl sigma (d:rel_declaration) : Constr.rel_declaration =
  let Refl = unsafe_eq in
  let Refl = unsafe_relevance_eq in
  Context.Rel.Declaration.map_constr_with_relevance (ERelevance.kind sigma) (to_constr sigma) d

let to_rel_context sigma (ctx:rel_context) : Constr.rel_context =
  let Refl = unsafe_eq in
  let Refl = unsafe_relevance_eq in
  List.Smart.map (to_rel_decl sigma) ctx

let to_named_decl sigma (d:named_declaration) : Constr.named_declaration =
  let Refl = unsafe_eq in
  let Refl = unsafe_relevance_eq in
  Context.Named.Declaration.map_constr_with_relevance (ERelevance.kind sigma) (to_constr sigma) d

let to_named_context sigma (ctx:named_context) : Constr.named_context =
  let Refl = unsafe_eq in
  let Refl = unsafe_relevance_eq in
  List.Smart.map (to_named_decl sigma) ctx

let map_branches f br =
  let f c = unsafe_to_constr (f (of_constr c)) in
  of_branches (Constr.map_branches f (unsafe_to_branches br))
let map_return_predicate f p =
  let f c = unsafe_to_constr (f (of_constr c)) in
  of_return (Constr.map_return_predicate f (unsafe_to_return p))

let map_instance sigma f evk args =
  let rec map ctx args = match ctx, SList.view args with
  | [], None -> SList.empty
  | decl :: ctx, Some (Some c, rem) ->
    let c' = f c in
    let rem' = map ctx rem in
    if c' == c && rem' == rem then args
    else if Constr.isVarId (NamedDecl.get_id decl) c' then SList.default rem'
    else SList.cons c' rem'
  | decl :: ctx, Some (None, rem) ->
    let c = Constr.mkVar (NamedDecl.get_id decl) in
    let c' = f c in
    let rem' = map ctx rem in
    if c' == c && rem' == rem then args
    else SList.cons c' rem'
  | [], Some _ | _ :: _, None -> assert false
  in
  let EvarInfo evi = Evd.find sigma evk in
  let ctx = Evd.evar_filtered_context evi in
  map ctx args

let map sigma f c =
  let f c = unsafe_to_constr (f (of_constr c)) in
  let c = unsafe_to_constr @@ whd_evar sigma c in
  match Constr.kind c with
  | Evar (evk, args) ->
    let args' = map_instance sigma f evk args in
    if args' == args then of_constr c else of_constr @@ Constr.mkEvar (evk, args')
  | _ -> of_constr (Constr.map f c)

let map_with_binders sigma g f l c =
  let f l c = unsafe_to_constr (f l (of_constr c)) in
  let c = unsafe_to_constr @@ whd_evar sigma c in
  match Constr.kind c with
  | Evar (evk, args) ->
    let args' = map_instance sigma (fun c -> f l c) evk args in
    if args' == args then of_constr c else of_constr @@ Constr.mkEvar (evk, args')
  | _ -> of_constr (Constr.map_with_binders g f l c)

let map_existential sigma f ((evk, args) as ev : existential) =
  let f c = unsafe_to_constr (f (of_constr c)) in
  let args : Constr.t SList.t = match Evd.MiniEConstr.unsafe_eq with Refl -> args in
  let args' = map_instance sigma f evk args in
  if args' == args then ev
  else
    let args' : t SList.t = match Evd.MiniEConstr.unsafe_eq with Refl -> args' in
    (evk, args')

let iter sigma f c =
  let f c = f (of_constr c) in
  let c = unsafe_to_constr @@ whd_evar sigma c in
  match Constr.kind c with
  | Evar ((evk, _) as ev) ->
    let args = Evd.expand_existential0 sigma ev in
    List.iter (fun c -> f c) args
  | _ -> Constr.iter f c

let expand_case env _sigma (ci, u, pms, p, iv, c, bl) =
  let u = EInstance.unsafe_to_instance u in
  let pms = unsafe_to_constr_array pms in
  let p = unsafe_to_return p in
  let iv = unsafe_to_case_invert iv in
  let c = unsafe_to_constr c in
  let bl = unsafe_to_branches bl in
  let (ci, (p,r), iv, c, bl) = Inductive.expand_case env (ci, u, pms, p, iv, c, bl) in
  let p = of_constr p in
  let r = ERelevance.make r in
  let c = of_constr c in
  let iv = of_case_invert iv in
  let bl = of_constr_array bl in
  (ci, (p,r), iv, c, bl)

let annotate_case env sigma (ci, u, pms, p, iv, c, bl as case) =
  let (_, (p,r), _, _, bl) = expand_case env sigma case in
  let p =
    (* Too bad we need to fetch this data in the environment, should be in the
      case_info instead. *)
    let (_, mip) = Inductive.lookup_mind_specif env ci.ci_ind in
    decompose_lambda_n_decls sigma (mip.Declarations.mind_nrealdecls + 1) p
  in
  let mk_br c n = decompose_lambda_n_decls sigma n c in
  let bl = Array.map2 mk_br bl ci.ci_cstr_ndecls in
  (ci, u, pms, (p,r), iv, c, bl)

let expand_branch env _sigma u pms (ind, i) (nas, _br) =
  let open Declarations in
  let u = EInstance.unsafe_to_instance u in
  let pms = unsafe_to_constr_array pms in
  let (mib, mip) = Inductive.lookup_mind_specif env ind in
  let paramdecl = Vars.subst_instance_context u mib.mind_params_ctxt in
  let paramsubst = Vars.subst_of_rel_context_instance paramdecl pms in
  let (ctx, _) = mip.mind_nf_lc.(i - 1) in
  let (ctx, _) = List.chop mip.mind_consnrealdecls.(i - 1) ctx in
  let nas =
    let gen : type a b. (a,b) eq -> (_,a) Context.pbinder_annot array ->
      (_,b) Context.pbinder_annot array =
      fun Refl x -> x
    in
    gen unsafe_relevance_eq nas
  in
  let ans = Inductive.instantiate_context u paramsubst nas ctx in
  let ans : rel_context =
    match Evd.MiniEConstr.(unsafe_eq, unsafe_relevance_eq) with
    | Refl, Refl -> ans
  in
  ans

let contract_case env _sigma (ci, (p,r), iv, c, bl) =
  let p = unsafe_to_constr p in
  let r = ERelevance.unsafe_to_relevance r in
  let iv = unsafe_to_case_invert iv in
  let c = unsafe_to_constr c in
  let bl = unsafe_to_constr_array bl in
  let (ci, u, pms, p, iv, c, bl) = Inductive.contract_case env (ci, (p,r), iv, c, bl) in
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
    | Construct _ | Int _ | Float _ | String _) -> ()
  | Cast (c,_,t) -> f n c; f n t
  | Prod (na,t,c) -> f n t; f (g (LocalAssum (na, t)) n) c
  | Lambda (na,t,c) -> f n t; f (g (LocalAssum (na, t)) n) c
  | LetIn (na,b,t,c) -> f n b; f n t; f (g (LocalDef (na, b, t)) n) c
  | App (c,l) -> f n c; Array.Fun1.iter f n l
  | Evar ((_,l) as ev) ->
    let l = Evd.expand_existential sigma ev in
    List.iter (fun c -> f n c) l
  | Case (ci,u,pms,p,iv,c,bl) ->
    let (ci, _, pms, (p,_), iv, c, bl) = annotate_case env sigma (ci, u, pms, p, iv, c, bl) in
    let f_ctx (ctx, c) = f (List.fold_right g ctx n) c in
    Array.Fun1.iter f n pms; f_ctx p; iter_invert (f n) iv; f n c; Array.iter f_ctx bl
  | Proj (_,_,c) -> f n c
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
  let c = unsafe_to_constr @@ whd_evar sigma c in
  match Constr.kind c with
  | Evar ((evk, _) as ev) ->
    let args = Evd.expand_existential0 sigma ev in
    List.iter (fun c -> f n c) args
  | _ -> Constr.iter_with_binders g f n c

let fold sigma f acc c =
  let f acc c = f acc (of_constr c) in
  let c = unsafe_to_constr @@ whd_evar sigma c in
  match Constr.kind c with
  | Evar ((evk, _) as ev) ->
    let args = Evd.expand_existential0 sigma ev in
    List.fold_left f acc args
  | _ -> Constr.fold f acc c

let fold_with_binders sigma g f e acc c =
  let f e acc c = f e acc (of_constr c) in
  let c = unsafe_to_constr @@ whd_evar sigma c in
  match Constr.kind c with
  | Evar ((evk, _) as ev) ->
    let args = Evd.expand_existential0 sigma ev in
    List.fold_left (fun acc c -> f e acc c) acc args
  | _ -> Constr.fold_constr_with_binders g f e acc c

let compare_gen k eq_inst eq_sort eq_constr eq_evars nargs c1 c2 =
  (c1 == c2) || Constr.compare_head_gen_with k k eq_inst eq_sort eq_constr eq_evars nargs c1 c2

let eq_existential sigma eq (evk1, args1) (evk2, args2) =
  if Evar.equal evk1 evk2 then
    let args1 = Evd.expand_existential sigma (evk1, args1) in
    let args2 = Evd.expand_existential sigma (evk2, args2) in
    List.equal eq args1 args2
  else false

let eq_constr sigma c1 c2 =
  let kind c = kind sigma c in
  let eq_inst _ i1 i2 = EInstance.equal sigma i1 i2 in
  let eq_sorts s1 s2 = ESorts.equal sigma s1 s2 in
  let eq_existential eq e1 e2 = eq_existential sigma (eq 0) e1 e2 in
  let rec eq_constr nargs c1 c2 =
    compare_gen kind eq_inst eq_sorts (eq_existential eq_constr) eq_constr nargs c1 c2
  in
  eq_constr 0 c1 c2

let eq_constr_nounivs sigma c1 c2 =
  let kind c = kind sigma c in
  let eq_existential eq e1 e2 = eq_existential sigma (eq 0) e1 e2 in
  let rec eq_constr nargs c1 c2 =
    compare_gen kind (fun _ _ _ -> true) (fun _ _ -> true) (eq_existential eq_constr) eq_constr nargs c1 c2
  in
  eq_constr 0 c1 c2

let compare_constr sigma cmp c1 c2 =
  let kind c = kind sigma c in
  let eq_inst _ i1 i2 = EInstance.equal sigma i1 i2 in
  let eq_sorts s1 s2 = ESorts.equal sigma s1 s2 in
  let eq_existential eq e1 e2 = eq_existential sigma (eq 0) e1 e2 in
  let cmp nargs c1 c2 = cmp c1 c2 in
  compare_gen kind eq_inst eq_sorts (eq_existential cmp) cmp 0 c1 c2

let cmp_inductives cv_pb (mind,ind as spec) nargs u1 u2 cstrs =
  let open UnivProblem in
  match mind.Declarations.mind_variance with
  | None -> enforce_eq_instances_univs false u1 u2 cstrs
  | Some variances ->
    let num_param_arity = Conversion.inductive_cumulativity_arguments spec in
    if not (Int.equal num_param_arity nargs) then enforce_eq_instances_univs false u1 u2 cstrs
    else compare_cumulative_instances cv_pb  variances u1 u2 cstrs

let cmp_constructors (mind, ind, cns as spec) nargs u1 u2 cstrs =
  let open UnivProblem in
  match mind.Declarations.mind_variance with
  | None -> enforce_eq_instances_univs false u1 u2 cstrs
  | Some _ ->
    let num_cnstr_args = Conversion.constructor_cumulativity_arguments spec in
    if not (Int.equal num_cnstr_args nargs)
    then enforce_eq_instances_univs false u1 u2 cstrs
    else
      let qs1, us1 = UVars.Instance.to_array u1
      and qs2, us2 = UVars.Instance.to_array u2 in
      let cstrs = enforce_eq_qualities qs1 qs2 cstrs in
      Array.fold_left2 (fun cstrs u1 u2 -> UnivProblem.(Set.add (UWeak (u1,u2)) cstrs))
        cstrs us1 us2

let eq_universes env sigma cstrs cv_pb refargs l l' =
  if EInstance.is_empty l then (assert (EInstance.is_empty l'); true)
  else
    let l = EInstance.kind sigma l
    and l' = EInstance.kind sigma l' in
    let open GlobRef in
    let open UnivProblem in
    match refargs with
    | Some (ConstRef c, 1) when Environ.is_array_type env c ->
      cstrs := compare_cumulative_instances cv_pb [|UVars.Variance.Irrelevant|] l l' !cstrs;
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
    let cv_pb = if leq then Conversion.CUMUL else Conversion.CONV in
    let eq_universes refargs l l' = eq_universes env sigma cstrs Conversion.CONV refargs l l'
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
    let eq_existential eq e1 e2 = eq_existential sigma (eq 0) e1 e2 in
    let rec eq_constr' nargs m n = compare_gen kind eq_universes eq_sorts (eq_existential eq_constr') eq_constr' nargs m n in
    let res =
      if leq then
        let rec compare_leq nargs m n =
          Constr.compare_head_gen_leq_with kind kind leq_universes leq_sorts (eq_existential eq_constr')
            eq_constr' leq_constr' nargs m n
        and leq_constr' nargs m n = m == n || compare_leq nargs m n in
        compare_leq nargs m n
      else
        Constr.compare_head_gen_with kind kind eq_universes eq_sorts (eq_existential eq_constr') eq_constr' nargs m n
    in
    if res then Some !cstrs else None

let eq_constr_universes env sigma ?nargs m n =
  test_constr_universes env sigma false ?nargs m n
let leq_constr_universes env sigma ?nargs m n =
  test_constr_universes env sigma true ?nargs m n

let compare_head_gen_proj env sigma equ eqs eqev eqc' nargs m n =
  let kind c = kind sigma c in
  match kind m, kind n with
  | Proj (p, _, c), App (f, args)
  | App (f, args), Proj (p, _, c) ->
      (match kind f with
      | Const (p', u) when Environ.QConstant.equal env (Projection.constant p) p' ->
          let npars = Projection.npars p in
          if Array.length args == npars + 1 then
            eqc' 0 c args.(npars)
          else false
      | _ -> false)
  | _ -> Constr.compare_head_gen_with kind kind equ eqs eqev eqc' nargs m n

let eq_constr_universes_proj env sigma m n =
  let open UnivProblem in
  if m == n then Some Set.empty
  else
    let cstrs = ref Set.empty in
    let eq_universes ref l l' = eq_universes env sigma cstrs Conversion.CONV ref l l' in
    let eq_sorts s1 s2 =
      let s1 = ESorts.kind sigma s1 in
      let s2 = ESorts.kind sigma s2 in
      if Sorts.equal s1 s2 then true
      else
        (cstrs := Set.add
           (UEq (s1, s2)) !cstrs;
         true)
    in
    let eq_existential eq e1 e2 = eq_existential sigma (eq 0) e1 e2 in
    let rec eq_constr' nargs m n =
      m == n || compare_head_gen_proj env sigma eq_universes eq_sorts (eq_existential eq_constr') eq_constr' nargs m n
    in
    let res = eq_constr' 0 m n in
    if res then Some !cstrs else None

let add_universes_of_instance sigma (qs,us) u =
  let u = EInstance.kind sigma u in
  let qs', us' = UVars.Instance.levels u in
  let qs = Sorts.Quality.(Set.fold (fun q qs -> match q with
      | QVar q -> Sorts.QVar.Set.add q qs
      | QConstant _ -> qs)
      qs' qs)
  in
  qs, Univ.Level.Set.union us us'

let add_relevance sigma (qs,us as v) r =
  let open Sorts in
  (* NB this normalizes above_prop to Relevant which makes it disappear *)
  match ERelevance.kind sigma r with
  | Irrelevant | Relevant -> v
  | RelevanceVar q -> QVar.Set.add q qs, us

let univs_and_qvars_visitor sigma =
  let open Univ in
  let visit_sort (qs,us as acc) s =
    match ESorts.kind sigma s with
    | Sorts.Type u ->
      qs, Universe.levels ~init:us u
    | Sorts.QSort (q,u) ->
      Sorts.QVar.Set.add q qs, Universe.levels ~init:us u
    | Sorts.(SProp | Prop | Set) -> acc
  in
  let visit_instance acc u = add_universes_of_instance sigma acc u in
  let visit_relevance acc r = add_relevance sigma acc r in
  {
    Vars.visit_sort = visit_sort;
    visit_instance = visit_instance;
    visit_relevance = visit_relevance;
  }

let universes_of_constr ?(init=Sorts.QVar.Set.empty,Univ.Level.Set.empty) sigma c =
  let visit = univs_and_qvars_visitor sigma in
  let rec aux s c =
    let kc = kind sigma c in
    let s = Vars.visit_kind_univs visit s kc in
    match kc with
    | Evar (k, args) ->
      let concl = Evd.evar_concl (Evd.find_undefined sigma k) in
      fold sigma aux (aux s concl) c
    | _ -> fold sigma aux s c
  in
  aux init c

open Context
open Environ

let cast_list : type a b. (a,b) eq -> a list -> b list =
  fun Refl x -> x

let cast_vect : type a b. (a,b) eq -> a array -> b array =
  fun Refl x -> x

let cast_rel_decl :
  type a b c d. (a,b) eq -> (c,d) eq -> (a, a, c) Rel.Declaration.pt -> (b, b, d) Rel.Declaration.pt =
  fun Refl Refl x -> x

let cast_rel_context :
  type a b c d. (a,b) eq -> (c,d) eq -> (a, a, c) Rel.pt -> (b, b, d) Rel.pt =
  fun Refl Refl x -> x

let cast_rec_decl :
  type a b c d. (a,b) eq -> (c,d) eq -> (a, a, c) Constr.prec_declaration -> (b, b, d) Constr.prec_declaration =
  fun Refl Refl x -> x

let cast_named_decl :
  type a b c d. (a,b) eq -> (c,d) eq -> (a, a, c) Named.Declaration.pt -> (b, b, d) Named.Declaration.pt =
  fun Refl Refl x -> x

let cast_named_context :
  type a b c d. (a,b) eq -> (c,d) eq -> (a, a, c) Named.pt -> (b, b, d) Named.pt =
  fun Refl Refl x -> x


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

type substituend = Vars.substituend
let make_substituend c = Vars.make_substituend (unsafe_to_constr c)
let lift_substituend n s = of_constr (Vars.lift_substituend n s)

let replace_vars = replace_vars

(* (subst_var str t) substitute (Var str) by (Rel 1) in t *)
let subst_var sigma str t = replace_vars sigma [(str, mkRel 1)] t

(* (subst_vars [id1;...;idn] t) substitute (Var idj) by (Rel j) in t *)
let substn_vars sigma p vars c =
  let _,subst =
    List.fold_left (fun (n,l) var -> ((n+1),(var, mkRel n)::l)) (p,[]) vars
  in replace_vars sigma (List.rev subst) c

let subst_vars sigma subst c = substn_vars sigma 1 subst c

let subst_univs_level_constr subst c =
  of_constr (Vars.subst_univs_level_constr subst (to_constr c))

let subst_instance_context subst ctx =
  let subst = EInstance.unsafe_to_instance subst in
  cast_rel_context (sym unsafe_eq) (sym unsafe_relevance_eq) (Vars.subst_instance_context subst (cast_rel_context unsafe_eq unsafe_relevance_eq ctx))

let subst_instance_constr subst c =
  let subst = EInstance.unsafe_to_instance subst in
  of_constr (Vars.subst_instance_constr subst (to_constr c))

let subst_instance_relevance subst r =
  let subst = EInstance.unsafe_to_instance subst in
  let r = ERelevance.unsafe_to_relevance r in
  let r = UVars.subst_instance_relevance subst r in
  ERelevance.make r

(** Operations that dot NOT commute with evar-normalization *)
let noccurn sigma n term =
  let rec occur_rec n h c =
    let (h, knd) = Expand.kind sigma h c in
    match knd with
    | Rel m -> if Int.equal m n then raise LocalOccur
    | Evar (evk, l) ->
      let evi = Evd.find_undefined sigma evk in
      let l = Expand.expand_instance ~skip:true evi h l in
      SList.Skip.iter (fun c -> occur_rec n h c) l
    | _ -> Expand.iter_with_binders sigma succ occur_rec n h knd
  in
  let h, term = Expand.make term in
  try occur_rec n h term; true with LocalOccur -> false

let noccur_between sigma n m term =
  let rec occur_rec n h c =
    let (h, knd) = Expand.kind sigma h c in
    match knd with
    | Rel p -> if n<=p && p<n+m then raise LocalOccur
    | Evar (evk, l) ->
      let evi = Evd.find_undefined sigma evk in
      let l = Expand.expand_instance ~skip:true evi h l in
      SList.Skip.iter (fun c -> occur_rec n h c) l
    | _        -> Expand.iter_with_binders sigma succ occur_rec n h knd
  in
  let h, term = Expand.make term in
  try occur_rec n h term; true with LocalOccur -> false

let closedn sigma n c =
  let rec closed_rec n h c =
    let (h, knd) = Expand.kind sigma h c in
    match knd with
    | Rel m -> if m>n then raise LocalOccur
    | Evar (evk, l) ->
      let evi = Evd.find_undefined sigma evk in
      let l = Expand.expand_instance ~skip:true evi h l in
      SList.Skip.iter (fun c -> closed_rec n h c) l
    | _ -> Expand.iter_with_binders sigma succ closed_rec n h knd
  in
  let h, c = Expand.make c in
  try closed_rec n h c; true with LocalOccur -> false

let closed0 sigma c = closedn sigma 0 c

let subst_of_rel_context_instance ctx subst =
  cast_list (sym unsafe_eq)
    (Vars.subst_of_rel_context_instance (cast_rel_context unsafe_eq unsafe_relevance_eq ctx) (cast_vect unsafe_eq subst))
let subst_of_rel_context_instance_list ctx subst =
  cast_list (sym unsafe_eq)
    (Vars.subst_of_rel_context_instance_list (cast_rel_context unsafe_eq unsafe_relevance_eq ctx) (cast_list unsafe_eq subst))

let liftn_rel_context n k ctx =
  cast_rel_context (sym unsafe_eq) (sym unsafe_relevance_eq)
    (Vars.liftn_rel_context n k (cast_rel_context unsafe_eq unsafe_relevance_eq ctx))

let lift_rel_context n ctx =
  cast_rel_context (sym unsafe_eq) (sym unsafe_relevance_eq)
    (Vars.lift_rel_context n (cast_rel_context unsafe_eq unsafe_relevance_eq ctx))

let substnl_rel_context subst n ctx =
  cast_rel_context (sym unsafe_eq) (sym unsafe_relevance_eq)
    (Vars.substnl_rel_context (cast_list unsafe_eq subst) n (cast_rel_context unsafe_eq unsafe_relevance_eq ctx))

let substl_rel_context subst ctx =
  cast_rel_context (sym unsafe_eq) (sym unsafe_relevance_eq)
    (Vars.substl_rel_context (cast_list unsafe_eq subst) (cast_rel_context unsafe_eq unsafe_relevance_eq ctx))

let smash_rel_context ctx =
  cast_rel_context (sym unsafe_eq) (sym unsafe_relevance_eq)
      (Vars.smash_rel_context (cast_rel_context unsafe_eq unsafe_relevance_eq ctx))

let esubst : (int -> 'a -> t) -> 'a Esubst.subs -> t -> t =
match unsafe_eq with
| Refl -> Vars.esubst

end

(* Constructs either [forall x:t, c] or [let x:=b:t in c] *)
let mkProd_or_LetIn decl c =
  let open Context.Rel.Declaration in
  match decl with
  | LocalAssum (na,t) -> mkProd (na, t, c)
  | LocalDef (na,b,t) -> mkLetIn (na, b, t, c)

(* Constructs either [forall x:t, c] or [c] in which [x] is replaced by [b] *)
let mkProd_wo_LetIn decl c =
  let open Context.Rel.Declaration in
  match decl with
  | LocalAssum (na,t) -> mkProd (na, t, c)
  | LocalDef (_,b,_) -> Vars.subst1 b c

let mkLambda_or_LetIn decl c =
  let open Context.Rel.Declaration in
  match decl with
  | LocalAssum (na,t) -> mkLambda (na, t, c)
  | LocalDef (na,b,t) -> mkLetIn (na, b, t, c)

let mkLambda_wo_LetIn decl c =
  let open Context.Rel.Declaration in
  match decl with
  | LocalAssum (na,t) -> mkLambda (na, t, c)
  | LocalDef (_,b,_) -> Vars.subst1 b c

let mkNamedProd sigma id typ c = mkProd (map_annot Name.mk_name id, typ, Vars.subst_var sigma id.binder_name c)
let mkNamedLambda sigma id typ c = mkLambda (map_annot Name.mk_name id, typ, Vars.subst_var sigma id.binder_name c)
let mkNamedLetIn sigma id c1 t c2 = mkLetIn (map_annot Name.mk_name id, c1, t, Vars.subst_var sigma id.binder_name c2)

let mkNamedProd_or_LetIn sigma decl c =
  let open Context.Named.Declaration in
  match decl with
  | LocalAssum (id,t) -> mkNamedProd sigma id t c
  | LocalDef (id,b,t) -> mkNamedLetIn sigma id b t c

let mkNamedLambda_or_LetIn sigma decl c =
  let open Context.Named.Declaration in
  match decl with
  | LocalAssum (id,t) -> mkNamedLambda sigma id t c
  | LocalDef (id,b,t) -> mkNamedLetIn sigma id b t c

let mkNamedProd_wo_LetIn sigma decl c =
  let open Context.Named.Declaration in
  match decl with
  | LocalAssum (id,t) -> mkNamedProd sigma id t c
  | LocalDef (id,b,t) -> Vars.subst1 b c

let it_mkProd init = List.fold_left (fun c (n,t)  -> mkProd (n, t, c)) init
let it_mkLambda init = List.fold_left (fun c (n,t)  -> mkLambda (n, t, c)) init

let compose_lam l b = it_mkLambda b l

let it_mkProd_or_LetIn t ctx = List.fold_left (fun c d -> mkProd_or_LetIn d c) t ctx
let it_mkLambda_or_LetIn t ctx = List.fold_left (fun c d -> mkLambda_or_LetIn d c) t ctx

let it_mkProd_wo_LetIn t ctx = List.fold_left (fun c d -> mkProd_wo_LetIn d c) t ctx
let it_mkLambda_wo_LetIn t ctx = List.fold_left (fun c d -> mkLambda_wo_LetIn d c) t ctx

let it_mkNamedProd_or_LetIn sigma t ctx = List.fold_left (fun c d -> mkNamedProd_or_LetIn sigma d c) t ctx
let it_mkNamedLambda_or_LetIn sigma t ctx = List.fold_left (fun c d -> mkNamedLambda_or_LetIn sigma d c) t ctx

let it_mkNamedProd_wo_LetIn sigma t ctx = List.fold_left (fun c d -> mkNamedProd_wo_LetIn sigma d c) t ctx

let rec isArity sigma c =
  match kind sigma c with
  | Prod (_,_,c)    -> isArity sigma c
  | LetIn (_,_,_,c) -> isArity sigma c
  | Cast (c,_,_)      -> isArity sigma c
  | Sort _          -> true
  | _               -> false

type arity = rel_context * ESorts.t

let mkArity (ctx, s) = it_mkProd_or_LetIn (mkSort s) ctx

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

let push_rel d e = push_rel (cast_rel_decl unsafe_eq unsafe_relevance_eq d) e
let push_rel_context d e = push_rel_context (cast_rel_context unsafe_eq unsafe_relevance_eq d) e
let push_rec_types d e = push_rec_types (cast_rec_decl unsafe_eq unsafe_relevance_eq d) e
let push_named d e = push_named (cast_named_decl unsafe_eq unsafe_relevance_eq d) e
let push_named_context d e = push_named_context (cast_named_context unsafe_eq unsafe_relevance_eq d) e
let push_named_context_val d e = push_named_context_val (cast_named_decl unsafe_eq unsafe_relevance_eq d) e

let rel_context e = cast_rel_context (sym unsafe_eq) (sym unsafe_relevance_eq) (rel_context e)
let named_context e = cast_named_context (sym unsafe_eq) (sym unsafe_relevance_eq) (named_context e)

let val_of_named_context e = val_of_named_context (cast_named_context unsafe_eq unsafe_relevance_eq e)
let named_context_of_val e = cast_named_context (sym unsafe_eq) (sym unsafe_relevance_eq) (named_context_of_val e)

let of_existential : Constr.existential -> existential =
  let gen : type a b. (a,b) eq -> 'c * b SList.t -> 'c * a SList.t = fun Refl x -> x in
  gen unsafe_eq

let lookup_rel i e = cast_rel_decl (sym unsafe_eq) (sym unsafe_relevance_eq) (lookup_rel i e)
let lookup_named n e = cast_named_decl (sym unsafe_eq) (sym unsafe_relevance_eq) (lookup_named n e)
let lookup_named_val n e = cast_named_decl (sym unsafe_eq) (sym unsafe_relevance_eq) (lookup_named_ctxt n e)

let map_rel_context_in_env f env sign =
  let rec aux env acc = function
    | d::sign ->
        aux (push_rel d env) (Context.Rel.Declaration.map_constr (f env) d :: acc) sign
    | [] ->
        acc
  in
  aux env [] (List.rev sign)

let match_named_context_val :
  named_context_val -> (named_declaration * named_context_val) option =
  match unsafe_eq, unsafe_relevance_eq with
  | Refl, Refl -> match_named_context_val

let identity_subst_val : named_context_val -> t SList.t = fun ctx ->
  SList.defaultn (List.length ctx.Environ.env_named_ctx) SList.empty

let fresh_global ?loc ?rigid ?names env sigma reference =
  let (evd,t) = Evd.fresh_global ?loc ?rigid ?names env sigma reference in
  evd, t

let is_global = isRefX

(** Kind of type *)

type kind_of_type =
  | SortType   of ESorts.t
  | CastType   of types * t
  | ProdType   of Name.t binder_annot * t * t
  | LetInType  of Name.t binder_annot * t * t * t
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
  | (Lambda _ | Construct _ | Int _ | Float _ | String _ | Array _) -> failwith "Not a type"

module Unsafe =
struct
let to_relevance = ERelevance.unsafe_to_relevance
let to_sorts = ESorts.unsafe_to_sorts
let to_instance = EInstance.unsafe_to_instance
let to_constr = unsafe_to_constr
let to_constr_array = unsafe_to_constr_array
let to_binder_annot : 'a binder_annot -> 'a Constr.binder_annot =
  match unsafe_relevance_eq with Refl -> fun x -> x
let to_rel_decl = unsafe_to_rel_decl
let to_named_decl = unsafe_to_named_decl
let to_named_context =
  let gen : type a b c d. (a, b) eq -> (c,d) eq -> (a,a,c) Context.Named.pt -> (b,b,d) Context.Named.pt
    = fun Refl Refl x -> x
  in
  gen unsafe_eq unsafe_relevance_eq
let to_rel_context =
  let gen : type a b c d. (a, b) eq -> (c,d) eq -> (a,a,c) Context.Rel.pt -> (b,b,d) Context.Rel.pt
    = fun Refl Refl x -> x
  in
  gen unsafe_eq unsafe_relevance_eq
let to_case_invert = unsafe_to_case_invert

let eq = unsafe_eq

let relevance_eq = unsafe_relevance_eq
end

module UnsafeMonomorphic = struct
  let mkConst c = of_kind (Const (in_punivs c))
  let mkInd i = of_kind (Ind (in_punivs i))
  let mkConstruct c = of_kind (Construct (in_punivs c))
end

(* deprecated *)

let decompose_lambda_assum = decompose_lambda_decls
let decompose_prod_assum = decompose_prod_decls
let decompose_prod_n_assum = decompose_prod_n_decls
let prod_assum = prod_decls
let decompose_lam = decompose_lambda
let decompose_lam_n_assum = decompose_lambda_n_assum
let decompose_lam_n_decls = decompose_lambda_n_decls
let decompose_lam_assum = decompose_lambda_assum

include UnsafeMonomorphic
