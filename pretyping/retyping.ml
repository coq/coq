
(* $Id$ *)

open Util
open Term
open Inductive
open Names
open Generic
open Reduction
open Environ
open Typeops

type metamap = (int * constr) list

let outsort env sigma t =
  match whd_betadeltaiota env sigma t with
      DOP0(Sort s) -> s
    | _ -> anomaly "Retyping: found a type of type which is not a sort"

let rec subst_type env sigma typ = function
    [] -> typ
  | h::rest ->
      match whd_betadeltaiota env sigma typ with
          DOP2(Prod,c1,DLAM(_,c2)) -> subst_type env sigma (subst1 h c2) rest
        | _ -> anomaly "Non-functional construction"

(* Si ft est le type d'un terme f, lequel est appliqué à args, *)
(* [sort_of_atomic_ty] calcule ft[args] qui doit être une sorte *)
(* On suit une méthode paresseuse, en espèrant que ft est une arité *)
(* et sinon on substitue *)

let sort_of_atomic_type env sigma ft args =
  let rec concl_of_arity ar =
    match whd_betadeltaiota env sigma ar with
      | DOP2 (Prod, _, DLAM (_, b)) -> concl_of_arity b
      | DOP0 (Sort s) -> s
      | _ -> outsort env sigma (subst_type env sigma ft args)
  in concl_of_arity ft

let typeur sigma metamap =
let rec type_of env cstr=
  match kind_of_term cstr with
      IsMeta n ->
          (try strip_outer_cast (List.assoc n metamap)
           with Not_found -> anomaly "type_of: this is not a well-typed term")
    | IsRel n -> lift n (body_of_type (snd (lookup_rel n env)))
    | IsVar id ->
      (try body_of_type (snd (lookup_var id env))
       with Not_found ->
         anomaly ("type_of: variable "^(string_of_id id)^" unbound"))
    | IsAbst _ -> error "No more Abst" (*type_of env (abst_value cstr)*)
    | IsConst c -> body_of_type (type_of_constant env sigma c)
    | IsEvar _ -> type_of_existential env sigma cstr
    | IsMutInd ind -> body_of_type (type_of_inductive env sigma ind)
    | IsMutConstruct cstr -> body_of_type (type_of_constructor env sigma cstr)
    | IsMutCase (_,p,c,lf) ->
        let IndType (indf,realargs) =
          try find_rectype env sigma (type_of env c)
          with Induc -> anomaly "type_of: Bad recursive type" in
	let (aritysign,_) = get_arity indf in
	let (psign,_) = splay_prod env sigma (type_of env p) in
        let al =
	  if List.length psign > List.length aritysign
	  then realargs@[c] else realargs in
        whd_betadeltaiota env sigma (applist (p,al))
    | IsLambda (name,c1,c2) ->
        let var = make_typed c1 (sort_of env c1) in
          mkProd name c1 (type_of (push_rel (name,var) env) c2)
    | IsFix ((vn,i),(lar,lfi,vdef)) -> lar.(i)
    | IsCoFix (i,(lar,lfi,vdef)) -> lar.(i)
    | IsAppL(f,args)->
      strip_outer_cast (subst_type env sigma (type_of env f) args)
    | IsCast (c,t) -> t
    | IsSort _ | IsProd (_,_,_) | IsMutInd _ -> mkSort (sort_of env cstr)
    | _ -> error "type_of: Unexpected constr"

and sort_of env t = 
  match kind_of_term t with
    | IsCast (c,DOP0(Sort s)) -> s
    | IsSort (Prop c) -> type_0
    | IsSort (Type u) -> Type Univ.dummy_univ
    | IsProd (name,t,c2) ->
        let var = make_typed t (sort_of env t) in
        (match (sort_of (push_rel (name,var) env) c2) with
	  | Prop _ as s -> s
	  | Type u2 -> Type Univ.dummy_univ)
    | IsAppL(f,args) -> sort_of_atomic_type env sigma (type_of env f) args
    | IsLambda _ | IsFix _ | IsMutConstruct _ ->
        anomaly "sort_of: Not a type (1)"
    | _ -> outsort env sigma (type_of env t)

in type_of, sort_of

let get_type_of env sigma c = fst (typeur sigma []) env c
let get_sort_of env sigma t = snd (typeur sigma []) env t
let get_type_of_with_meta env sigma metamap = fst (typeur sigma metamap) env

(* Makes an assumption from a constr *)
let get_assumption_of env evc c = make_typed_lazy c (get_sort_of env evc)

(* Makes an unsafe judgment from a constr *)
let get_judgment_of env evc c =
  let typ = get_type_of env evc c in
  { uj_val = c; uj_type = get_assumption_of env evc typ }

