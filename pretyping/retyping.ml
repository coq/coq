(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Util
open Term
open Inductive
open Names
open Reduction
open Environ
open Typeops

type metamap = (int * constr) list

let outsort env sigma t =
  match kind_of_term (whd_betadeltaiota env sigma t) with
    | IsSort s -> s
    | _ -> anomaly "Retyping: found a type of type which is not a sort"

let rec subst_type env sigma typ = function
  | [] -> typ
  | h::rest ->
      match kind_of_term (whd_betadeltaiota env sigma typ) with
        | IsProd (na,c1,c2) -> 
	    subst_type (push_rel_assum (na,c1) env) sigma (subst1 h c2) rest
        | _ -> anomaly "Non-functional construction"

(* Si ft est le type d'un terme f, lequel est appliqué à args, *)
(* [sort_of_atomic_ty] calcule ft[args] qui doit être une sorte *)
(* On suit une méthode paresseuse, en espèrant que ft est une arité *)
(* et sinon on substitue *)

let sort_of_atomic_type env sigma ft args =
  let rec concl_of_arity env ar =
    match kind_of_term (whd_betadeltaiota env sigma ar) with
      | IsProd (na, t, b) -> concl_of_arity (push_rel_assum (na,t) env) b
      | IsSort s -> s
      | _ -> outsort env sigma (subst_type env sigma ft (Array.to_list args))
  in concl_of_arity env ft

let typeur sigma metamap =
  let rec type_of env cstr=
    match kind_of_term cstr with
    | IsMeta n ->
          (try strip_outer_cast (List.assoc n metamap)
           with Not_found -> anomaly "type_of: this is not a well-typed term")
    | IsRel n -> lift n (body_of_type (snd (lookup_rel_type n env)))
    | IsVar id ->
      (try body_of_type (snd (lookup_named id env))
       with Not_found ->
         anomaly ("type_of: variable "^(string_of_id id)^" unbound"))
    | IsConst c -> body_of_type (type_of_constant env sigma c)
    | IsEvar ev -> type_of_existential env sigma ev
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
          mkProd (name, c1, type_of (push_rel_assum (name,c1) env) c2)
    | IsLetIn (name,b,c1,c2) ->
         subst1 b (type_of (push_rel_def (name,b,c1) env) c2)
    | IsFix ((_,i),(_,tys,_)) -> tys.(i)
    | IsCoFix (i,(_,tys,_)) -> tys.(i)
    | IsApp(f,args)->
        strip_outer_cast
          (subst_type env sigma (type_of env f) (Array.to_list args))
    | IsCast (c,t) -> t
    | IsSort _ | IsProd (_,_,_) | IsMutInd _ -> mkSort (sort_of env cstr)

  and sort_of env t = 
    match kind_of_term t with
    | IsCast (c,s) when isSort s -> destSort s
    | IsSort (Prop c) -> type_0
    | IsSort (Type u) -> Type (fst (Univ.super u))
    | IsProd (name,t,c2) ->
        (match (sort_of (push_rel_assum (name,t) env) c2) with
	  | Prop _ as s -> s
	  | Type u2 as s -> s (*Type Univ.dummy_univ*))
    | IsApp(f,args) -> sort_of_atomic_type env sigma (type_of env f) args
    | IsLambda _ | IsFix _ | IsMutConstruct _ ->
        anomaly "sort_of: Not a type (1)"
    | _ -> outsort env sigma (type_of env t)

  and sort_family_of env t =
    match kind_of_term (whd_betadeltaiota env sigma t) with
    | IsCast (c,s) when isSort s -> family_of_sort (destSort s)
    | IsSort (Prop c) -> InType
    | IsSort (Type u) -> InType
    | IsProd (name,t,c2) -> sort_family_of (push_rel_assum (name,t) env) c2
    | IsApp(f,args) -> 
       family_of_sort (sort_of_atomic_type env sigma (type_of env f) args)
    | IsLambda _ | IsFix _ | IsMutConstruct _ ->
        anomaly "sort_of: Not a type (1)"
    | _ -> family_of_sort (outsort env sigma (type_of env t))

  in type_of, sort_of, sort_family_of

let get_type_of env sigma c = let f,_,_ = typeur sigma [] in f env c
let get_sort_of env sigma t = let _,f,_ = typeur sigma [] in f env t
let get_sort_family_of env sigma c = let _,_,f = typeur sigma [] in f env c

let get_type_of_with_meta env sigma metamap = 
  let f,_,_ = typeur sigma metamap in f env

(* Makes an assumption from a constr *)
let get_assumption_of env evc c = c

(* Makes an unsafe judgment from a constr *)
let get_judgment_of env evc c = { uj_val = c; uj_type = get_type_of env evc c }

