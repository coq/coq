
(* $Id$ *)

open Util
open Term
open Inductive
open Names
open Generic
open Reduction
open Environ
open Typeops

(* A light version of mind_specif_of_mind *)

type mutind_id = inductive_path * constr array

type mutind =
    {fullmind : constr;
     mind : mutind_id;
     nparams : int;
     nrealargs : int;
     nconstr : int;
     params : constr list;
     realargs : constr list;
     arity : constr}

(* raise Induc if not an inductive type *)
let try_mutind_of env sigma ty =
  let (mind,largs) = find_mrectype env sigma ty in
  let mispec = lookup_mind_specif mind env in 
  let nparams = mis_nparams mispec in
  let (params,realargs) = list_chop nparams largs in 
  {fullmind = ty;
   mind     = (let (sp,i,cv) = destMutInd mind in (sp,i),cv);
   nparams  = nparams;
   nrealargs = List.length realargs;
   nconstr  = mis_nconstr mispec;
   params   = params;
   realargs = realargs;
   arity    = Instantiate.mis_arity mispec}


(********  A light version of type_of *********)
type metamap = (int * constr) list

let rec is_dep_case env sigma (pt,ar) =
  match whd_betadeltaiota env sigma pt,whd_betadeltaiota env sigma ar with
      DOP2(Prod,_,DLAM(_,t1)),DOP2(Prod,_,DLAM(_,t2)) ->
	is_dep_case env sigma (t1,t2) 
    | DOP2(Prod,_,DLAM(_,_)),ki -> true
    | k,ki   -> false

let outsort env sigma t =
  match whd_betadeltaiota env sigma t with
      DOP0(Sort s) -> s
    | _ -> anomaly "outsort: Not a sort"

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
    | IsVar id -> body_of_type (snd (lookup_var id env))

    | IsAbst _ -> error "No more Abst" (*type_of env (abst_value cstr)*)
    | IsConst _ -> (body_of_type (type_of_constant env sigma cstr))
    | IsEvar _ -> type_of_existential env sigma cstr
    | IsMutInd _ -> (body_of_type (type_of_inductive env sigma cstr))
    | IsMutConstruct (sp,i,j,args) -> 
        let (typ,kind) =
	  destCast (type_of_constructor env sigma (((sp,i),j),args))
        in typ
    | IsMutCase (_,p,c,lf) ->
        let {realargs=args;arity=arity;nparams=n} =
          try try_mutind_of env sigma (type_of env c)
          with Induc -> anomaly "type_of: Bad inductive" in
        let (_,ar) = decomp_n_prod env sigma n arity in
        let al =
          if is_dep_case env sigma (type_of env p,ar) 
	  then args@[c] else args in
        whd_betadeltaiota env sigma (applist (p,al))
    | IsLambda (name,c1,c2) ->
        let var = make_typed c1 (sort_of env c1) in
          mkProd name c1 (type_of (push_rel (name,var) env) c2)
    | IsFix (vn,i,lar,lfi,vdef) -> lar.(i)
    | IsCoFix (i,lar,lfi,vdef) -> lar.(i)

    | IsAppL(f,args)-> strip_outer_cast (subst_type env sigma (type_of env f) args)
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

let get_type_of env sigma = fst (typeur sigma []) env
let get_sort_of env sigma = snd (typeur sigma []) env
let get_type_of_with_meta env sigma metamap = fst (typeur sigma metamap) env
