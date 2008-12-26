(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Util
open Term
open Inductive
open Inductiveops
open Names
open Reductionops
open Environ
open Typeops
open Declarations
open Termops

let rec subst_type env sigma typ = function
  | [] -> typ
  | h::rest ->
      match kind_of_term (whd_betadeltaiota env sigma typ) with
        | Prod (na,c1,c2) -> subst_type env sigma (subst1 h c2) rest
        | _ -> anomaly "Non-functional construction"

(* Si ft est le type d'un terme f, lequel est appliqué à args, *)
(* [sort_of_atomic_ty] calcule ft[args] qui doit être une sorte *)
(* On suit une méthode paresseuse, en espèrant que ft est une arité *)
(* et sinon on substitue *)

let sort_of_atomic_type env sigma ft args =
  let rec concl_of_arity env ar =
    match kind_of_term (whd_betadeltaiota env sigma ar) with
    | Prod (na, t, b) -> concl_of_arity (push_rel (na,None,t) env) b
    | Sort s -> s
    | _ -> decomp_sort env sigma (subst_type env sigma ft (Array.to_list args))
  in concl_of_arity env ft

let type_of_var env id =
  try let (_,_,ty) = lookup_named id env in ty
  with Not_found ->
    anomaly ("type_of: variable "^(string_of_id id)^" unbound")

let retype sigma metamap =
  let rec type_of env cstr=
    match kind_of_term cstr with
    | Meta n ->
          (try strip_outer_cast (List.assoc n metamap)
           with Not_found -> anomaly "type_of: this is not a well-typed term")
    | Rel n ->
        let (_,_,ty) = lookup_rel n env in
        lift n ty
    | Var id -> type_of_var env id
    | Const cst -> Typeops.type_of_constant env cst
    | Evar ev -> Evd.existential_type sigma ev
    | Ind ind -> type_of_inductive env ind
    | Construct cstr -> type_of_constructor env cstr
    | Case (_,p,c,lf) ->
        let Inductiveops.IndType(_,realargs) =
          try Inductiveops.find_rectype env sigma (type_of env c)
          with Not_found -> anomaly "type_of: Bad recursive type" in
        let t = whd_beta (applist (p, realargs)) in
        (match kind_of_term (whd_betadeltaiota env sigma (type_of env t)) with
          | Prod _ -> whd_beta (applist (t, [c]))
          | _ -> t)
    | Lambda (name,c1,c2) ->
          mkProd (name, c1, type_of (push_rel (name,None,c1) env) c2)
    | LetIn (name,b,c1,c2) ->
         subst1 b (type_of (push_rel (name,Some b,c1) env) c2)
    | Fix ((_,i),(_,tys,_)) -> tys.(i)
    | CoFix (i,(_,tys,_)) -> tys.(i)
    | App(f,args) when isGlobalRef f ->
	let t = type_of_global_reference_knowing_parameters env f args in
        strip_outer_cast (subst_type env sigma t (Array.to_list args))
    | App(f,args) ->
        strip_outer_cast
          (subst_type env sigma (type_of env f) (Array.to_list args))
    | Cast (c,_, t) -> t
    | Sort _ | Prod _ -> mkSort (sort_of env cstr)

  and sort_of env t = 
    match kind_of_term t with
    | Cast (c,_, s) when isSort s -> destSort s
    | Sort (Prop c) -> type1_sort
    | Sort (Type u) -> Type (Univ.super u)
    | Prod (name,t,c2) ->
        (match (sort_of env t, sort_of (push_rel (name,None,t) env) c2) with
	  | _, (Prop Null as s) -> s
          | Prop _, (Prop Pos as s) -> s
          | Type _, (Prop Pos as s) when
              Environ.engagement env = Some ImpredicativeSet -> s
	  | (Type _, _) | (_, Type _) -> new_Type_sort ()
(*
          | Type u1, Prop Pos -> Type (Univ.sup u1 Univ.type0_univ)
	  | Prop Pos, (Type u2) -> Type (Univ.sup Univ.type0_univ u2)
	  | Prop Null, (Type _ as s) -> s
	  | Type u1, Type u2 -> Type (Univ.sup u1 u2)*))
    | App(f,args) when isGlobalRef f ->
	let t = type_of_global_reference_knowing_parameters env f args in
        sort_of_atomic_type env sigma t args
    | App(f,args) -> sort_of_atomic_type env sigma (type_of env f) args
    | Lambda _ | Fix _ | Construct _ ->
        anomaly "sort_of: Not a type (1)"
    | _ -> decomp_sort env sigma (type_of env t)

  and sort_family_of env t =
    match kind_of_term t with
    | Cast (c,_, s) when isSort s -> family_of_sort (destSort s)
    | Sort (Prop c) -> InType
    | Sort (Type u) -> InType
    | Prod (name,t,c2) -> 
	let s2 = sort_family_of (push_rel (name,None,t) env) c2 in
	if Environ.engagement env <> Some ImpredicativeSet &&
	   s2 = InSet & sort_family_of env t = InType then InType else s2
    | App(f,args) -> 
       family_of_sort (sort_of_atomic_type env sigma (type_of env f) args)
    | Lambda _ | Fix _ | Construct _ ->
        anomaly "sort_of: Not a type (1)"
    | _ -> family_of_sort (decomp_sort env sigma (type_of env t))

  and type_of_global_reference_knowing_parameters env c args =
    let argtyps = Array.map (fun c -> nf_evar sigma (type_of env c)) args in
    match kind_of_term c with
    | Ind ind ->
      let (_,mip) = lookup_mind_specif env ind in
      Inductive.type_of_inductive_knowing_parameters env mip argtyps
    | Const cst ->
      let t = constant_type env cst in
      Typeops.type_of_constant_knowing_parameters env t argtyps
    | Var id -> type_of_var env id
    | Construct cstr -> type_of_constructor env cstr
    | _ -> assert false

  in type_of, sort_of, sort_family_of,
     type_of_global_reference_knowing_parameters

let get_sort_of env sigma t = let _,f,_,_ = retype sigma [] in f env t
let get_sort_family_of env sigma c = let _,_,f,_ = retype sigma [] in f env c
let type_of_global_reference_knowing_parameters env sigma c args =
  let _,_,_,f = retype sigma [] in f env c args

let type_of_global_reference_knowing_conclusion env sigma c conclty =
  let conclty = nf_evar sigma conclty in
  match kind_of_term c with
    | Ind ind ->
        let (_,mip) = Inductive.lookup_mind_specif env ind in
        type_of_inductive_knowing_conclusion env mip conclty
    | Const cst ->
        let t = constant_type env cst in
        (* TODO *)
        Typeops.type_of_constant_knowing_parameters env t [||]
    | Var id -> type_of_var env id
    | Construct cstr -> type_of_constructor env cstr
    | _ -> assert false

(* We are outside the kernel: we take fresh universes *)
(* to avoid tactics and co to refresh universes themselves *)
let get_type_of env sigma c =
  let f,_,_,_ = retype sigma [] in refresh_universes (f env c)

let get_type_of_with_meta env sigma metamap c =
  let f,_,_,_ = retype sigma metamap in refresh_universes (f env c)

(* Makes an assumption from a constr *)
let get_assumption_of env evc c = c

(* Makes an unsafe judgment from a constr *)
let get_judgment_of env evc c = { uj_val = c; uj_type = get_type_of env evc c }

