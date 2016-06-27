(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Util
open Pp
open Names
open Term
open Vars
open Termops
open Namegen
open Environ
open Evd
open Evarutil
open Pretype_errors
open Sigma.Notations

let new_evar_unsafe env evd ?src ?filter ?candidates ?store ?naming ?principal typ =
  let evd = Sigma.Unsafe.of_evar_map evd in
  let Sigma (evk, evd, _) = new_evar env evd ?src ?filter ?candidates ?store ?naming ?principal typ in
  (Sigma.to_evar_map evd, evk)

let env_nf_evar sigma env =
  let open Context.Rel.Declaration in
  process_rel_context
    (fun d e -> push_rel (map_constr (nf_evar sigma) d) e) env

let env_nf_betaiotaevar sigma env =
  let open Context.Rel.Declaration in
  process_rel_context
    (fun d e ->
      push_rel (map_constr (Reductionops.nf_betaiota sigma) d) e) env

(****************************************)
(* Operations on value/type constraints *)
(****************************************)

type type_constraint = types option

type val_constraint = constr option

(* Old comment...
 * Basically, we have the following kind of constraints (in increasing
 * strength order):
 *   (false,(None,None)) -> no constraint at all
 *   (true,(None,None))  -> we must build a judgement which _TYPE is a kind
 *   (_,(None,Some ty))  -> we must build a judgement which _TYPE is ty
 *   (_,(Some v,_))      -> we must build a judgement which _VAL is v
 * Maybe a concrete datatype would be easier to understand.
 * We differentiate (true,(None,None)) from (_,(None,Some Type))
 * because otherwise Case(s) would be misled, as in
 * (n:nat) Case n of bool [_]nat end  would infer the predicate Type instead
 * of Set.
 *)

(* The empty type constraint *)
let empty_tycon = None

(* Builds a type constraint *)
let mk_tycon ty = Some ty

(* Constrains the value of a type *)
let empty_valcon = None

(* Builds a value constraint *)
let mk_valcon c = Some c

let idx = Namegen.default_dependent_ident

(* Refining an evar to a product *)

let define_pure_evar_as_product evd evk =
  let open Context.Named.Declaration in
  let evi = Evd.find_undefined evd evk in
  let evenv = evar_env evi in
  let id = next_ident_away idx (ids_of_named_context (evar_context evi)) in
  let concl = Reductionops.whd_betadeltaiota evenv evd evi.evar_concl in
  let s = destSort concl in
  let evd1,(dom,u1) =
    let evd = Sigma.Unsafe.of_evar_map evd in
    let Sigma (e, evd1, _) = new_type_evar evenv evd univ_flexible_alg ~filter:(evar_filter evi) in
    (Sigma.to_evar_map evd1, e)
  in
  let evd2,rng =
    let newenv = push_named (LocalAssum (id, dom)) evenv in
    let src = evar_source evk evd1 in
    let filter = Filter.extend 1 (evar_filter evi) in
      if is_prop_sort s then
       (* Impredicative product, conclusion must fall in [Prop]. *)
        new_evar_unsafe newenv evd1 concl ~src ~filter
      else
	let status = univ_flexible_alg in
	let evd3, (rng, srng) =
          let evd1 = Sigma.Unsafe.of_evar_map evd1 in
          let Sigma (e, evd3, _) = new_type_evar newenv evd1 status ~src ~filter in
          (Sigma.to_evar_map evd3, e)
        in
	let prods = Univ.sup (univ_of_sort u1) (univ_of_sort srng) in
	let evd3 = Evd.set_leq_sort evenv evd3 (Type prods) s in
	  evd3, rng
  in
  let prod = mkProd (Name id, dom, subst_var id rng) in
  let evd3 = Evd.define evk prod evd2 in
    evd3,prod

(* Refine an applied evar to a product and returns its instantiation *)

let define_evar_as_product evd (evk,args) =
  let evd,prod = define_pure_evar_as_product evd evk in
  (* Quick way to compute the instantiation of evk with args *)
  let na,dom,rng = destProd prod in
  let evdom = mkEvar (fst (destEvar dom), args) in
  let evrngargs = Array.cons (mkRel 1) (Array.map (lift 1) args) in
  let evrng =  mkEvar (fst (destEvar rng), evrngargs) in
  evd,mkProd (na, evdom, evrng)

(* Refine an evar with an abstraction

   I.e., solve x1..xq |- ?e:T(x1..xq) with e:=λy:A.?e'[x1..xq,y] where:
   - either T(x1..xq) = πy:A(x1..xq).B(x1..xq,y)
     or T(x1..xq) = ?d[x1..xq] and we define ?d := πy:?A.?B
        with x1..xq |- ?A:Type and x1..xq,y |- ?B:Type
   - x1..xq,y:A |- ?e':B
*)

let define_pure_evar_as_lambda env evd evk =
  let open Context.Named.Declaration in
  let evi = Evd.find_undefined evd evk in
  let evenv = evar_env evi in
  let typ = Reductionops.whd_betadeltaiota evenv evd (evar_concl evi) in
  let evd1,(na,dom,rng) = match kind_of_term typ with
  | Prod (na,dom,rng) -> (evd,(na,dom,rng))
  | Evar ev' -> let evd,typ = define_evar_as_product evd ev' in evd,destProd typ
  | _ -> error_not_product_loc Loc.ghost env evd typ in
  let avoid = ids_of_named_context (evar_context evi) in
  let id =
    next_name_away_with_default_using_types "x" na avoid (Reductionops.whd_evar evd dom) in
  let newenv = push_named (LocalAssum (id, dom)) evenv in
  let filter = Filter.extend 1 (evar_filter evi) in
  let src = evar_source evk evd1 in
  let evd2,body = new_evar_unsafe newenv evd1 ~src (subst1 (mkVar id) rng) ~filter in
  let lam = mkLambda (Name id, dom, subst_var id body) in
  Evd.define evk lam evd2, lam

let define_evar_as_lambda env evd (evk,args) =
  let evd,lam = define_pure_evar_as_lambda env evd evk in
  (* Quick way to compute the instantiation of evk with args *)
  let na,dom,body = destLambda lam in
  let evbodyargs = Array.cons (mkRel 1) (Array.map (lift 1) args) in
  let evbody = mkEvar (fst (destEvar body), evbodyargs) in
  evd,mkLambda (na, dom, evbody)

let rec evar_absorb_arguments env evd (evk,args as ev) = function
  | [] -> evd,ev
  | a::l ->
      (* TODO: optimize and avoid introducing intermediate evars *)
      let evd,lam = define_pure_evar_as_lambda env evd evk in
      let _,_,body = destLambda lam in
      let evk = fst (destEvar body) in
      evar_absorb_arguments env evd (evk, Array.cons a args) l

(* Refining an evar to a sort *)

let define_evar_as_sort env evd (ev,args) =
  let evd, u = new_univ_variable univ_rigid evd in
  let evi = Evd.find_undefined evd ev in 
  let s = Type u in
  let concl = Reductionops.whd_betadeltaiota (evar_env evi) evd evi.evar_concl in
  let sort = destSort concl in
  let evd' = Evd.define ev (mkSort s) evd in
  Evd.set_leq_sort env evd' (Type (Univ.super u)) sort, s

(* Propagation of constraints through application and abstraction:
   Given a type constraint on a functional term, returns the type
   constraint on its domain and codomain. If the input constraint is
   an evar instantiate it with the product of 2 new evars. *)

let split_tycon loc env evd tycon =
  let rec real_split evd c =
    let t = Reductionops.whd_betadeltaiota env evd c in
      match kind_of_term t with
	| Prod (na,dom,rng) -> evd, (na, dom, rng)
	| Evar ev (* ev is undefined because of whd_betadeltaiota *) ->
	    let (evd',prod) = define_evar_as_product evd ev in
	    let (_,dom,rng) = destProd prod in
	      evd',(Anonymous, dom, rng)
	| App (c,args) when isEvar c ->
	    let (evd',lam) = define_evar_as_lambda env evd (destEvar c) in
	    real_split evd' (mkApp (lam,args))
	| _ -> error_not_product_loc loc env evd c
  in
    match tycon with
      | None -> evd,(Anonymous,None,None)
      | Some c ->
	  let evd', (n, dom, rng) = real_split evd c in
	    evd', (n, mk_tycon dom, mk_tycon rng)

let valcon_of_tycon x = x
let lift_tycon n = Option.map (lift n)

let pr_tycon env = function
    None -> str "None"
  | Some t -> Termops.print_constr_env env t
