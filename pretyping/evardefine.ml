(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Sorts
open Util
open Pp
open Names
open Constr
open Termops
open EConstr
open Vars
open Namegen
open Evd
open Evarutil
open Evar_kinds
open Pretype_errors

module RelDecl = Context.Rel.Declaration

let env_nf_evar sigma env =
  let nf_evar c = nf_evar sigma c in
  process_rel_context
    (fun d e -> push_rel (RelDecl.map_constr nf_evar d) e) env

let env_nf_betaiotaevar sigma env =
  process_rel_context
    (fun d env ->
      push_rel (RelDecl.map_constr (fun c -> Reductionops.nf_betaiota env sigma c) d) env) env

(****************************************)
(* Operations on value/type constraints *)
(****************************************)

type type_constraint = EConstr.types option

type val_constraint = EConstr.constr option

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
  let id = next_ident_away idx (Environ.ids_of_named_context_val evi.evar_hyps) in
  let concl = Reductionops.whd_all evenv evd evi.evar_concl in
  let s = destSort evd concl in
  let evksrc = evar_source evk evd in
  let src = subterm_source evk ~where:Domain evksrc in
  let evd1,(dom,u1) =
    new_type_evar evenv evd univ_flexible_alg ~src ~filter:(evar_filter evi)
  in
  let evd2,rng =
    let newenv = push_named (LocalAssum (id, dom)) evenv in
    let src = subterm_source evk ~where:Codomain evksrc in
    let filter = Filter.extend 1 (evar_filter evi) in
      if Sorts.is_prop (ESorts.kind evd1 s) then
       (* Impredicative product, conclusion must fall in [Prop]. *)
        new_evar newenv evd1 concl ~src ~filter
      else
	let status = univ_flexible_alg in
	let evd3, (rng, srng) =
          new_type_evar newenv evd1 status ~src ~filter
        in
	let prods = Univ.sup (univ_of_sort u1) (univ_of_sort srng) in
	let evd3 = Evd.set_leq_sort evenv evd3 (Type prods) (ESorts.kind evd1 s) in
	  evd3, rng
  in
  let prod = mkProd (Name id, dom, subst_var id rng) in
  let evd3 = Evd.define evk prod evd2 in
    evd3,prod

(* Refine an applied evar to a product and returns its instantiation *)

let define_evar_as_product evd (evk,args) =
  let evd,prod = define_pure_evar_as_product evd evk in
  (* Quick way to compute the instantiation of evk with args *)
  let na,dom,rng = destProd evd prod in
  let evdom = mkEvar (fst (destEvar evd dom), args) in
  let evrngargs = Array.cons (mkRel 1) (Array.map (lift 1) args) in
  let evrng =  mkEvar (fst (destEvar evd rng), evrngargs) in
  evd, mkProd (na, evdom, evrng)

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
  let typ = Reductionops.whd_all evenv evd (evar_concl evi) in
  let evd1,(na,dom,rng) = match EConstr.kind evd typ with
  | Prod (na,dom,rng) -> (evd,(na,dom,rng))
  | Evar ev' -> let evd,typ = define_evar_as_product evd ev' in evd,destProd evd typ
  | _ -> error_not_product env evd typ in
  let avoid = Environ.ids_of_named_context_val evi.evar_hyps in
  let id =
    next_name_away_with_default_using_types "x" na avoid (Reductionops.whd_evar evd dom) in
  let newenv = push_named (LocalAssum (id, dom)) evenv in
  let filter = Filter.extend 1 (evar_filter evi) in
  let src = subterm_source evk ~where:Body (evar_source evk evd1) in
  let evd2,body = new_evar newenv evd1 ~src (subst1 (mkVar id) rng) ~filter in
  let lam = mkLambda (Name id, dom, subst_var id body) in
  Evd.define evk lam evd2, lam

let define_evar_as_lambda env evd (evk,args) =
  let evd,lam = define_pure_evar_as_lambda env evd evk in
  (* Quick way to compute the instantiation of evk with args *)
  let na,dom,body = destLambda evd lam in
  let evbodyargs = Array.cons (mkRel 1) (Array.map (lift 1) args) in
  let evbody = mkEvar (fst (destEvar evd body), evbodyargs) in
  evd, mkLambda (na, dom, evbody)

let rec evar_absorb_arguments env evd (evk,args as ev) = function
  | [] -> evd,ev
  | a::l ->
      (* TODO: optimize and avoid introducing intermediate evars *)
      let evd,lam = define_pure_evar_as_lambda env evd evk in
      let _,_,body = destLambda evd lam in
      let evk = fst (destEvar evd body) in
      evar_absorb_arguments env evd (evk, Array.cons a args) l

(* Refining an evar to a sort *)

let define_evar_as_sort env evd (ev,args) =
  let evd, u = new_univ_variable univ_rigid evd in
  let evi = Evd.find_undefined evd ev in 
  let s = Type u in
  let concl = Reductionops.whd_all (evar_env evi) evd evi.evar_concl in
  let sort = destSort evd concl in
  let evd' = Evd.define ev (mkSort s) evd in
  Evd.set_leq_sort env evd' (Type (Univ.super u)) (ESorts.kind evd' sort), s

(* Propagation of constraints through application and abstraction:
   Given a type constraint on a functional term, returns the type
   constraint on its domain and codomain. If the input constraint is
   an evar instantiate it with the product of 2 new evars. *)

let split_tycon ?loc env evd tycon =
  let rec real_split evd c =
    let t = Reductionops.whd_all env evd c in
      match EConstr.kind evd t with
	| Prod (na,dom,rng) -> evd, (na, dom, rng)
	| Evar ev (* ev is undefined because of whd_all *) ->
	    let (evd',prod) = define_evar_as_product evd ev in
	    let (_,dom,rng) = destProd evd prod in
	      evd',(Anonymous, dom, rng)
	| App (c,args) when isEvar evd c ->
	    let (evd',lam) = define_evar_as_lambda env evd (destEvar evd c) in
	    real_split evd' (mkApp (lam,args))
	| _ -> error_not_product ?loc env evd c
  in
    match tycon with
      | None -> evd,(Anonymous,None,None)
      | Some c ->
	  let evd', (n, dom, rng) = real_split evd c in
	    evd', (n, mk_tycon dom, mk_tycon rng)

let valcon_of_tycon x = x
let lift_tycon n = Option.map (lift n)

let pr_tycon env sigma = function
    None -> str "None"
  | Some t -> Termops.Internal.print_constr_env env sigma t
