(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pp
open Names
open Constr
open Context
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

let define_pure_evar_as_product env evd na evk =
  let open Context.Named.Declaration in
  let evi = Evd.find_undefined evd evk in
  let evenv = evar_env env evi in
  let id = match na with Some id -> id | None -> idx in
  let id = next_ident_away id (Environ.ids_of_named_context_val (Evd.evar_hyps evi)) in
  let concl = Reductionops.whd_all evenv evd (Evd.evar_concl evi) in
  let s = destSort evd concl in
  let evksrc = evar_source evi in
  let src = subterm_source evk ~where:Domain evksrc in
  let evd1,(dom,u1) =
    new_type_evar evenv evd univ_flexible_alg ~src ~filter:(evar_filter evi)
  in
  let rdom = ESorts.relevance_of_sort u1 in
  let evd2,rng =
    let newenv = push_named (LocalAssum (make_annot id rdom, dom)) evenv in
    let src = subterm_source evk ~where:Codomain evksrc in
    let filter = Filter.extend 1 (evar_filter evi) in
      if Environ.is_impredicative_sort env (ESorts.kind evd1 s) then
       (* Impredicative product, conclusion must fall in [Prop]. *)
        new_evar newenv evd1 concl ~src ~filter
      else
        let status = univ_flexible_alg in
        let evd3, (rng, srng) =
          new_type_evar newenv evd1 status ~src ~filter
        in
        let prods = Typeops.sort_of_product env (ESorts.kind evd3 u1) (ESorts.kind evd3 srng) in
        let evd3 = Evd.set_leq_sort evd3 (ESorts.make prods) s in
          evd3, rng
  in
  let prod = mkProd (make_annot (Name id) rdom, dom, subst_var evd2 id rng) in
  let evd3 = Evd.define evk prod evd2 in
    evd3,prod

(* Refine an applied evar to a product and returns its instantiation *)

let define_evar_as_product env evd ?name (evk,args) =
  let evd,prod = define_pure_evar_as_product env evd name evk in
  (* Quick way to compute the instantiation of evk with args *)
  let na,dom,rng = destProd evd prod in
  let evdom = mkEvar (fst (destEvar evd dom), args) in
  let evrngargs = SList.cons (mkRel 1) (SList.Skip.map (lift 1) args) in
  let evrng =  mkEvar (fst (destEvar evd rng), evrngargs) in
  evd, mkProd (na, evdom, evrng)

(* Refine an evar with an abstraction

   I.e., solve x1..xq |- ?e:T(x1..xq) with e:=λy:A.?e'[x1..xq,y] where:
   - either T(x1..xq) = πy:A(x1..xq).B(x1..xq,y)
     or T(x1..xq) = ?d[x1..xq] and we define ?d := πy:?A.?B
        with x1..xq |- ?A:Type and x1..xq,y |- ?B:Type
   - x1..xq,y:A |- ?e':B
*)

let define_pure_evar_as_lambda env evd name evk =
  let open Context.Named.Declaration in
  let evi = Evd.find_undefined evd evk in
  let evenv = evar_env env evi in
  let typ = Reductionops.whd_all evenv evd (evar_concl evi) in
  let evd1,(na,dom,rng) = match EConstr.kind evd typ with
  | Prod (na,dom,rng) -> (evd,(na,dom,rng))
  | Evar ev' -> let evd,typ = define_evar_as_product env evd ?name ev' in evd,destProd evd typ
  | _ -> error_not_product env evd typ in
  let avoid = Environ.ids_of_named_context_val (Evd.evar_hyps evi) in
  let id =
    map_annot (fun na -> next_name_away_with_default_using_types "x" na avoid
      (Reductionops.whd_evar evd dom)) na
  in
  let newenv = push_named (LocalAssum (id, dom)) evenv in
  let filter = Filter.extend 1 (evar_filter evi) in
  let src = subterm_source evk ~where:Body (evar_source evi) in
  let abstract_arguments = Abstraction.abstract_last (Evd.evar_abstract_arguments evi) in
  let evd2,body = new_evar newenv evd1 ~src (subst1 (mkVar id.binder_name) rng) ~filter ~abstract_arguments in
  let lam = mkLambda (map_annot Name.mk_name id, dom, subst_var evd2 id.binder_name body) in
  Evd.define evk lam evd2, lam

let define_evar_as_lambda env evd ?name (evk,args) =
  let evd,lam = define_pure_evar_as_lambda env evd name evk in
  (* Quick way to compute the instantiation of evk with args *)
  let na,dom,body = destLambda evd lam in
  let evbodyargs = SList.cons (mkRel 1) (SList.Skip.map (lift 1) args) in
  let evbody = mkEvar (fst (destEvar evd body), evbodyargs) in
  evd, mkLambda (na, dom, evbody)

let rec evar_absorb_arguments env evd (evk,args as ev) = function
  | [] -> evd,ev
  | a::l ->
      (* TODO: optimize and avoid introducing intermediate evars *)
      let evd,lam = define_pure_evar_as_lambda env evd None evk in
      let _,_,body = destLambda evd lam in
      let evk = fst (destEvar evd body) in
      evar_absorb_arguments env evd (evk, SList.cons a args) l

(* Refining an evar to a sort *)

let define_evar_as_sort env evd (ev,args) =
  let evd, s = new_sort_variable univ_rigid evd in
  let evi = Evd.find_undefined evd ev in
  let concl = Reductionops.whd_all (evar_env env evi) evd (Evd.evar_concl evi) in
  let sort = destSort evd concl in
  let evd' = Evd.define ev (mkSort s) evd in
  Evd.set_leq_sort evd' (ESorts.super evd' s) sort, s

(* Unify with unknown array *)

let rec presplit env sigma c =
  let c = Reductionops.whd_all env sigma c in
  match EConstr.kind sigma c with
  | App (h,args) when isEvar sigma h ->
    let sigma, lam = define_evar_as_lambda env sigma (destEvar sigma h) in
    (* XXX could be just whd_all -> no recursion? *)
    presplit env sigma (mkApp (lam, args))
  | _ -> sigma, c

let define_pure_evar_as_array env sigma evk =
  let evi = Evd.find_undefined sigma evk in
  let evenv = evar_env env evi in
  let evksrc = evar_source evi in
  let src = subterm_source evk ~where:Domain evksrc in
  let sigma, u = new_univ_level_variable univ_flexible sigma in
  let s' = ESorts.make @@ Sorts.sort_of_univ @@ Univ.Universe.make u in
  let sigma, ty = new_evar evenv sigma ~typeclass_candidate:false ~src ~filter:(evar_filter evi) (mkSort s') in
  let concl = Reductionops.whd_all evenv sigma (Evd.evar_concl evi) in
  let s = destSort sigma concl in
  (* array@{u} ty : Type@{u} <= Type@{s} *)
  let sigma = Evd.set_leq_sort sigma s' s in
  let ar = Typeops.type_of_array env (UVars.Instance.of_array ([||],[|u|])) in
  let sigma = Evd.define evk (mkApp (EConstr.of_constr ar, [| ty |])) sigma in
  sigma

let is_array_const env sigma c =
  match EConstr.kind sigma c with
  | Const (cst,_) ->
    (match (Environ.retroknowledge env).Retroknowledge.retro_array with
     | None -> false
     | Some cst' -> Environ.QConstant.equal env cst cst')
  | _ -> false

let split_as_array env sigma0 = function
  | None -> sigma0, None
  | Some c ->
    let sigma, c = presplit env sigma0 c in
    match EConstr.kind sigma c with
    | App (h,[|ty|]) when is_array_const env sigma h -> sigma, Some ty
    | Evar ev ->
      let sigma = define_pure_evar_as_array env sigma (fst ev) in
      let ty = match EConstr.kind sigma c with
        | App (_,[|ty|]) -> ty
        | _ -> assert false
      in
      sigma, Some ty
    | _ -> sigma0, None

let valcon_of_tycon x = x
let lift_tycon n = Option.map (lift n)

let pr_tycon env sigma = function
    None -> str "None"
  | Some t -> Termops.Internal.print_constr_env env sigma t
