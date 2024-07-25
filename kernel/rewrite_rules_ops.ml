(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open Univ
open Sorts
open Names
open Constr
open Declarations
open Environ

type pattern_translation_error =
  | UnknownEvar
  | UnknownQVar of QVar.t
  | UnknownLevel of Level.t
  | DuplicatePatVar of Evar.t * Id.t * int * int
  | DuplicateQVar of QVar.t * int * int
  | DuplicateUVar of Level.t * int * int
  | NoHeadSymbol

exception PatternTranslationError of pattern_translation_error


let update_invtbl evk id (curvar, tbl) =
  curvar, (succ curvar, tbl |> Evar.Map.update evk @@ function
  | None -> Some curvar
  | Some k as c when k = curvar -> c
  | Some k ->
      raise (PatternTranslationError (DuplicatePatVar (evk, id, k, curvar))))

let update_invtblu1 ~(alg:bool) lvl (curvaru, alg_vars, tbl) =
  curvaru, (succ curvaru, alg :: alg_vars, tbl |> Level.Map.update lvl @@ function
    | None -> Some curvaru
    | Some k as c when k = curvaru -> c
    | Some k ->
        raise (PatternTranslationError (DuplicateUVar (lvl, k, curvaru))))

let update_invtblq1 qvar (curvarq, tbl) =
  curvarq, (succ curvarq, tbl |> QVar.Map.update qvar @@ function
    | None -> Some curvarq
    | Some k as c when k = curvarq -> c
    | Some k ->
        raise (PatternTranslationError (DuplicateQVar (qvar, k, curvarq))))

let translate_quality_pattern stateq = function
  | PQConstant _ as q -> stateq, q
  | PQVar (_, false) -> stateq, PQVar None
  | PQVar (qvar, true) ->
      let qi, stateq = update_invtblq1 qvar stateq in
      stateq, PQVar (Some qi)

let translate_instance (state, stateq, stateu) (q, u) =
  let stateq, maskq = Array.fold_left_map translate_quality_pattern stateq q in
  let stateu, masku = Array.fold_left_map (fun stateu (lvl, pat) ->
      if pat then
        let ui, stateu = update_invtblu1 ~alg:false lvl stateu in
        stateu, Some ui
      else stateu, None
    ) stateu u
  in
  (state, stateq, stateu), (maskq, masku)

let translate_sort_pattern (st, sq, su as state) = function
  | PSProp | PSSProp | PSSet as sp -> state, sp
  | PSType (lvl, pat) ->
      if pat then
        let ui, su = update_invtblu1 ~alg:true lvl su in
        (st, sq, su), PSType (Some ui)
      else state, PSType None
  | PSQSort ((q, patq), (lvl, patu)) ->
      let sq, bq =
        if patq then
          let qi, sq = update_invtblq1 q sq in
          sq, Some qi
        else sq, None
      in
      let su, ba =
        if patu then
          let ui, su = update_invtblu1 ~alg:true lvl su in
          su, Some ui
        else su, None
      in
      (st, sq, su), PSQSort (bq, ba)


let rec translate_pattern state = function
  | PRel n -> state, (PHRel n, [])
  | PSort (sp, _) ->
      let state, sp = translate_sort_pattern state sp in
      state, (PHSort sp, [])
  | PSymbol (cst, mask) ->
      let state, mask = translate_instance state mask in
      state, (PHSymbol (cst, mask), [])
  | PInd (ind, mask) ->
      let state, mask = translate_instance state mask in
      state, (PHInd (ind, mask), [])
  | PConstr (cstr, mask) ->
      let state, mask = translate_instance state mask in
      state, (PHConstr (cstr, mask), [])
  | PInt i -> state, (PHInt i, [])
  | PFloat f -> state, (PHFloat f, [])
  | PString s -> state, (PHString s, [])
  | PLambda (_, arg, _, bod) ->
      let state, arg = translate_arg_pattern state arg in
      let state, bod = translate_pattern state bod in
      let lambda = begin match bod with PHLambda (args, bod), [] -> PHLambda (Array.append [|arg|] args, bod) | _ -> PHLambda ([|arg|], bod) end in
      state, (lambda, [])
  | PProd (_, arg, _, bod, _, _) ->
      let state, arg = translate_arg_pattern state arg in
      let state, bod = translate_arg_pattern state bod in
      let prod = begin match bod with ERigid (PHProd (args, bod), []) -> PHProd (Array.append [|arg|] args, bod) | _ -> PHProd ([|arg|], bod) end in
      state, (prod, [])
  | PApp (f, arg, _, _) ->
      let state, (head, elims) = translate_pattern state f in
      let state, arg = translate_arg_pattern state arg in
      let elims = begin match elims with PEApp args :: elims -> PEApp (Array.append args [|arg|]) :: elims | _ -> PEApp [|arg|] :: elims end in
      state, (head, elims)
  | PCase (c, ind, _, (ret, _), brs) ->
      let state, (head, elims) = translate_pattern state c in
      let state, ret = translate_arg_pattern state (snd ret) in
      let state, brs = Array.fold_left_map (fun state (_, br) -> translate_arg_pattern state br) state brs in
      state, (head, PECase (ind, ret, brs) :: elims)
  | PProj (c, p, _) ->
      let state, (head, elims) = translate_pattern state c in
      state, (head, PEProj p :: elims)

and translate_pattern_rev state p =
  let state, (h, e) = translate_pattern state p in
  state, (h, List.rev e)

and translate_arg_pattern (st, sq, su as state) = function
  | PVar (evk, Name id) ->
      let i, st = update_invtbl evk id st in
      (st, sq, su), EHole i
  | PVar (_, Anonymous) ->
      state, EHoleIgnored
  | Pat p ->
      let state, p = translate_pattern_rev state p in
      state, ERigid p

let translate_pattern = translate_pattern_rev

let identity_of_ctx (ctx : Constr.rel_context) =
  Context.Rel.instance mkRel 0 ctx

(* relocation of evars into de Bruijn indices *)
let rec evar_subst evmap evd k t =
  match kind t with
  | Evar (evk, inst) -> begin
    match Evar.Map.find_opt evk evmap with
    | None -> raise (PatternTranslationError UnknownEvar)
    | Some n ->
        let head = mkRel (n + k) in
        let (ctx, _, _, _) = Evar.Map.find evk evd in
        let args = identity_of_ctx ctx in
        let inst = inst |> SList.Smart.map (evar_subst evmap evd k) in
        let inst = inst |> SList.to_list |> List.map Option.get in
        let args = Array.map (Vars.substl inst) args in
        mkApp (head, args)
    end
  | _ -> map_with_binders succ (evar_subst evmap evd) k t

let make_usubst (qvmap, uvmap) : UVars.sort_level_subst =
  let qsubst = QVar.Map.map Quality.var qvmap in
  let usubst = Level.Map.map Level.var uvmap in
  qsubst, usubst

let test_qvar env nvarqs q =
  match Sorts.QVar.var_index q with
  | Some n when n < 0 || n > nvarqs -> CErrors.anomaly Pp.(str "Unknown sort variable in rewrite rule.")
  | Some _ -> ()
  | None ->
      if not @@ Sorts.QVar.Set.mem q env.env_qualities then
        raise (PatternTranslationError (UnknownQVar q))

let test_level env nvarus lvl =
  match Univ.Level.var_index lvl with
  | Some n when n < 0 || n > nvarus -> CErrors.anomaly Pp.(str "Unknown universe level variable in rewrite rule")
  | Some _ -> ()
  | None ->
      match UGraph.check_declared_universes (Environ.universes env) (Univ.Level.Set.singleton lvl) with
      | Ok () -> ()
      | Error l ->
        let lvl = Univ.Level.Set.choose l in (* Subsingleton of size 1 *)
        raise (PatternTranslationError (UnknownLevel lvl))



let translate_rewrite_rule env { pattern; replacement; info=Info info } =
  let empty_state = ((1, Evar.Map.empty), (0, QVar.Map.empty), (0, [], Level.Map.empty)) in
  let state, lhs_pat = translate_pattern empty_state pattern in
  let (nvars, evmap), (nvarqs, qvmap), (nvarus, _, uvmap) = state in
  let rhs = evar_subst evmap info.evar_map 0 replacement in
  let usubst = make_usubst (qvmap, uvmap) in
  let rhs = Vars.subst_univs_level_constr usubst rhs in
  let () =
    let qs, us = Vars.sort_and_universes_of_constr rhs in
    Sorts.QVar.Set.iter (test_qvar env nvarqs) qs;
    Univ.Level.Set.iter (test_level env nvarqs) us
  in
  let symb, head_umask, elims = match lhs_pat with
    | (PHSymbol (symb, mask), elims) -> symb, mask, elims
    | _ -> raise (PatternTranslationError NoHeadSymbol)
  in

  symb, { nvars = (nvars-1, nvarqs, nvarus); lhs_pat = (head_umask, elims); rhs }

let rec head_symbol = function
  | PSymbol (cst, _) -> cst
  | PApp (f, _, _, _) -> head_symbol f
  | PCase (c, _, _, _, _) -> head_symbol c
  | PProj (c, _, _) -> head_symbol c
  | PRel _ | PSort _ | PInd _ | PConstr _ | PInt _ | PFloat _ | PString _ | PLambda _ | PProd _ ->
      raise (PatternTranslationError NoHeadSymbol)
