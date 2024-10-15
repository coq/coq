(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open Constr
open Declarations
open Environ
open Context

module RelDecl = Context.Rel.Declaration

let relevance_of_rel env n =
  let decl = lookup_rel n env in
  RelDecl.get_relevance decl

let relevance_of_var env x =
  let decl = lookup_named x env in
  Context.Named.Declaration.get_relevance decl

let relevance_of_constant env (c,u) =
  let decl = lookup_constant c env in
  UVars.subst_instance_relevance u decl.const_relevance

let relevance_of_constructor env ((ind,_),u) =
  Inductive.relevance_of_inductive env (ind,u)

let relevance_of_projection_repr env (p, u) =
  let mib = lookup_mind (Names.Projection.Repr.mind p) env in
  let _mind,i = Names.Projection.Repr.inductive p in
  match mib.mind_record with
  | NotRecord | FakeRecord ->
    CErrors.anomaly ~label:"relevance_of_projection" Pp.(str "not a projection")
  | PrimRecord infos ->
    let _,_,rs,_ = infos.(i) in
    UVars.subst_instance_relevance u rs.(Names.Projection.Repr.arg p)

let relevance_of_projection env (p,u) =
  relevance_of_projection_repr env (Names.Projection.repr p,u)

let rec relevance_of_term_extra env extra lft c =
  match kind c with
  | Rel n ->
    if n <= lft then Range.get extra (n - 1)
    else relevance_of_rel env (n - lft)
  | Var x -> relevance_of_var env x
  | Sort _ | Ind _ | Prod _ -> Sorts.Relevant (* types are always relevant *)
  | Cast (c, _, _) -> relevance_of_term_extra env extra lft c
  | Lambda ({binder_relevance=r;_}, _, bdy) ->
    relevance_of_term_extra env (Range.cons r extra) (lft + 1) bdy
  | LetIn ({binder_relevance=r;_}, _, _, bdy) ->
    relevance_of_term_extra env (Range.cons r extra) (lft + 1) bdy
  | App (c, _) -> relevance_of_term_extra env extra lft c
  | Const c -> relevance_of_constant env c
  | Construct c -> relevance_of_constructor env c
  | Case (_, _, _, (_, r), _, _, _) -> r
  | Fix ((_,i),(lna,_,_)) -> (lna.(i)).binder_relevance
  | CoFix (i,(lna,_,_)) -> (lna.(i)).binder_relevance
  | Proj (_, r, _) -> r
  | Int _ | Float _ | String _ -> Sorts.Relevant
  | Array _ -> Sorts.Relevant

  | Meta _ | Evar _ -> Sorts.Relevant (* let's assume metas and evars are relevant for now *)

let relevance_of_term env c =
  relevance_of_term_extra env Range.empty 0 c
