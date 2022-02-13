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
open Names
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

let relevance_of_constant env c =
  let decl = lookup_constant c env in
  decl.const_relevance

let relevance_of_constructor env ((mi,i),_) =
  let decl = lookup_mind mi env in
  let packet = decl.mind_packets.(i) in
  packet.mind_relevance

let relevance_of_projection env p =
  let mind = Projection.mind p in
  let mib = lookup_mind mind env in
  Declareops.relevance_of_projection_repr mib (Projection.repr p)

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
  | Const (c,_) -> relevance_of_constant env c
  | Construct (c,_) -> relevance_of_constructor env c
  | Case (ci, _, _, _, _, _, _) -> ci.ci_relevance
  | Fix ((_,i),(lna,_,_)) -> (lna.(i)).binder_relevance
  | CoFix (i,(lna,_,_)) -> (lna.(i)).binder_relevance
  | Proj (p, _) -> relevance_of_projection env p
  | Int _ | Float _ -> Sorts.Relevant
  | Array _ -> Sorts.Relevant

  | Meta _ | Evar _ -> Sorts.Relevant (* let's assume metas and evars are relevant for now *)

let relevance_of_term env c =
  relevance_of_term_extra env Range.empty 0 c
