(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
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

let rec relevance_of_rel_extra env extra n =
  match extra with
  | [] -> relevance_of_rel env n
  | r :: _ when Int.equal n 1 -> r
  | _ :: extra -> relevance_of_rel_extra env extra (n-1)

let relevance_of_flex env extra lft = function
  | ConstKey (c,_) -> relevance_of_constant env c
  | VarKey x -> relevance_of_var env x
  | RelKey p -> relevance_of_rel_extra env extra (Esubst.reloc_rel p lft)

let rec relevance_of_fterm env extra lft f =
  let open CClosure in
  match CClosure.relevance_of f with
  | KnownR -> Sorts.Relevant
  | KnownI -> Sorts.Irrelevant
  | Unknown ->
    let r = match fterm_of f with
      | FRel n -> relevance_of_rel_extra env extra (Esubst.reloc_rel n lft)
      | FAtom c -> relevance_of_term_extra env extra lft (Esubst.subs_id 0) c
      | FFlex key -> relevance_of_flex env extra lft key
      | FInt _ -> Sorts.Relevant
      | FInd _ | FProd _ -> Sorts.Relevant (* types are always relevant *)
      | FConstruct (c,_) -> relevance_of_constructor env c
      | FApp (f, _) -> relevance_of_fterm env extra lft f
      | FProj (p, _) -> relevance_of_projection env p
      | FFix (((_,i),(lna,_,_)), _) -> (lna.(i)).binder_relevance
      | FCoFix ((i,(lna,_,_)), _) -> (lna.(i)).binder_relevance
      | FCaseT (ci, _, _, _, _) -> ci.ci_relevance
      | FLambda (len, tys, bdy, e) ->
        let extra = List.rev_append (List.map (fun (x,_) -> binder_relevance x) tys) extra in
        let lft = Esubst.el_liftn len lft in
        relevance_of_term_extra env extra lft e bdy
      | FLetIn (x, _, _, bdy, e) ->
        relevance_of_term_extra env (x.binder_relevance :: extra)
          (Esubst.el_lift lft) (Esubst.subs_lift e) bdy
      | FLIFT (k, f) -> relevance_of_fterm env extra (Esubst.el_shft k lft) f
      | FCLOS (c, e) -> relevance_of_term_extra env extra lft e c

      | FEvar (_, _) -> Sorts.Relevant (* let's assume evars are relevant for now *)
      | FLOCKED -> assert false
    in
    CClosure.set_relevance r f;
    r

and relevance_of_term_extra env extra lft subs c =
  match kind c with
  | Rel n ->
    (match Esubst.expand_rel n subs with
     | Inl (k, f) -> relevance_of_fterm env extra (Esubst.el_liftn k lft) f
     | Inr (n, _) -> relevance_of_rel_extra env extra (Esubst.reloc_rel n lft))
  | Var x -> relevance_of_var env x
  | Sort _ | Ind _ | Prod _ -> Sorts.Relevant (* types are always relevant *)
  | Cast (c, _, _) -> relevance_of_term_extra env extra lft subs c
  | Lambda ({binder_relevance=r;_}, _, bdy) ->
    relevance_of_term_extra env (r::extra) (Esubst.el_lift lft) (Esubst.subs_lift subs) bdy
  | LetIn ({binder_relevance=r;_}, _, _, bdy) ->
    relevance_of_term_extra env (r::extra) (Esubst.el_lift lft) (Esubst.subs_lift subs) bdy
  | App (c, _) -> relevance_of_term_extra env extra lft subs c
  | Const (c,_) -> relevance_of_constant env c
  | Construct (c,_) -> relevance_of_constructor env c
  | Case (ci, _, _, _) -> ci.ci_relevance
  | Fix ((_,i),(lna,_,_)) -> (lna.(i)).binder_relevance
  | CoFix (i,(lna,_,_)) -> (lna.(i)).binder_relevance
  | Proj (p, _) -> relevance_of_projection env p
  | Int _ -> Sorts.Relevant

  | Meta _ | Evar _ -> Sorts.Relevant (* let's assume metas and evars are relevant for now *)

let relevance_of_fterm env extra lft c =
  if Environ.sprop_allowed env then relevance_of_fterm env extra lft c
  else Sorts.Relevant

let relevance_of_term env c =
  if Environ.sprop_allowed env
  then relevance_of_term_extra env [] Esubst.el_id (Esubst.subs_id 0) c
  else Sorts.Relevant
