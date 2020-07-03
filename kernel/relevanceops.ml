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

let relevance_of_flex env = function
  | ConstKey (c,_) -> relevance_of_constant env c
  | VarKey x -> relevance_of_var env x
  | RelKey p -> relevance_of_rel env p

let rec relevance_of_fterm env extra lft f =
  let open CClosure in
  match CClosure.relevance_of f with
  | KnownR -> Sorts.Relevant
  | KnownI -> Sorts.Irrelevant
  | Unknown ->
    let r = match fterm_of f with
      | FRel n -> Range.get extra (Esubst.reloc_rel n lft - 1)
      | FAtom c -> relevance_of_term_extra env extra lft (Esubst.subs_id 0) c
      | FFlex (key, _) -> relevance_of_flex env key
      | FInt _ | FFloat _ -> Sorts.Relevant
      | FInd _ | FProd _ -> Sorts.Relevant (* types are always relevant *)
      | FConstruct (c,_) -> relevance_of_constructor env c
      | FApp (f, _) -> relevance_of_fterm env extra lft f
      | FProj (p, _) -> relevance_of_projection env p
      | FFix (((_,i),(lna,_,_)), _) -> (lna.(i)).binder_relevance
      | FCoFix ((i,(lna,_,_)), _) -> (lna.(i)).binder_relevance
      | FCaseT (ci, _, _, _, _) -> ci.ci_relevance
      | FLambda (len, tys, bdy, e) ->
        let extra = List.fold_left (fun accu (x, _) -> Range.cons (binder_relevance x) accu) extra tys in
        let lft = Esubst.el_liftn len lft in
        let e = Esubst.subs_liftn len e in
        relevance_of_term_extra env extra lft e bdy
      | FLetIn (x, _, _, bdy, e) ->
        relevance_of_term_extra env (Range.cons x.binder_relevance extra)
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
  | Rel (n, _) ->
    begin match Esubst.expand_rel n subs with
     | Inl (k, f) -> relevance_of_fterm env extra (Esubst.el_liftn k lft) f
     | Inr (n, None) -> Range.get extra (Esubst.reloc_rel n lft - 1)
     | Inr (_, Some p) -> relevance_of_rel env p
    end
  | Var (x, _) -> relevance_of_var env x
  | Sort _ | Ind _ | Prod _ -> Sorts.Relevant (* types are always relevant *)
  | Cast (c, _, _) -> relevance_of_term_extra env extra lft subs c
  | Lambda ({binder_relevance=r;_}, _, bdy) ->
    relevance_of_term_extra env (Range.cons r extra) (Esubst.el_lift lft) (Esubst.subs_lift subs) bdy
  | LetIn ({binder_relevance=r;_}, _, _, bdy) ->
    relevance_of_term_extra env (Range.cons r extra) (Esubst.el_lift lft) (Esubst.subs_lift subs) bdy
  | App (c, _) -> relevance_of_term_extra env extra lft subs c
  | Const ((c,_), _) -> relevance_of_constant env c
  | Construct (c,_) -> relevance_of_constructor env c
  | Case (ci, _, _, _) -> ci.ci_relevance
  | Fix ((_,i),(lna,_,_)) -> (lna.(i)).binder_relevance
  | CoFix (i,(lna,_,_)) -> (lna.(i)).binder_relevance
  | Proj (p, _) -> relevance_of_projection env p
  | Int _ | Float _ -> Sorts.Relevant

  | Meta _ | Evar _ -> Sorts.Relevant (* let's assume metas and evars are relevant for now *)

let relevance_of_fterm env extra lft c =
  if Environ.sprop_allowed env then relevance_of_fterm env extra lft c
  else Sorts.Relevant

let relevance_of_term env c =
  if Environ.sprop_allowed env
  then relevance_of_term_extra env Range.empty Esubst.el_id (Esubst.subs_id 0) c
  else Sorts.Relevant
