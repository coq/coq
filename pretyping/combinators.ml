(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Coqlib
open CErrors
open Util

module RelDecl = Context.Rel.Declaration

type family = SPropF | PropF | TypeF
let family_of_sort_family = let open Sorts in function
    | InSProp -> SPropF
    | InProp -> PropF
    | InSet | InType | InQSort -> TypeF

let get_sigmatypes sigma ~sort ~predsort =
  let open EConstr in
  let which, sigsort = match predsort, sort with
    | SPropF, _ | _, SPropF ->
      user_err Pp.(str "SProp arguments not supported by Program Fixpoint yet.")
    | PropF, PropF -> "ex", PropF
    | PropF, TypeF -> "sig", TypeF
    | TypeF, (PropF|TypeF) -> "sigT", TypeF
  in
  let sigma, ty = Evd.fresh_global (Global.env ()) sigma (lib_ref ("core."^which^".type")) in
  let uinstance = snd (destRef sigma ty) in
  let intro = mkRef (lib_ref ("core."^which^".intro"), uinstance) in
  let p1 = mkRef (lib_ref ("core."^which^".proj1"), uinstance) in
  let p2 = mkRef (lib_ref ("core."^which^".proj2"), uinstance) in
  sigma, ty, intro, p1, p2, sigsort

let rec telescope sigma l =
  let open EConstr in
  let open Vars in
  match l with
  | [] -> assert false
  | [RelDecl.LocalAssum (n, t), _] ->
    sigma, t, [RelDecl.LocalDef (n, mkRel 1, t)], mkRel 1
  | (LocalAssum (n, t), tsort) :: tl ->
      let sigma, ty, _tysort, tys, (k, constr) =
        List.fold_left
          (fun (sigma, ty, tysort, tys, (k, constr)) (decl,sort) ->
            let t = RelDecl.get_type decl in
            let pred = mkLambda (RelDecl.get_annot decl, t, ty) in
            let sigma, ty, intro, p1, p2, sigsort = get_sigmatypes sigma ~predsort:tysort ~sort in
            let sigty = mkApp (ty, [|t; pred|]) in
            let intro = mkApp (intro, [|lift k t; lift k pred; mkRel k; constr|]) in
              (sigma, sigty, sigsort, (pred, p1, p2) :: tys, (succ k, intro)))
          (sigma, t, tsort, [], (2, mkRel 1)) tl
      in
      let sigma, last, subst = List.fold_right2
        (fun (pred,p1,p2) (decl,_) (sigma, prev, subst) ->
          let t = RelDecl.get_type decl in
          let proj1 = applist (p1, [t; pred; prev]) in
          let proj2 = applist (p2, [t; pred; prev]) in
            (sigma, lift 1 proj2, RelDecl.(LocalDef (get_annot decl, proj1, t) :: subst)))
        (List.rev tys) tl (sigma, mkRel 1, [])
      in sigma, ty, (LocalDef (n, last, t) :: subst), constr

  | (LocalDef (n, b, t), _) :: tl ->
    let sigma, ty, subst, term = telescope sigma tl in
    sigma, ty, (LocalDef (n, b, t) :: subst), lift 1 term

type telescope = {
  telescope_type : EConstr.types;
  telescope_value : EConstr.constr;
}

let telescope env sigma ctx =
  let ctx, _ = List.fold_right_map (fun d env ->
      let s = Retyping.get_sort_family_of env sigma (RelDecl.get_type d) in
      let env = EConstr.push_rel d env in
      (d, family_of_sort_family s), env) ctx env
  in
  let sigma, telescope_type, letcontext, telescope_value = telescope sigma ctx in
  sigma, letcontext, { telescope_type; telescope_value }
