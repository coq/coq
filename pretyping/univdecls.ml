(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open CErrors

(** Local universes and constraints declarations *)
type universe_decl =
  (Misctypes.lident list, Univ.Constraint.t) Misctypes.gen_universe_decl

let default_univ_decl =
  let open Misctypes in
  { univdecl_instance = [];
    univdecl_extensible_instance = true;
    univdecl_constraints = Univ.Constraint.empty;
    univdecl_extensible_constraints = true }

let interp_univ_constraints env evd cstrs =
  let interp (evd,cstrs) (u, d, u') =
    let ul = Pretyping.interp_known_glob_level evd u in
    let u'l = Pretyping.interp_known_glob_level evd u' in
    let cstr = (ul,d,u'l) in
    let cstrs' = Univ.Constraint.add cstr cstrs in
    try let evd = Evd.add_constraints evd (Univ.Constraint.singleton cstr) in
        evd, cstrs'
    with Univ.UniverseInconsistency e ->
      user_err ~hdr:"interp_constraint"
        (Univ.explain_universe_inconsistency (Termops.pr_evd_level evd) e)
  in
  List.fold_left interp (evd,Univ.Constraint.empty) cstrs

let interp_univ_decl env decl =
  let open Misctypes in
  let pl : lident list = decl.univdecl_instance in
  let evd = Evd.from_ctx (UState.make_with_initial_binders (Environ.universes env) pl) in
  let evd, cstrs = interp_univ_constraints env evd decl.univdecl_constraints in
  let decl = { univdecl_instance = pl;
    univdecl_extensible_instance = decl.univdecl_extensible_instance;
    univdecl_constraints = cstrs;
    univdecl_extensible_constraints = decl.univdecl_extensible_constraints }
  in evd, decl

let interp_univ_decl_opt env l =
  match l with
  | None -> Evd.from_env env, default_univ_decl
  | Some decl -> interp_univ_decl env decl
