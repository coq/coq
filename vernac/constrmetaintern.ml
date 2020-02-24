(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Genintern
open Pattern

let intern_constr_gen pattern_mode isarity {ltacvars=lfun; genv=env; extra; intern_sign; strict_check} c =
  let warn = if strict_check then fun x -> x else Constrintern.for_grammar in
  let scope = if isarity then Pretyping.IsType else Pretyping.WithoutTypeConstraint in
  let ltacvars = {
    Constrintern.ltac_vars = lfun;
    ltac_bound = Id.Set.empty;
    ltac_extra = extra;
  } in
  let c' =
    warn (Constrintern.intern_core scope ~pattern_mode ~ltacvars env Evd.(from_env env) intern_sign) c
  in
  (c',if strict_check then None else Some c)

let intern_constr = intern_constr_gen false false
let intern_type = intern_constr_gen false true

let dummy_pat = PRel 0

let intern_typed_pattern ist ~as_type ~ltacvars p =
  (* we cannot ensure in non strict mode that the pattern is closed *)
  (* keeping a constr_expr copy is too complicated and we want anyway to *)
  (* type it, so we remember the pattern as a glob_constr only *)
  let metas,pat =
    if ist.strict_check then
      let ltacvars = {
          Constrintern.ltac_vars = ltacvars;
          ltac_bound = Id.Set.empty;
          ltac_extra = ist.extra;
        } in
      Constrintern.intern_constr_pattern ist.genv Evd.(from_env ist.genv) ~as_type ~ltacvars p
    else
      [], dummy_pat in
  let (glob,_ as c) = intern_constr_gen true false ist p in
  let bound_names = Glob_ops.bound_glob_vars glob in
  metas,(bound_names,c,pat)
