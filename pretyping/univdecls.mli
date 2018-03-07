(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Local universe and constraint declarations. *)
type universe_decl =
  (Misctypes.lident list, Univ.Constraint.t) Misctypes.gen_universe_decl

val default_univ_decl : universe_decl

val interp_univ_decl : Environ.env -> Constrexpr.universe_decl_expr ->
                       Evd.evar_map * universe_decl

val interp_univ_decl_opt : Environ.env -> Constrexpr.universe_decl_expr option ->
                       Evd.evar_map * universe_decl
