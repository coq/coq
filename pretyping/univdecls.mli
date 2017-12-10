(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Local universe and constraint declarations. *)
type universe_decl =
  (Misctypes.lident list, Univ.Constraint.t) Misctypes.gen_universe_decl

val default_univ_decl : universe_decl

val interp_univ_decl : Environ.env -> Vernacexpr.universe_decl_expr ->
                       Evd.evar_map * universe_decl

val interp_univ_decl_opt : Environ.env -> Vernacexpr.universe_decl_expr option ->
                       Evd.evar_map * universe_decl
