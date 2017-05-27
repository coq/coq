(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Vernacexpr

type universe_decl =
  (lident list, Univ.Constraint.t) gen_universe_decl

val interp_univ_decl : Environ.env -> universe_decl_expr ->
                       Evd.evar_map * universe_decl

val interp_univ_decl_opt : Environ.env -> universe_decl_expr option ->
                       Evd.evar_map * universe_decl

val default_univ_decl : universe_decl

val check_univ_decl : Evd.evar_map -> universe_decl -> Universes.universe_binders * Univ.universe_context
