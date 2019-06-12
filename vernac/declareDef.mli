(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Decl_kinds

val declare_definition
  : Id.t
  -> definition_kind
  -> ?hook_data:(Lemmas.declaration_hook * UState.t * (Id.t * Constr.t) list)
  -> Evd.side_effects Entries.definition_entry
  -> UnivNames.universe_binders
  -> Impargs.manual_implicits
  -> GlobRef.t

val declare_fix
  : ?opaque:bool
  -> ?hook_data:(Lemmas.declaration_hook * UState.t * (Id.t * Constr.t) list)
  -> definition_kind
  -> UnivNames.universe_binders
  -> Entries.universes_entry
  -> Id.t
  -> Evd.side_effects Entries.proof_output
  -> Constr.types
  -> Impargs.manual_implicits
  -> GlobRef.t

val prepare_definition : allow_evars:bool ->
  ?opaque:bool -> ?inline:bool -> poly:bool ->
  Evd.evar_map -> UState.universe_decl ->
  types:EConstr.t option -> body:EConstr.t ->
  Evd.evar_map * Evd.side_effects Entries.definition_entry

val prepare_parameter : allow_evars:bool ->
  poly:bool -> Evd.evar_map -> UState.universe_decl -> EConstr.types ->
  Evd.evar_map * Entries.parameter_entry
