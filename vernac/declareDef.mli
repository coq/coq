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

val get_locality : Id.t -> kind:string -> Decl_kinds.locality -> bool

val declare_definition : Id.t -> definition_kind ->
  Safe_typing.private_constants Entries.definition_entry -> UnivNames.universe_binders -> Impargs.manual_implicits ->
    GlobRef.t Lemmas.declaration_hook -> GlobRef.t

val declare_fix : ?opaque:bool -> definition_kind ->
  UnivNames.universe_binders -> Entries.constant_universes_entry ->
  Id.t -> Safe_typing.private_constants Entries.proof_output ->
  Constr.types -> Impargs.manual_implicits ->
  GlobRef.t
