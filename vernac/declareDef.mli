(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Decl_kinds

val get_locality : Id.t -> kind:string -> Decl_kinds.locality -> bool

val declare_definition : Id.t -> definition_kind ->
  Safe_typing.private_constants Entries.definition_entry -> Universes.universe_binders -> Impargs.manual_implicits ->
    GlobRef.t Lemmas.declaration_hook -> GlobRef.t

val declare_fix : ?opaque:bool -> definition_kind -> Universes.universe_binders -> Univ.UContext.t -> Id.t ->
  Safe_typing.private_constants Entries.proof_output -> Constr.types -> Impargs.manual_implicits -> GlobRef.t
