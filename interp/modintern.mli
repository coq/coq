(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Environ
open Entries
open Constrexpr

(** Module internalization errors *)

type module_internalization_error =
  | NotAModuleNorModtype of string
  | IncorrectWithInModule
  | IncorrectModuleApplication

exception ModuleInternalizationError of module_internalization_error

(** Module expressions and module types are interpreted relatively to
   possible functor or functor signature arguments. When the input kind
   is ModAny (i.e. module or module type), we tries to interprete this ast
   as a module, and in case of failure, as a module type. The returned
   kind is never ModAny, and it is equal to the input kind when this one
   isn't ModAny. *)

val interp_module_ast :
  env -> Declaremods.module_kind -> module_ast -> module_struct_entry * Declaremods.module_kind * Univ.ContextSet.t
