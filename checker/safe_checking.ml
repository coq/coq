(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Declarations
open Environ

let import senv clib univs digest =
  let mb = Safe_typing.module_of_library clib in
  let env = Safe_typing.env_of_safe_env senv in
  let env = push_context_set ~strict:true mb.mod_constraints env in
  let env = push_context_set ~strict:true univs env in
  let env = Modops.add_retroknowledge mb.mod_retroknowledge env in
  Mod_checking.check_module env mb.mod_mp mb;
  let (_,senv) = Safe_typing.import clib univs digest senv in senv

let unsafe_import senv clib univs digest =
  let (_,senv) = Safe_typing.import clib univs digest senv in senv
