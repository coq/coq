(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Declarations
open Environ

let import senv opac clib vmtab digest =
  let senv = Safe_typing.check_flags_for_library clib senv in
  let mb = Safe_typing.module_of_library clib in
  let env = Safe_typing.env_of_safe_env senv in
  let env = push_context_set ~strict:true (Safe_typing.univs_of_library clib) env in
  let env = Modops.add_retroknowledge mb.mod_retroknowledge env in
  let env = Environ.link_vm_library vmtab env in
  let opac = Mod_checking.check_module env opac mb.mod_mp mb in
  let (_,senv) = Safe_typing.import clib vmtab digest senv in senv, opac

let import senv opac clib vmtab digest : _ * _ =
  NewProfile.profile "import"
    ~args:(fun () ->
        let dp = match (Safe_typing.module_of_library clib).mod_mp with
          | MPfile dp -> dp
          | _ -> assert false
        in
        [("name", `String (Names.DirPath.to_string dp))])
  @@ fun () ->
  import senv opac clib vmtab digest

let unsafe_import senv clib vmtab digest =
  let (_,senv) = Safe_typing.import clib vmtab digest senv in senv
