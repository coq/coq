(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Environ

let env_of_library senv clib =
  let env = Safe_typing.env_of_safe_env senv in
  let qualities, univs = Safe_typing.univs_of_library clib in
  let check_quality q =
    not (QGraph.is_declared (Sorts.Quality.QGlobal q) (Environ.qualities env))
  in
  let () = assert (Sorts.QGlobal.Set.for_all check_quality (fst qualities)) in
  let env = Environ.push_qualities (Sorts.Quality.Set.of_qglobals @@ fst qualities) env in
  let env = Environ.merge_elim_constraints ~rigid:true (snd qualities) env in
  push_context_set ~strict:true univs env

(* The checker does not read the [vmlibrary] segment of the file at all: the
   bytecode of every constant is recompiled from the declarations about to be
   checked (see [Safe_typing.recompile_vm_library]), and the resulting table is
   handed to [Safe_typing.import] in place of the one stored in the file.

   With -bytecode-compiler no, the default, no bytecode is ever run, so there is
   nothing to recompile and we hand over an empty table. *)
let vm_library_of env clib =
  if !CheckFlags.enable_vm then Safe_typing.recompile_vm_library env clib
  else Safe_typing.empty_vm_library env clib, clib

let import senv opac clib digest =
  let senv = Safe_typing.check_flags_for_library clib senv in
  let dp = Safe_typing.dirpath_of_library clib in
  let retro = Safe_typing.retroknowledge_of_library clib in
  let env = env_of_library senv clib in
  let vmtab, clib = vm_library_of env clib in
  let env = Environ.set_vm_library vmtab env in
  let mb = Safe_typing.module_of_library clib in
  let opac = Mod_checking.check_module env opac retro (Names.ModPath.MPfile dp) mb in
  let vmtab = Vmlibrary.inject (Vmlibrary.export vmtab) in
  let (_,senv) = Safe_typing.import clib vmtab digest senv in senv, opac

let import senv opac clib digest : _ * _ =
  NewProfile.profile "import"
    ~args:(fun () ->
        let dp = Safe_typing.dirpath_of_library clib in
        [("name", `String (Names.DirPath.to_string dp))])
    (fun () ->import senv opac clib digest)
    ()

let unsafe_import senv clib digest =
  (* Admitted libraries are trusted for their declarations, but their bytecode is
     recompiled all the same, so that the trusted surface is exactly the same. *)
  let env = env_of_library senv clib in
  let vmtab, clib = vm_library_of env clib in
  let vmtab = Vmlibrary.inject (Vmlibrary.export vmtab) in
  let (_,senv) = Safe_typing.import clib vmtab digest senv in senv
