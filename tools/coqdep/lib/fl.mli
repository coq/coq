(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** [findlib_resolve meta_files file package legacy_name plugin_name]
   tries to locate a [.cmxs] for a given [package.plugin_name]

    If a [META] file for [package] is found, it will try to use it to
   resolve the path to the [.cmxs], and return both. If not, it will
   return [None, legacy_name]. If [legacy_name] is absent, it errors.

    The [META] file for [package] is search among the list of
   [meta_files] first, then using [Findlib.package_meta_file]. note
   that coqdep doesn't initialize findlib so that function performs
   implicity initialization.
*)
val findlib_resolve
  : meta_files:string list
  -> file:string
  -> package:string
  -> legacy_name:string option
  -> plugin_name:string list
  -> string option * string
