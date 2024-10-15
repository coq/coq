(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** [findlib_resolve ~meta_files ~file ~package ~plugin_name] tries to locate
    a [.cmxs] for a given [package.plugin_name].

    If a [META] file for [package] is found, it will try to use it to resolve
    the path to the [.cmxs], and return a relative path to both. If not, it
    errors.

    The [META] file for [package] is first searched in the [meta_files] list,
    and if it is not found then [Findlib.package_meta_file] is used. Note that
    coqdep does not initialize findlib, so that function performs implicity
    initialization. *)
val findlib_resolve
  : meta_files:string list
  -> file:string
  -> package:string
  -> plugin_name:string list
  -> string * string
