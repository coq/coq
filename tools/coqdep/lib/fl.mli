(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** [findlib_resolve ~file ~package ~plugin_name] tries to locate
    a [.cmxs] for a given [package.plugin_name].

    If a [META] file for [package] is found, it will try to use it to resolve
    the path to the [.cmxs], and return a relative path to both. If not, it
    errors. *)
val findlib_resolve
  :  file:string
  -> package:string
  -> plugin_name:string list
  -> string * string
