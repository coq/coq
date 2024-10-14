(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(*i*)
open Safe_typing
(*i*)

val import
  : safe_environment
  -> Names.Cset.t Names.Cmap.t
  -> compiled_library
  -> Vmlibrary.on_disk
  -> vodigest -> safe_environment * Names.Cset.t Names.Cmap.t

val unsafe_import
  : safe_environment
  -> compiled_library
  -> Vmlibrary.on_disk
  -> vodigest
  -> safe_environment
