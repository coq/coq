(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** [coqide ocamlfind prefs best_compiler camllib] returns
   "opt|byte|no" and the path to lablgtk3 *)
val coqide : string -> CmdArgs.Prefs.t -> string -> string -> string * string

(** [idearchdef ocamlfind prefs coqide arch] returns ["QUARTZ"|"X11"|"WIN32"] *)
val idearchdef : string -> CmdArgs.Prefs.t -> string -> string -> string
