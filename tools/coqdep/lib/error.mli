(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

exception CannotParseFile of string * (int * int)
exception CannotParseProjectFile of string * string
exception CannotOpenFile of string * string
exception CannotOpenProjectFile of string
exception InvalidFindlibPluginName of string * string

val cannot_parse : string -> int * int -> 'a
val cannot_open_project_file : string -> 'a
val cannot_parse_project_file : string -> string -> 'a
val cannot_open : string -> string -> 'a
val findlib_name : string -> string -> 'a

type what = Library | External
val str_of_what : what -> string
val mlnotfound : string -> string -> 'a
val filenotfound : string -> what -> string list option -> string list -> 'a
