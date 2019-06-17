(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

val local : bool        (* local use (no installation) *)

(* The fields below are absolute paths *)
val coqlib : string     (* where the std library is installed *)
val configdir : string  (* where configuration files are installed *)
val datadir : string    (* where extra data files are installed *)
val docdir : string     (* where the doc is installed *)

(* The fields below are paths relative to the installation prefix *)
(* However, if an absolute path, it means discarding the actual prefix *)
val coqlibsuffix : string    (* std library relative to installation prefix *)
val configdirsuffix : string (* config files relative to installation prefix *)
val datadirsuffix : string   (* data files relative to installation prefix *)
val docdirsuffix : string    (* doc directory relative to installation prefix *)

val ocamlfind : string

val caml_flags : string     (* arguments passed to ocamlc (ie. CAMLFLAGS) *)

val arch : string       (* architecture *)
val arch_is_win32 : bool

val version : string    (* version number of Coq *)
val caml_version : string    (* OCaml version used to compile Coq *)
val caml_version_nums : int list    (* OCaml version used to compile Coq by components *)
val date : string       (* release date *)
val compile_date : string (* compile date *)
val vo_magic_number : int
val state_magic_number : int

val all_src_dirs : string list

val exec_extension : string (* "" under Unix, ".exe" under MS-windows *)

val browser : string
(** default web browser to use, may be overridden by environment
    variable COQREMOTEBROWSER *)

val gtk_platform : [`QUARTZ | `WIN32 | `X11]

val has_natdynlink : bool

val wwwcoq : string
val wwwrefman : string
val wwwbugtracker : string
val wwwstdlib : string
val localwwwrefman : string

val bytecode_compiler : bool
val native_compiler : bool
