(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
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

val ocaml : string      (* names of ocaml binaries *)
val ocamlfind : string
val ocamllex : string

val camlbin : string    (* base directory of OCaml binaries *)
val camllib : string    (* for Dynlink *)

val camlp5o : string    (* name of the camlp5o executable *)
val camlp5bin : string  (* base directory for camlp5 binaries *)
val camlp5lib : string  (* where is the library of camlp5 *)
val camlp5compat : string (* compatibility argument to camlp5 *)

val coqideincl : string (* arguments for building coqide (e.g. lablgtk) *)
val cflags : string     (* arguments passed to gcc *)
val caml_flags : string     (* arguments passed to ocamlc (ie. CAMLFLAGS) *)

val best : string       (* byte/opt *)
val arch : string       (* architecture *)
val arch_is_win32 : bool
val vmbyteflags : string list (* -custom/-dllib -lcoqrun *)

val version : string    (* version number of Coq *)
val caml_version : string    (* OCaml version used to compile Coq *)
val caml_version_nums : int list    (* OCaml version used to compile Coq by components *)
val date : string       (* release date *)
val compile_date : string (* compile date *)
val vo_magic_number : int
val state_magic_number : int

val core_src_dirs : string list
val plugins_dirs : string list
val all_src_dirs : string list

val exec_extension : string (* "" under Unix, ".exe" under MS-windows *)

val browser : string
(** default web browser to use, may be overridden by environment
    variable COQREMOTEBROWSER *)

val has_coqide : string
val gtk_platform : [`QUARTZ | `WIN32 | `X11]

val has_natdynlink : bool
val natdynlinkflag : string (* special cases of natdynlink (e.g. MacOS 10.5) *)

val flambda_flags : string list

val wwwcoq : string
val wwwrefman : string
val wwwbugtracker : string
val wwwstdlib : string
val localwwwrefman : string

val bytecode_compiler : bool
val native_compiler : bool
