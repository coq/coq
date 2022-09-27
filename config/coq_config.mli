(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

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

(* used in envars (likely for coq_makefile) *)
val ocamlfind : string

(* Used in coqide *)
val arch : string       (* architecture *)

(* dubious use in envars, use in coqmakefile *)
val arch_is_win32 : bool

val version : string    (* version number of Coq *)
val caml_version : string    (* OCaml version used to compile Coq *)
val caml_version_nums : int list    (* OCaml version used to compile Coq by components *)
val vo_version : int32

(* Used in micromega *)
val exec_extension : string (* "" under Unix, ".exe" under MS-windows *)

(* Used in coqide *)
val browser : string
(** default web browser to use, may be overridden by environment
    variable COQREMOTEBROWSER *)

(* used in coqdep *)
val has_natdynlink : bool

(* used in coqdoc *)
val wwwcoq : string
val wwwstdlib : string

(* used in coqide *)
val wwwrefman : string

(* for error reporting *)
val wwwbugtracker : string

val bytecode_compiler : bool
type native_compiler = NativeOff | NativeOn of { ondemand : bool }
val native_compiler : native_compiler
