(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

val local : bool        (* local use (no installation) *)

val coqlib : string     (* where the std library is installed *)
val coqsrc : string     (* where are the sources *)

val ocaml : string      (* names of ocaml binaries *)
val ocamlc : string
val ocamlopt : string
val ocamlmklib : string
val ocamldoc : string
val ocamldep : string
val ocamlyacc : string
val ocamllex : string

val camlbin : string    (* base directory of OCaml binaries *)
val camllib : string    (* for Dynlink *)

val camlp4 : string     (* exact name of camlp4: either "camlp4" ou "camlp5" *)
val camlp4o : string    (* name of the camlp4o/camlp5o executable *)
val camlp4bin : string  (* base directory for Camlp4/5 binaries *)
val camlp4lib : string  (* where is the library of Camlp4 *)
val camlp4compat : string (* compatibility argument to camlp4/5 *)

val coqideincl : string (* arguments for building coqide (e.g. lablgtk) *)
val cflags : string     (* arguments passed to gcc *)

val best : string       (* byte/opt *)
val arch : string       (* architecture *)
val osdeplibs : string  (* OS dependant link options for ocamlc *)
val coqrunbyteflags : string (* -custom/-dllib -lcoqrun *)


(* val defined : string list  (* options for lib/ocamlpp *) *)

val version : string    (* version number of Coq *)
val caml_version : string    (* OCaml version used to compile Coq *)
val date : string       (* release date *)
val compile_date : string (* compile date *)
val vo_magic_number : int
val state_magic_number : int

val theories_dirs : string list
val plugins_dirs : string list

val exec_extension : string (* "" under Unix, ".exe" under MS-windows *)
val with_geoproof : bool ref (* to (de)activate functions specific to Geoproof with Coqide *)

val browser : string
(** default web browser to use, may be overriden by environment
    variable COQREMOTEBROWSER *)

val has_coqide : string

val has_natdynlink : bool
val natdynlinkflag : string (* special cases of natdynlink (e.g. MacOS 10.5) *)

val wwwcoq : string
val wwwrefman : string
val wwwstdlib : string
val localwwwrefman : string

