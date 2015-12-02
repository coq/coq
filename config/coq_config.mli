(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

val local : bool        (* local use (no installation) *)

val bindir : string     (* where the binaries are installed *)
val coqlib : string     (* where the std library is installed *)

val coqtop : string     (* where are the sources *)

val camllib : string    (* for Dynlink *)

val camlp4 : string     (* exact name of camlp4: either "camlp4" ou "camlp5" *)
val camlp4lib : string  (* where is the library of Camlp4 *)

val lablgtklib : string  (* where is the library of Lablgtk2 *)

val best : string       (* byte/opt *)
val arch : string       (* architecture *)
val osdeplibs : string  (* OS dependant link options for ocamlc *)

(* val defined : string list  (* options for lib/ocamlpp *) *)

val version : string    (* version number of Coq *)
val caml_version : string    (* OCaml version used to compile Coq *)
val versionsi : string  (* version number of Coq\_SearchIsos *)
val date : string       (* release date *)
val compile_date : string (* compile date *)

val theories_dirs : string list
val contrib_dirs : string list

val exec_extension : string (* "" under Unix, ".exe" under MS-windows *)
