
(*i $Id$ i*)

val local : bool        (* local use (no installation) *)

val bindir : string     (* where the binaries are installed *)
val coqlib : string     (* where the std library is installed *)

val coqtop : string     (* where are the sources *)

val camllib : string    (* for Dynlink *)

val camlp4lib : string  (* where is the library of Camlp4 *)

val best : string       (* byte/opt *)
val arch : string       (* architecture *)
val osdeplibs : string  (* OS dependant link options for ocamlc *)

val defined : string list  (* options for lib/ocamlpp *)

val version : string    (* version number of Coq *)
val versionsi : string  (* version number of Coq\_SearchIsos *)
val date : string       (* release date *)
val compile_date : string (* compile date *)

val theories_dirs : string list
val contrib_dirs : string list

