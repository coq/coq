(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** This file provides a high-level interface to the environment variables 
    needed by Coq to run (such as coqlib). The values of these variables
    may come from different sources (shell environment variables, 
    command line options, options set at the time Coq was build). *)

(** [expand_path_macros warn s] substitutes environment variables 
    in a string by their values. This function also takes care of
    substituting path of the form '~X' by an absolute path. 
    Use [warn] as a message displayer. *)
val expand_path_macros : warn:(string -> unit) -> string -> string

(** [home warn] returns the root of the user directory, depending
    on the OS. This information is usually stored in the $HOME 
    environment variable on POSIX shells. If no such variable 
    exists, then other common names are tried (HOMEDRIVE, HOMEPATH,
    USERPROFILE). If all of them fail, [warn] is called. *)
val home : warn:(string -> unit) -> string

(** [coqlib] is the path to the Coq library. *)
val coqlib : unit -> string

(** [set_coqlib] must be runned once before any access to [coqlib] *)
val set_coqlib : fail:(string -> string) -> unit

(** [docdir] is the path to the Coq documentation. *)
val docdir : unit -> string

(** [coqbin] is the name of the current executable. *)
val coqbin : string

(** [coqroot] is the path to [coqbin]. 
    The following value only makes sense when executables are running from
    source tree (e.g. during build or in local mode). 
*)
val coqroot : string

(** [coqpath] is the standard path to coq. 
    Notice that coqpath is stored in reverse order, since that is 
    the order it gets added to the search path. *)
val coqpath : string list

(** [camlbin ()] is the path to the ocaml binaries. *)
val camlbin : unit -> string

(** [camllib ()] is the path to the ocaml standard library. *)
val camllib : unit -> string

(** [ocamlc ()] is the ocaml bytecode compiler that compiled this Coq. *)
val ocamlc   : unit -> string

(** [ocamlc ()] is the ocaml native compiler that compiled this Coq. *)
val ocamlopt : unit -> string

(** [camlp4bin ()] is the path to the camlp4 binary. *)
val camlp4bin : unit -> string

(** [camlp4lib ()] is the path to the camlp4 library. *)
val camlp4lib : unit -> string

(** [camlp4 ()] is the camlp4 utility. *)
val camlp4 : unit -> string

(** Coq tries to honor the XDG Base Directory Specification to access
    the user's configuration files.

    see [http://standards.freedesktop.org/basedir-spec/basedir-spec-latest.html]
*)
val xdg_config_home : (string -> unit) -> string
val xdg_data_home   : (string -> unit) -> string
val xdg_config_dirs : (string -> unit) -> string list
val xdg_data_dirs   : (string -> unit) -> string list
val xdg_dirs : warn : (string -> unit) -> string list
