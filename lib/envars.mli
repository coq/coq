(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
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

(** [docdir] is the path to the installed documentation. *)
val docdir : unit -> string

(** [datadir] is the path to the installed data directory. *)
val datadir : unit -> string

(** [configdir] is the path to the installed config directory. *)
val configdir : unit -> string

(** [set_coqlib] must be runned once before any access to [coqlib] *)
val set_coqlib : fail:(string -> string) -> unit

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

(** [camlfind ()] is the path to the ocamlfind binary. *)
val ocamlfind : unit -> string

(** [camlp5bin ()] is the path to the camlp5 binary. *)
val camlp5bin : unit -> string

(** [camlp5lib ()] is the path to the camlp5 library. *)
val camlp5lib : unit -> string

(** Coq tries to honor the XDG Base Directory Specification to access
    the user's configuration files.

    see [http://standards.freedesktop.org/basedir-spec/basedir-spec-latest.html]
*)
val xdg_config_home : (string -> unit) -> string
val xdg_data_home   : (string -> unit) -> string
val xdg_data_dirs   : (string -> unit) -> string list
val xdg_dirs : warn : (string -> unit) -> string list

(** {6 Prints the configuration information } *)
val print_config : ?prefix_var_name:string -> out_channel -> string list -> unit
