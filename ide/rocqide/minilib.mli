(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Some excerpts of Util and similar files to avoid depending on them
    and hence on Compat and Camlp5 *)

val print_list : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a list -> unit

type level = [
  | `DEBUG
  | `INFO
  | `NOTICE
  | `WARNING
  | `ERROR
  | `FATAL ]

(** debug printing *)
val debug : bool ref

val log_pp : ?level:level -> Pp.t -> unit
val log    : ?level:level -> string        -> unit

(* The directory where user config files are conventionally *)
(* installed on the current platform (as given by Glib) *)
val rocqide_config_home : unit -> string

(* The directories where system-wide config files are conventionally *)
(* installed on the current platform (as given by Glib) *)
val rocqide_system_config_dirs : unit -> string list

(* The directory where default config files are installed at installation time *)
val rocqide_default_config_dir : unit -> string

(* The ordered list of directories where a config file is searched by default *)
val rocqide_config_dirs : unit -> string list

(* The ordered list of directories where a data file is searched by default *)
val rocqide_data_dirs : unit -> string list
