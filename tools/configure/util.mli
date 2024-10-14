(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

val os_type_win32 : bool
val os_type_cygwin : bool

val cprintf : ('a, out_channel, unit, unit) format4 -> 'a

val string_split : char -> string -> string list
val starts_with : string -> string -> bool
val generic_version_nums : name:string -> string -> int list

val warn : ('a, out_channel, unit, unit, unit, unit) format6 -> 'a
val die : string -> 'a

val is_executable : string -> bool
val dir_exists : string -> bool

val which : string -> string
val program_in_path : string -> bool

val exe : string ref
type err = StdErr | StdOut | DevNull

val run
  : ?fatal:bool
  -> ?verbose:bool
  -> ?err:err
  -> string -> string list -> string * string list

val tryrun : string -> string list -> string * string list
val read_lines_and_close : in_channel -> string * string list

val arch : string option -> string

(* bin is used to avoid adding \r on Cygwin/Windows *)
val write_config_file : file:string -> ?bin:bool -> (out_channel -> unit) -> unit

(* enable debug mode *)
val debug : bool ref
