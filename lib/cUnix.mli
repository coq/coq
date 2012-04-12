(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** {5 System utilities} *)

type physical_path = string
type load_path = physical_path list

val canonical_path_name : string -> string

val physical_path_of_string : string -> physical_path
val string_of_physical_path : physical_path -> string

val path_to_list : string -> string list

val make_suffix : string -> string -> string
val file_readable_p : string -> bool

(** {6 Executing commands } *)
(** [run_command converter f com] launches command [com], and returns
    the contents of stdout and stderr that have been processed with
    [converter]; the processed contents of stdout and stderr is also
    passed to [f] *)

val run_command : (string -> string) -> (string -> unit) -> string ->
  Unix.process_status * string

