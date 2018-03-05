(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
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

val coqide_config_home : unit -> string
val coqide_config_dirs : unit -> string list
val coqide_data_dirs : unit -> string list
val is_prefix_of : string -> string -> bool
