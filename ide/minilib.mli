(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(** Some excerpts of Util and similar files to avoid depending on them
    and hence on Compat and Camlp4 *)

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

val log : ?level:level -> string -> unit

val coqide_config_home : unit -> string
val coqide_config_dirs : unit -> string list
val coqide_data_dirs : unit -> string list
val is_prefix_of : string -> string -> bool
