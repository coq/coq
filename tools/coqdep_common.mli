(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

module StrSet : Set.S with type elt = string

val option_c : bool ref
val option_noglob : bool ref
val option_boot : bool ref
val option_natdynlk : bool ref
val option_mldep : string option ref
val norec_dirs : StrSet.t ref
val suffixe : string ref
type dir = string option
val get_extension : string -> string list -> string * string
val basename_noext : string -> string
val mlAccu : (string * string * dir) list ref
val mliAccu : (string * dir) list ref
val mllibAccu : (string * dir) list ref
val vAccu : (string * string) list ref
val addQueue : 'a list ref -> 'a -> unit
val add_ml_known : string -> dir -> string -> unit
val iter_ml_known : (string -> dir -> unit) -> unit
val search_ml_known : string -> dir option
val add_mli_known : string -> dir -> string -> unit
val iter_mli_known : (string -> dir -> unit) -> unit
val search_mli_known : string -> dir option
val add_mllib_known : string -> dir -> string -> unit
val search_mllib_known : string -> dir option
val search_v_known : ?from:string list -> string list -> string option
val file_name : string -> string option -> string
val escape : string -> string
val canonize : string -> string
val mL_dependencies : unit -> unit
val coq_dependencies : unit -> unit
val suffixes : 'a list -> 'a list list
val add_known : bool -> string -> string list -> string -> unit
val add_coqlib_known : bool -> string -> string list -> string -> unit
val add_caml_known : string -> string list -> string -> unit
val add_caml_dir : string -> unit
val add_dir :
  (bool -> string -> string list -> string -> unit) -> string -> string list -> unit
val add_rec_dir :
  (bool -> string -> string list -> string -> unit) -> string -> string list -> unit
val add_rec_uppercase_subdirs :
  (bool -> string -> string list -> string -> unit) -> string -> string list -> unit
val treat_file : dir -> string -> unit
val error_cannot_parse : string -> int * int -> 'a
